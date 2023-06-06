use std::{
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
};

use itertools::Itertools;
use number::FieldElement;
use parser::{
    asm_ast::{
        batched::{ASMStatementBatch, BatchedASMFile, Incompatible, IncompatibleSet},
        ASMFile, ASMStatement, InstructionBodyElement, InstructionParams, RegisterFlag,
    },
    ast::{Expression, Statement},
    expr_any,
};

/// A map of which cells are accessed by a given construct
#[derive(Default, Clone, Debug)]
struct Footprint {
    /// the polynomials accessed on the current row
    cur: BTreeSet<String>,
    /// the polynomials accessed on the next row
    next: BTreeSet<String>,
    /// the assignment registers used
    assignment: BTreeSet<String>,
    /// whether we write the pc
    pc_next: bool,
}

impl Footprint {
    fn process<T: FieldElement>(
        &mut self,
        e: &Expression<T>,
        batcher: &ASMBatcher<T>,
        ignore: &BTreeSet<String>,
    ) {
        expr_any(e, |e| match e {
            Expression::PolynomialReference(r) => {
                if !ignore.contains(&r.name) {
                    if r.next {
                        self.next.insert(r.name.clone());
                    } else {
                        self.cur.insert(r.name.clone());
                    };

                    if r.next && r.name == *batcher.pc_name.as_ref().unwrap() {
                        self.pc_next = true;
                    }
                }

                false
            }
            Expression::FunctionCall(instr, _) => {
                let footprint = batcher.instructions.get(instr).unwrap().footprint.clone();
                self.join(footprint);
                false
            }
            _ => false,
        });
    }

    // expand a footprint based on connected components in the column graph
    fn expand(&mut self, columns: &Columns) {
        let cur: Vec<_> = self.cur.iter().cloned().collect();
        for c in cur {
            self.cur.extend(dbg!(columns.get_connected(&c)));
        }
        let next: Vec<_> = self.next.iter().cloned().collect();
        for c in next {
            self.next.extend(dbg!(columns.get_connected(&c)));
        }
    }

    fn join(&mut self, other: Self) {
        self.cur.extend(other.cur);
        self.next.extend(other.next);
        self.assignment.extend(other.assignment);
        assert!(!self.pc_next);
        self.pc_next = other.pc_next;
    }

    fn try_join(&mut self, other: Self) -> Result<(), (Self, IncompatibleSet)> {
        let mut incompatible_set = BTreeSet::default();
        if self.pc_next {
            incompatible_set.insert(Incompatible::Jump);
        }
        if !self.next.is_disjoint(&other.cur) {
            incompatible_set.insert(Incompatible::ReadAfterWrite);
        }
        if !self.next.is_disjoint(&other.next) {
            incompatible_set.insert(Incompatible::BusyWriteRegister);
        }
        if !self.assignment.is_disjoint(&other.assignment) {
            incompatible_set.insert(Incompatible::BusyAssignmentRegister);
        }

        if incompatible_set.is_empty() {
            self.join(other);
            Ok(())
        } else {
            Err((other, IncompatibleSet(incompatible_set)))
        }
    }
}

#[derive(Default)]
struct Batch<T> {
    statements: Vec<ASMStatement<T>>,
    footprint: Footprint,
}

impl<T: FieldElement> Batch<T> {
    fn from_statement(s: ASMStatement<T>, batcher: &ASMBatcher<T>) -> Batch<T> {
        let mut footprint = Footprint::default();

        match &s {
            ASMStatement::Assignment(_, write_to, ass_reg, value) => {
                // register the assignment registers
                footprint.assignment.extend(ass_reg.clone());
                // register the registers written to as accessed on the next row
                footprint.next.extend(write_to.clone());
                // if the pc is written to, register it
                footprint.pc_next |= write_to.iter().any(|r| Some(r) == batcher.pc_name.as_ref());
                // process the value being written
                footprint.process(value, batcher, &Default::default());
            }
            ASMStatement::Instruction(_, instr, args) => {
                let mut ignore = BTreeSet::new();
                let instruction = &batcher.instructions.get(instr).unwrap();

                // ignore the label inputs
                ignore.extend(
                    args.iter()
                        .zip(&instruction.is_label)
                        .filter(|(_, is_label)| **is_label)
                        .map(|(arg, _)| match arg {
                            Expression::PolynomialReference(r) => r.name.clone(),
                            _ => unreachable!(),
                        }),
                );

                // ignore the label names inside the instruction body?
                ignore.extend(instruction.labels.clone());

                // process the instruction call
                footprint.process(
                    &Expression::FunctionCall(instr.clone(), args.clone()),
                    batcher,
                    &ignore,
                );
            }
            ASMStatement::Label(..) => {
                // a label does not access anything, do nothing
            }
            _ => unreachable!(),
        };

        footprint.expand(&batcher.columns);

        Batch {
            statements: vec![s],
            footprint,
        }
    }

    fn try_absorb(
        &mut self,
        s: ASMStatement<T>,
        batcher: &ASMBatcher<T>,
    ) -> Result<(), (ASMStatement<T>, IncompatibleSet)> {
        let batch = Self::from_statement(s, batcher);
        self.try_join(batch)
            .map_err(|(b, incompatible)| (b.statements.into_iter().next().unwrap(), incompatible))
    }

    fn try_join(&mut self, other: Self) -> Result<(), (Self, IncompatibleSet)> {
        let mut incompatible_set = BTreeSet::default();
        if !self.statements.is_empty()
            && other
                .statements
                .iter()
                .any(|s| matches!(s, ASMStatement::Label(..)))
        {
            incompatible_set.insert(Incompatible::Label);
            return Err((other, IncompatibleSet(incompatible_set)));
        }

        match self.footprint.try_join(other.footprint) {
            Ok(()) => {
                self.statements.extend(other.statements);
                Ok(())
            }
            Err((footprint, incompatible)) => Err((Batch { footprint, ..other }, incompatible)),
        }
    }
}

type Components = BTreeMap<String, usize>;

// the columns of the program
#[derive(Default)]
struct Columns {
    edges: BTreeMap<String, BTreeSet<String>>,
    components: Option<Components>,
}

impl Columns {
    fn add_column(&mut self, c: String) {
        assert!(self.edges.insert(c, Default::default()).is_none());
    }

    fn set_connected(&mut self, left: String, right: String) {
        self.edges
            .entry(left.clone())
            .or_default()
            .insert(right.clone());
        self.edges.entry(right).or_default().insert(left);
    }

    fn build_components(&mut self) {
        let mut id = 0;
        let mut components = BTreeMap::default();

        for node in self.edges.keys() {
            if !components.contains_key(node) {
                // we start a new component
                id += 1;

                let mut to_treat = vec![node.clone()];

                let mut treat_node = |node: &String, to_treat: &mut Vec<String>| {
                    if !components.contains_key(node) {
                        components.insert(node.clone(), id);
                        to_treat.extend(self.edges.get(node).cloned().unwrap());
                    }
                };

                while let Some(node) = to_treat.pop() {
                    treat_node(&node, &mut to_treat);
                }
            }
        }

        self.components = Some(components);
    }

    fn get_connected(&self, e: &String) -> BTreeSet<String> {
        let components: &BTreeMap<String, usize> = self.components.as_ref().unwrap();

        let id = components.get(e).expect(e);

        components
            .iter()
            .filter(|(_, i)| *i == id)
            .map(|(c, _)| c.clone())
            .collect()
    }
}

#[derive(Default)]
pub struct ASMBatcher<T> {
    /// the name of the pc for this program
    pc_name: Option<String>,
    /// the footprint of each column, built recursively
    columns: Columns,
    /// the footprint of each instruction
    instructions: BTreeMap<String, Instruction>,
    marker: PhantomData<T>,
}

#[derive(Default, Debug)]

struct Instruction {
    footprint: Footprint,
    labels: BTreeSet<String>,
    is_label: Vec<bool>,
}

impl<T: FieldElement> ASMBatcher<T> {
    /// split a list of statements into compatible batches
    fn to_compatible_batches(
        &self,
        statements: impl IntoIterator<Item = ASMStatement<T>>,
    ) -> Vec<ASMStatementBatch<T>> {
        statements
            .into_iter()
            .peekable()
            .batching(|it| {
                let mut batch = Batch::default();
                loop {
                    match it.peek() {
                        Some(new_s) => match batch.try_absorb(new_s.clone(), self) {
                            Ok(()) => {
                                it.next().unwrap();
                            }
                            Err((_, reason)) => {
                                let res = ASMStatementBatch {
                                    statements: batch.statements,
                                    reason: Some(reason),
                                };
                                break Some(res);
                            }
                        },
                        None => {
                            break match batch.statements.len() {
                                0 => None,
                                _ => Some(ASMStatementBatch {
                                    statements: batch.statements,
                                    reason: None,
                                }),
                            }
                        }
                    }
                }
            })
            .collect()
    }

    pub fn convert(&mut self, asm_file: ASMFile<T>) -> BatchedASMFile<T> {
        let statements = asm_file.0.into_iter().peekable();

        let (declarations, statements) = statements.into_iter().partition(|s| match s {
            ASMStatement::Degree(..) => true,
            ASMStatement::RegisterDeclaration(_, name, flags) => {
                self.handle_register_declaration(flags, name);
                true
            }
            ASMStatement::InstructionDeclaration(_, name, params, body) => {
                self.handle_instruction_def(body, name, params);
                true
            }
            ASMStatement::InlinePil(_, block) => {
                self.handle_inline_pil(block);
                true
            }
            _ => false,
        });

        self.expand();

        let batches = self.to_compatible_batches(statements);

        let lines_before = batches.iter().map(ASMStatementBatch::size).sum::<usize>() as f32;
        let lines_after = batches.len() as f32;

        log::debug!(
            "Batching complete with savings of {}% in execution trace lines",
            (1. - lines_after / lines_before) * 100.
        );

        BatchedASMFile {
            declarations,
            batches,
        }
    }

    fn expand(&mut self) {
        // build connected components
        self.columns.build_components();
        // extend the instruction footprints using the connected components
        for instruction in self.instructions.values_mut() {
            instruction.footprint.expand(&self.columns);
        }
    }

    fn handle_inline_pil(&mut self, statements: &[Statement<T>]) {
        for s in statements {
            let mut pool = BTreeSet::default();
            match s {
                Statement::PolynomialConstantDefinition(..) => {}
                Statement::PolynomialIdentity(_, e) => {
                    expr_any(e, |e| match e {
                        Expression::PolynomialReference(r) => {
                            pool.insert(r.name.clone());
                            false
                        }
                        _ => false,
                    });
                }
                _ => {
                    unimplemented!("batching not supported for statement {s}")
                }
            }
            for (i, j) in pool
                .iter()
                .flat_map(|r| pool.iter().map(|s| (r.clone(), s.clone())))
            {
                self.columns.set_connected(i.clone(), j.clone())
            }
        }
    }

    fn handle_register_declaration(&mut self, flags: &Option<RegisterFlag>, name: &str) {
        if let Some(RegisterFlag::IsPC) = flags {
            assert_eq!(self.pc_name, None);
            self.pc_name = Some(name.to_string());
        }

        self.columns.add_column(name.into());
    }

    fn handle_instruction_def(
        &mut self,
        body: &[InstructionBodyElement<T>],
        name: &str,
        params: &InstructionParams,
    ) {
        let mut footprint = Footprint::default();
        let mut labels = BTreeSet::default();
        let mut is_label = vec![];

        // get assignment registers
        for param in params
            .inputs
            .params
            .iter()
            .chain(params.outputs.iter().flat_map(|o| o.params.iter()))
        {
            match &param.ty {
                Some(ty) if ty == "label" => {
                    is_label.push(true);
                    labels.insert(param.name.clone());
                }
                None => {
                    is_label.push(false);
                    footprint.assignment.insert(param.name.clone());
                }
                _ => unreachable!(),
            }
        }

        // get accessed registers
        for expr in body {
            match expr {
                InstructionBodyElement::Expression(expr) => {
                    footprint.process(expr, self, &labels);
                }
                InstructionBodyElement::PlookupIdentity(left, _op, right) => {
                    for e in left
                        .expressions
                        .iter()
                        .chain(left.selector.iter())
                        .chain(right.expressions.iter())
                        .chain(right.selector.iter())
                    {
                        footprint.process(e, self, &labels);
                    }
                }
            }
        }

        log::debug!("Instruction footprint: {name} {:#?}", footprint);

        self.instructions.insert(
            name.into(),
            Instruction {
                footprint,
                labels,
                is_label,
            },
        );
    }
}

#[cfg(test)]
mod tests {

    use std::{fs, path::PathBuf};

    use number::GoldilocksField;
    use pretty_assertions::assert_eq;

    use super::*;

    fn test_batching(path: &str) {
        let base_path = PathBuf::from("../test_data/asm/batching");
        let file_name = base_path.join(path);
        let contents = fs::read_to_string(&file_name).unwrap();
        let batched_asm = parser::parse_asm::<GoldilocksField>(
            Some(file_name.as_os_str().to_str().unwrap()),
            &contents,
        )
        .map(|ast| ASMBatcher::default().convert(ast))
        .unwrap();
        let mut expected_file_name = file_name;
        expected_file_name.set_file_name(format!(
            "{}_batched.asm",
            expected_file_name.file_stem().unwrap().to_str().unwrap()
        ));
        let expected = fs::read_to_string(expected_file_name).unwrap();

        assert_eq!(
            format!("{batched_asm}").replace("\n\n", "\n"),
            expected.replace("\n\n", "\n")
        );
    }

    #[test]
    fn disjoint_assignments() {
        test_batching("disjoint_assignment_reg.asm")
    }
}
