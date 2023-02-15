use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use lalrpop_util::*;

pub mod ast;

lalrpop_mod!(
    #[allow(clippy::all)]
    pil,
    "/parser/pil.rs"
);

#[derive(Debug)]
pub struct ParseError<'a> {
    start: usize,
    end: usize,
    file_name: String,
    contents: &'a str,
    message: String,
}

impl<'a> ParseError<'a> {
    pub fn output_to_stderr(&self) {
        let config = term::Config::default();
        let mut files = SimpleFiles::new();
        let file_id = files.add(&self.file_name, self.contents);
        let diagnostic = Diagnostic::error()
            .with_message(&self.message)
            .with_labels(vec![Label::primary(file_id, self.start..self.end)]);
        let mut writer = StandardStream::stderr(ColorChoice::Always);
        term::emit(&mut writer, &config, &files, &diagnostic).unwrap()
    }
}

pub fn parse<'a>(file_name: Option<&str>, input: &'a str) -> Result<ast::PILFile, ParseError<'a>> {
    pil::PILFileParser::new().parse(input).map_err(|err| {
        let (&start, &end) = match &err {
            lalrpop_util::ParseError::InvalidToken { location } => (location, location),
            lalrpop_util::ParseError::UnrecognizedEOF {
                location,
                expected: _,
            } => (location, location),
            lalrpop_util::ParseError::UnrecognizedToken {
                token: (start, _, end),
                expected: _,
            } => (start, end),
            lalrpop_util::ParseError::ExtraToken {
                token: (start, _, end),
            } => (start, end),
            lalrpop_util::ParseError::User { error: _ } => (&0, &0),
        };
        ParseError {
            start,
            end,
            file_name: file_name.unwrap_or("input").to_string(),
            contents: input,
            message: format!("{err}"),
        }
    })
}

#[cfg(test)]
mod test {
    use std::fs;

    use super::*;
    use ast::*;

    #[test]
    fn empty() {
        assert!(pil::PILFileParser::new().parse("").is_ok());
    }

    #[test]
    fn simple_include() {
        let parsed = pil::PILFileParser::new().parse("include \"x\";").unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![Statement::Include(0, "x".to_string())])
        );
    }

    #[test]
    fn start_offsets() {
        let parsed = pil::PILFileParser::new()
            .parse("include \"x\"; pol commit t;")
            .unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![
                Statement::Include(0, "x".to_string()),
                Statement::PolynomialCommitDeclaration(
                    13,
                    vec![PolynomialName {
                        name: "t".to_string(),
                        array_size: None
                    }]
                )
            ])
        );
    }

    #[test]
    fn simple_plookup() {
        let parsed = pil::PILFileParser::new().parse("f in g;").unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![Statement::PlookupIdentity(
                0,
                SelectedExpressions {
                    selector: None,
                    expressions: vec![Expression::PolynomialReference(PolynomialReference {
                        name: "f".to_string(),
                        ..Default::default()
                    })]
                },
                SelectedExpressions {
                    selector: None,
                    expressions: vec![Expression::PolynomialReference(PolynomialReference {
                        name: "g".to_string(),
                        ..Default::default()
                    })]
                }
            )])
        );
    }

    fn parse_file(name: &str) -> PILFile {
        let input = fs::read_to_string(name).unwrap();
        parse(Some(name), &input).unwrap_or_else(|err| {
            eprintln!("Parse error during test:");
            err.output_to_stderr();
            panic!();
        })
    }

    #[test]
    fn parse_example_files() {
        parse_file("tests/polygon-hermez/arith.pil");
        parse_file("tests/polygon-hermez/binary.pil");
        parse_file("tests/polygon-hermez/byte4.pil");
        parse_file("tests/polygon-hermez/config.pil");
        parse_file("tests/polygon-hermez/global.pil");
        parse_file("tests/polygon-hermez/keccakf.pil");
        parse_file("tests/polygon-hermez/main.pil");
        parse_file("tests/polygon-hermez/mem_align.pil");
        parse_file("tests/polygon-hermez/mem.pil");
        parse_file("tests/polygon-hermez/nine2one.pil");
        parse_file("tests/polygon-hermez/padding_kk.pil");
        parse_file("tests/polygon-hermez/padding_kkbit.pil");
        parse_file("tests/polygon-hermez/padding_pg.pil");
        parse_file("tests/polygon-hermez/poseidong.pil");
        parse_file("tests/polygon-hermez/rom.pil");
        parse_file("tests/polygon-hermez/storage.pil");
    }

    #[test]
    fn simple_macro() {
        let parsed = pil::PILFileParser::new()
            .parse("macro f(x) { x in g; x + 1 };")
            .unwrap();
        assert_eq!(
            parsed,
            PILFile(vec![Statement::MacroDefinition(
                0,
                "f".to_string(),
                vec!["x".to_string()],
                vec![Statement::PlookupIdentity(
                    13,
                    SelectedExpressions {
                        selector: None,
                        expressions: vec![Expression::PolynomialReference(PolynomialReference {
                            name: "x".to_string(),
                            ..Default::default()
                        })]
                    },
                    SelectedExpressions {
                        selector: None,
                        expressions: vec![Expression::PolynomialReference(PolynomialReference {
                            name: "g".to_string(),
                            ..Default::default()
                        })]
                    }
                )],
                Some(Expression::BinaryOperation(
                    Box::new(Expression::PolynomialReference(PolynomialReference {
                        namespace: None,
                        name: "x".to_string(),
                        index: None,
                        next: false
                    })),
                    BinaryOperator::Add,
                    Box::new(Expression::Number(1))
                ))
            )])
        );
    }
}
