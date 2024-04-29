// ------------- gate stuff, application-specific -------------------

/// Recursive gate enum, application-specific
enum Op {
    Input(int),
    Xor(Op, Op),
    And(Op, Op),
    Rotl(Op, Op), // Rotate left by one bit, the second argument is ignored.
    /// Reference to the output of another (already flattened) gate.
    Gate(int),
}

let decompose_routine: Op -> Gate<Op> = |op| match op {
    Op::Input(n) => Gate::Reference(n), // TODO this assumes that we started appending all the inputs
    Op::Gate(n) => Gate::Reference(n),
    Op::Xor(a, b) => Gate::Op(1, a, b),
    Op::And(a, b) => Gate::Op(2, a, b),
    Op::Rotl(a, b) => Gate::Op(3, a, b),
};

/// Encapsulate a gate ID inside an Op structure.
let id_to_gate: int -> Op = |id| Op::Gate(id);

// ---------------- circuit flattening operations -----------------------------------

enum Gate<Op> {
    Reference(int),
    Op(int, Op, Op),
}

let new_circuit = || {
    ([], std::btree::new())
};

/// Flattens an Op-structure into an array of (gate_type, input_id1, input_id2).
/// Takes a state object (created using new_circuit) and a routine that
/// can be decomposed by decompose_routine and returns an updated state and the output gate ID.
/// TODO once we have traits, the functions should be replaced by trait functions.
/// This function can be called multiple times on different sub-routines.
let flatten_circuit = |state, routine, decompose_routine, id_to_gate| {
        let (flattened, output_id) = internal::flatten_circuit(state, routine, decompose_routine);
        (flattened, id_to_gate(output_id))
    };

mod internal {
    use std::utils::max;
    use super::Op;
    use super::Gate;
    use std::btree::CmpResult;
    use std::utils::Option;

    let flatten_circuit = |state, routine, decompose_routine|
        match decompose_routine(routine) {
            Gate::Reference(n) => (state, n),
            Gate::Op(op, a, b) => {
                let (s2, a_out) = flatten_circuit(state, a, decompose_routine);
                let (s3, b_out) = flatten_circuit(s2, b, decompose_routine);
                append_gate(s3, (op, a_out, b_out))
            },
        };
    
    let gate_ids_cmp: (int, int, int) -> CmpResult = |(a1, a2, a3), (b1, b2, b3)|
        match cmp_int(a1, b1) {
            CmpResult::Equal => cmp_two_tuple((a2, a3), (b2, b3)),
            x => x,
        };
    let cmp_two_tuple: (int, int) -> CmpResult = |(a1, a2), (b1, b2)|
        match cmp_int(a1, b1) {
            CmpResult::Equal => cmp_int(a2, b2),
            x => x,
        };

    let cmp_int: int, int -> CmpResult = |a, b|
        if a < b {
            CmpResult::Less
        } else {
            if a == b { CmpResult::Equal } else { CmpResult::Greater }
        };

    /// Appends a gate to the state and returns the gate ID.
    /// If the gate already exists, the existing ID is returned.
    let append_gate = |(gates, gate_ids), gate|
        match std::btree::get(gate_ids, gate, gate_ids_cmp) {
            Option::Some(id) => ((gates, gate_ids), id),
            Option::None => {
                let id = std::array::len(gates);
                let new_gate_ids = std::btree::insert(gate_ids, (gate, id));
                ((gates + [gate], new_gate_ids), id)
            }
        };

}

enum Vertex {
    Input1,
    Input2,
    Output
}

let vertex_to_str = |v| match v {
    Vertex::Input1 => "i1",
    Vertex::Input2 => "i2",
    Vertex::Output => "o",
};

let vertex_id = |row, vertex| match vertex {
    Vertex::Input1 => 3 * row + 0,
    Vertex::Input2 => 3 * row + 1,
    Vertex::Output => 3 * row + 2,
};

let vertex_id_to_row = |vertex_id| {
    let kind = match vertex_id % 3 {
        0 => Vertex::Input1,
        1 => Vertex::Input2,
        2 => Vertex::Output,
    };
    (vertex_id / 3, kind)
};

// ------------------------------- permutation routines for the copy constraints ---------------------------

/// Computes the permutation from a flattened circuit.
let ops_to_permutation: (int, int, int)[] -> (int -> int) = |ops| {
    // First create an edge list and sort it.
    // The first component of the edge list is the gate index.
    // The second component is the vertex index:

    let edges_unsorted = std::array::flatten(std::array::map_enumerated(
        ops,
        |i, (gate, l, r)| [(l, vertex_id(i, Vertex::Input1)), (r, vertex_id(i, Vertex::Input2))]
    ));
    let edges = std::array::sort(edges_unsorted, |(i, _), (j, _)| i < j);

    // Now we compute an array such that its `i`th element contains all the
    // vertices connected to the output vertex of gate `i`.
    // The values of this array is a partition of all the vertices.
    let partition = {
        // Helper: Take the current list and current tentative vertex list
        // and add it to the final list. Also adds empty lists only containing output
        // vertices until the length is equal to "next".
        let finalize = |list, vertices, next| {
            let row_id = std::array::len(list);
            list
                + [vertices + [vertex_id(row_id, Vertex::Output)]]
                + std::array::new(next - row_id - 1, |i| [vertex_id(row_id + i + 1, Vertex::Output)])
        };
        let (list, vertices) = std::array::fold(edges, ([], []), |(list, vertices), (from, to)|
            if from == std::array::len(list) {
                // we are still operating on the same gate,
                // add "to" as a new vertex to the current list.
                (list, vertices + [to])
            } else {
                // this is a new gate, finalize the old one
                // and then create a new group
                (finalize(list, vertices, from), [to])
            }
        );
        finalize(list, vertices, std::array::len(ops))
    };

    // Now compute a permutation from the partition list.
    // The permutation is in row-first order, although we need column-first order,
    // but it is easy to transpose.
    |i| {
        let vertex = i % (3 * std::array::len(ops));
        let (row, vertex_kind) = vertex_id_to_row(vertex);
        let source = match vertex_kind {
            Vertex::Output => row,
            Vertex::Input1 => { let (_, s, _) = ops[row]; s },
            Vertex::Input2 => { let (_, _, s) = ops[row]; s },
        };
        let vertices = partition[source];
        let self_index = std::array::index_of(vertices, vertex);
        let _ = std::check::assert(self_index >= 0, || "");
        (i - vertex) + vertices[(self_index + 1) % std::array::len(vertices)]
    }
};

// --------------------------- circuit description ---------------------------------

let routine_part = |a, b| rotl(and(xor(a, b), and(a, xor(b, a))), a);

let routine_2 = |circuit_descr, a, b| {
    let (circuit_descr, out1) = flatten(circuit_descr, routine_part(a, b));
    flatten(circuit_description, xor(out1, out1))
};


// This is the main input, the description of the circuit:
let<T1, T2> routine: (T1, T1, (T1, T1 -> T1), (T1, T1 -> T1), (T1, T1 -> T2)) -> T2 =
    |(a, b, xor, and, rotl)| rotl(and(xor(a, b), and(a, xor(b, a))), a);


// symbolic representation of each primitive, we could even implement them in more complex expressions
// (like rot via two shifts and an or)
let symbolic = || (
    Op::Input(0),
    Op::Input(1),
    |x, y| Op::Xor(x, y),
    |x, y| Op::And(x, y),
    |x, y| Op::Rotl(x, y)
);

// concrete representation of each primivite.
let concrete: int, int -> (int, int, (int, int -> int), (int, int -> int), (int, int -> int)) = |a, b| (
    a,
    b,
    |x, y| x ^ y,
    |x, y| x & y,
    |x, y| ((x << 1) | (x >> 8)) & 0xff
);

// A symbolic representation of the circuit
let symbolic_routine = routine(symbolic());
// A concreet representation of the circuit
let concrete_routine = |a, b| routine(concrete(a, b));

let flattened = flatten_circuit(symbolic_routine);
let circuit_len = std::array::len(flattened);

// TODO would be nice to allow certain user-defined types as values
// for fixed columns - maybe via a trait?
// And then we would allow lookups only between columns of the same user-defined type?
// Maybe have `col<Type>`, where Type could be omitted if it can be inferred?
let gate_to_int = |g| match g {
    Gate::Input => 0,
    Gate::Xor => 1,
    Gate::And => 2,
    Gate::Rotl => 3,
};
let int_to_gate = |i| match i {
    0 => Gate::Input,
    1 => Gate::Xor,
    2 => Gate::And,
    3 => Gate::Rotl,
};

let permutation = ops_to_permutation(flattened);
// TODO I don't think this is correct, it shuold add namespace len.
// TODO Are they really stacked on top of each other?
// TODO OK it turns out that row i in the first column is identified via `w^i`,
// and in the second colum via `k1 * w^i` and in the third row via `k2 * w^i`,
// where k1 and k2 are quadratic non-residues.
// So I wonder where it might be better to just use `(int, fe)` or even `(int, int)`
// as the type of the value of a RHS in a connect constraint.
let transposed = |i| i / 3 + (i % 3) * circuit_len;

/*
trat ToString<T> {
    to_string: |T| -> String,
}
impl<T: ToString> ToString<T[]> {
    let to_string = |a| "[" + std::array::fold("", std::array::map(a, ToString::to_string), |acc, x| acc + ", " + x) + "]";
}
*/

machine Main {
    // A, B are gate inputs, C is the gate output
    col witness A, B, C;
    // C(0) and C(1) are the public inputs
    let GATE: col = |i| { let (gate, _, _) = flattened[i % circuit_len]; gate_to_int(gate) };

    let Conn_A: col = |i| transposed(permutation(3 * (i % circuit_len))) + (i / circuit_len) * circuit_len;
    let Conn_B: col = |i| transposed(permutation(3 * (i % circuit_len) + 1)) + (i / circuit_len) * circuit_len;
    let Conn_C: col = |i| transposed(permutation(3 * (i % circuit_len) + 2)) + (i / circuit_len) * circuit_len;

    let inputs: (int -> int)[] = std::utils::cross_product([256, 256, 4]);
    let a = inputs[0];
    let b = inputs[1];
    let op = inputs[2];
    let P_A: col = |i| a(i);
    let P_B: col = |i| b(i);
    let P_GATE: col = |i| op(i);
    let P_C: col = |i| match int_to_gate(op(i)) {
        Gate::Input => a(i),
        Gate::Xor => a(i) ^ b(i),
        Gate::And => a(i) & b(i),
        Gate::Rotl => ((a(i) << 1) | (a(i) >> 8)) & 0xff
    };

    { GATE, A, B, C } in { P_GATE, P_A, P_B, P_C };
    //{ A, B, C } connect { Conn_A, Conn_B, Conn_C };

    // TODO What is the purpose of these constrainst in the polygon file?
    // Global.L1 * a44 = 0;
    // Global.L1 * (2**44-1-b44) = 0;
}
