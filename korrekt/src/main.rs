use std::marker::PhantomData;
use halo2_proofs::pasta::Fp as Fr;

mod abstract_expr;
mod layouter;
mod shape;
mod analyzer_io_type;
mod analyzer_io;
mod analyzer;
mod smt;
mod smt_parser;
mod benchmark;
mod sample_circuits;
mod new_layouters;

fn main() {
    // How to run our analysis on a circuit.
    let circuit:sample_circuits::fibonacci::FibonacciCircuit<_> = sample_circuits::fibonacci::FibonacciCircuit::<Fr>(PhantomData);
    //let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let analyzer_type = analyzer_io::retrieve_user_input_for_analyzer_type();
    analyzer.dispatch_analysis(analyzer_type);

    // The benchmark for underconstrained analysis.
    //benchmark::run_benchmark();
}

#[cfg(test)]
mod integration_tests;
