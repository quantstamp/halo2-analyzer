use std::marker::PhantomData;
use halo2_proofs::{pasta::Fp as Fr, dev::MockProver};

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


fn main() {
    // How to run our analysis on a circuit.
    let circuit = sample_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
    //let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let k = 6;

    let a = Fr::from(1); // F[0]
    let b = Fr::from(1); // F[1]
    let out = Fr::from(6); // F[9]

    let public_input = vec![a, b, out];

    let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    //let _lookups = prover.cs.lookups;

    let analyzer_type = analyzer_io::retrieve_user_input_for_analyzer_type();
    //println!("prover.fixed {:?}",prover.cs.lookups);
    analyzer.dispatch_analysis(analyzer_type,prover.fixed);

    // The benchmark for underconstrained analysis.
    //benchmark::run_benchmark();
}

#[cfg(test)]
mod integration_tests;
