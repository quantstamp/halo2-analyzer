use halo2_proofs::pasta::Fp as Fr;
use std::time::Instant;

use crate::{
    analyzer,
    analyzer_io_type,
    sample_circuits,
};

pub fn run_benchmark() {
    run_underconstrained_benchmark_for_specified_size::<2>();
    run_underconstrained_benchmark_for_specified_size::<4>();
    run_underconstrained_benchmark_for_specified_size::<8>();
    run_underconstrained_benchmark_for_specified_size::<16>();
    run_underconstrained_benchmark_for_specified_size::<32>();
    run_underconstrained_benchmark_for_specified_size::<64>();
    run_underconstrained_benchmark_for_specified_size::<128>();
}

pub fn run_underconstrained_benchmark_for_specified_size<const bits: usize>() {
    let circuit = sample_circuits::general_bit_decomp::BitDecompositonUnderConstrained::<Fr, bits>::new([Fr::from(1); bits]);
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let instance_cols =
        analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
    let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
        verification_method: analyzer_io_type::VerificationMethod::Random,
        verification_input: analyzer_io_type::VerificationInput {
            instances_string: instance_cols,
            iterations: 1,
        },
    };    
    let start = Instant::now();
    analyzer.analyze_underconstrained(analyzer_input);
    let duration = start.elapsed();
    println!("{} bits: Time elapsed for analyze_underconstrained() is: {:?}", bits, duration);
}