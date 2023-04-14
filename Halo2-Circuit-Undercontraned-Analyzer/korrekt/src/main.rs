use halo2_proofs::pasta::Fp as Fr;
use std::time::{Duration, Instant};

mod abstract_expr;
mod layouter;
mod shape;
mod analyzer_io_type;
mod analyzer_io;
mod analyzer;
mod sample_circuits;
mod smt;
mod smt_parser;

fn main() {
    println!("----------------------Analyzing Circuit----------------------");
    // let circuit = sample_circuits::BitDecompositon::<Fr, 3>::new([Fr::from(1); 3]);
    // let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    // let analyzer_type = analyzer_io::retrieve_user_input_for_analyzer_type();
    // analyzer.dispatch_analysis(analyzer_type);


    // How to run the benchmark for a particular size.
    run_underconstrained_benchmark::<2>();
    run_underconstrained_benchmark::<4>();
    run_underconstrained_benchmark::<8>();
    run_underconstrained_benchmark::<16>();
    run_underconstrained_benchmark::<32>();
    run_underconstrained_benchmark::<64>();
    run_underconstrained_benchmark::<128>();
}

pub fn run_underconstrained_benchmark<const bits: usize>() {
    let circuit = sample_circuits::BitDecompositonUnderConstrained::<Fr, bits>::new([Fr::from(1); bits]);
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

#[cfg(test)]
mod integration_tests;
