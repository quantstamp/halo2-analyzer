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

fn main() {
    // println!("----------------------Analyzing Circuit----------------------");
    // let circuit = sample_circuits::general_bit_decomp::BitDecompositon::<Fr, 3>::new([Fr::from(1); 3]);
    // let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    // let analyzer_type = analyzer_io::retrieve_user_input_for_analyzer_type();
    // analyzer.dispatch_analysis(analyzer_type);

    // Uncomment the following to run the benchmark
    // benchmark::run_benchmark();
}

#[cfg(test)]
mod integration_tests;
