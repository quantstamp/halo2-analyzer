use halo2_proofs::{dev::MockProver, pasta::Fp as Fr};
use std::time::Instant;

use crate::circuit_analyzer::analyzer;
use crate::io::analyzer_io_type;
use crate::sample_circuits;

/// Runs benchmark tests for various specified sizes.
///
/// This function executes a series of benchmark tests using the `run_underconstrained_benchmark_for_specified_size` function.
/// It runs the benchmark for different specified sizes: 2, 4, 8, 16, 32, 64, and 128. The `run_underconstrained_benchmark_for_specified_size`
/// function is called for each specified size.
pub fn run_benchmark() {
    run_underconstrained_benchmark_for_specified_size::<2>();
    run_underconstrained_benchmark_for_specified_size::<2>();
    run_underconstrained_benchmark_for_specified_size::<4>();
    run_underconstrained_benchmark_for_specified_size::<8>();
    run_underconstrained_benchmark_for_specified_size::<16>();
    run_underconstrained_benchmark_for_specified_size::<32>();
    run_underconstrained_benchmark_for_specified_size::<64>();
    run_underconstrained_benchmark_for_specified_size::<128>();
}
/// Runs an underconstrained benchmark for a specified size.
///
/// This function performs an underconstrained benchmark test for a specified size indicated by the `BITS` generic constant.
/// It creates a `BitDecompositonUnderConstrained` circuit using the provided size and runs various operations on it.
/// The benchmark includes creating a mock prover, analyzing the circuit, and measuring the elapsed time.
///
/// # Generic Parameters
///
/// - `BITS`: The size of the circuit in bits.
///
/// # Examples
///
/// ```
/// // Run underconstrained benchmark for size 2
/// run_underconstrained_benchmark_for_specified_size::<2>();
/// ```
pub fn run_underconstrained_benchmark_for_specified_size<const BITS: usize>() {
    let k = 11;
    let circuit =
        sample_circuits::bit_decomposition::general_bit_decomp::BitDecompositonUnderConstrained::<
            Fr,
            BITS,
        >::default();
    let public_input = Fr::from(3);
    let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![vec![public_input]]).unwrap();
    let mut analyzer = analyzer::Analyzer::create_with_circuit(&circuit);
    let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
    let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
        verification_method: analyzer_io_type::VerificationMethod::Random,
        verification_input: analyzer_io_type::VerificationInput {
            instances_string: instance_cols,
            iterations: 1,
        },
    };
    let start = Instant::now();
    let _result = analyzer.analyze_underconstrained(analyzer_input, prover.fixed);
    let duration = start.elapsed();

    println!(
        "{} bits: Time elapsed for analyze_underconstrained() is: {:?}",
        BITS, duration
    );
}
