use std::time::{Duration, Instant};

use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256;
use halo2_proofs::halo2curves::bn256::Fr;

use anyhow::{Context, Ok, Result};
use korrekt_V1::{
    circuit_analyzer::analyzer::Analyzer,
    io::{
        self,
        analyzer_io_type::{self,AnalyzerInput, VerificationInput, VerificationMethod},
    },
    sample_circuits,
};
use num::{BigInt, Num};

/// `run_underconstrained_benchmarks` macro.
///
/// This macro runs the underconstrained benchmarks for all provided sizes.
///
/// # Examples
///
/// ```
/// // Run underconstrained benchmarks for sizes 10 and 20.
/// run_underconstrained_benchmarks!(10, 20);
/// ```
///
/// # Parameters
///
/// - `$($size:expr),*`: A comma-separated list of sizes to run the underconstrained benchmarks for.
///
macro_rules! run_underconstrained_benchmarks {
        ($($size:expr),*) => {
            $(
                run_underconstrained_benchmark_for_specified_size::<$size>();
            )*
        };
}

/// Runs benchmark tests for various specified sizes.
///
/// This function executes a series of benchmark tests using the `run_underconstrained_benchmark_for_specified_size` function.
/// It runs the benchmark for different specified sizes: 2, 4, 8, 16, 32, 64, and 128. The `run_underconstrained_benchmark_for_specified_size`
/// function is called for each specified size.
pub fn run_benchmark() -> Vec<(usize, std::time::Duration)> {
    let sizes = vec![5,8,13,21,34]; // Define your sizes here
    let mut results = Vec::new();

    for &size in &sizes {
        let duration = match size {
            3 => run_underconstrained_benchmark_for_specified_size::<3>(),
            5 => run_underconstrained_benchmark_for_specified_size::<5>(),
            8 => run_underconstrained_benchmark_for_specified_size::<8>(),
            13 => run_underconstrained_benchmark_for_specified_size::<13>(),
            21 => run_underconstrained_benchmark_for_specified_size::<21>(),
            34 => run_underconstrained_benchmark_for_specified_size::<34>(),
            // Add more cases as needed
            _ => continue, // Skip sizes that aren't explicitly handled
        };
        results.push((size, duration));
    }

    results
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
pub fn run_underconstrained_benchmark_for_specified_size<const ROWS: usize>() -> Duration {
    let circuit =
        sample_circuits::copy_constraint::fibonacci_for_bench::FibonacciCircuit::<Fr,ROWS>::default();
        let start = Instant::now();
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();
    
    let _output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed, &prime)
            .unwrap()
            .output_status;
    let duration = start.elapsed();
    duration
    // println!(
    //     "{} rows: Time elapsed for analyze_underconstrained() is: {:?}",
    //     ROWS, duration
    // );
}
