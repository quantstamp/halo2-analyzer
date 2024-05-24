use criterion::{criterion_group, criterion_main, Criterion};
use halo2_proofs::halo2curves::bn256::Fr;
use std::marker::PhantomData;

use korrekt_V2;

use korrekt_V2::circuit_analyzer::analyzer;
use korrekt_V2::io::analyzer_io_type::{
    self, AnalyzerType, LookupMethod, VerificationMethod,
};
use korrekt_V2::sample_circuits;

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
    ($c:expr, $($size:expr),*) => {
        {
            let mut group = $c.benchmark_group("underconstrained_fibo_v2_uninterpreted");
            group.sample_size(20);
            $(
                group.bench_function(format!("size_{}", $size), |b| {
                    b.iter(|| run_underconstrained_benchmark_for_specified_size::<$size>())
                });
            )*
            group.finish();
        }
    };
}

/// Runs benchmark tests for various specified sizes.
///
/// This function executes a series of benchmark tests using the `run_underconstrained_benchmark_for_specified_size` function.
/// It runs the benchmark for different specified sizes: 5, 8, 13, 21, and 34. The `run_underconstrained_benchmark_for_specified_size`
/// function is called for each specified size.
pub fn run_benchmark(c: &mut Criterion) {
    run_underconstrained_benchmarks!(c, 5, 8, 13, 21, 34);
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
pub fn run_underconstrained_benchmark_for_specified_size<const ROWS: usize>() {
    let circuit = sample_circuits::pse_v1::copy_constraint::fibonacci_for_bench::FibonacciCircuit::<
        Fr,
        ROWS,
    >(PhantomData);
    let k: u32 = 11;
    

    let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
        verification_method: VerificationMethod::Random,
        iterations: 5,
        lookup_method: LookupMethod::Uninterpreted,
    };
    let mut analyzer = analyzer::Analyzer::new(&circuit, k,AnalyzerType::UnderconstrainedCircuit,Some(&analyzer_input)).unwrap();


    let _output_status = analyzer
        .analyze_underconstrained(&analyzer_input)
        .unwrap()
        .output_status;
}

criterion_group!(name = benches;
                config = Criterion::default().measurement_time(std::time::Duration::from_secs(20));
                targets = run_benchmark);
criterion_main!(benches);
