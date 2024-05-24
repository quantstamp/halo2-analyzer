use std::collections::HashMap;

use criterion::{criterion_group, criterion_main, Criterion};
use halo2_proofs::halo2curves::bn256::Fr;
use korrekt_V2;

use korrekt_V2::circuit_analyzer::analyzer;
use korrekt_V2::io::analyzer_io_type::{
    self, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
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
            let mut group = $c.benchmark_group("underconstrained_bit_decomp_v2");
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
/// This function executes a series of benchmark tests using the `run_underconstrained_benchmarks` macro.
pub fn run_benchmark(c: &mut Criterion) {
    run_underconstrained_benchmarks!(c, 2, 4, 8, 16, 32, 64, 128);
}

/// Runs an underconstrained benchmark for a specified size.
pub fn run_underconstrained_benchmark_for_specified_size<const BITS: usize>() {
    let k = 11;
    let circuit = sample_circuits::pse_v1::bit_decomposition::general_bit_decomp::BitDecompositonUnderConstrained::<
        Fr,
        BITS,
    >::default();

    let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
        verification_method: VerificationMethod::Random,
        verification_input: VerificationInput {
            instance_cells: HashMap::new(),
            iterations: 5,
        },
        lookup_method: LookupMethod::Interpreted,
    };

    let mut analyzer = analyzer::Analyzer::new(
        &circuit,
        k,
        AnalyzerType::UnderconstrainedCircuit,
        Some(&analyzer_input),
    )
    .unwrap();

    let _result = analyzer.analyze_underconstrained(&analyzer_input);
}

criterion_group!(benches, run_benchmark);
criterion_main!(benches);
