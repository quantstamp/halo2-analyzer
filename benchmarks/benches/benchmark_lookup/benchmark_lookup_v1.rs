use criterion::{criterion_group, criterion_main, Criterion};

use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256;
use halo2_proofs::halo2curves::bn256::Fr;

use korrekt_V1::{
    circuit_analyzer::analyzer::Analyzer,
    io::
        analyzer_io_type::{self, VerificationInput, VerificationMethod},
    
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
    ($c:expr, $($size:expr),*) => {
        {
            let mut group = $c.benchmark_group("underconstrained_lookup_v1");
            group.sample_size(10);
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
    run_underconstrained_benchmarks!(c, 5);//, 8, 13, 21, 34);
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
    let circuit =
        sample_circuits::lookup_circuits::multiple_matched_lookups::MyCircuit::<Fr,ROWS>::default();
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
}

criterion_group!(name = benches;
    config = Criterion::default();
    targets = run_benchmark);
criterion_main!(benches);