use criterion::Criterion;
use halo2_proofs::halo2curves::bn256::Fr;
use std::collections::HashMap;
use std::marker::PhantomData;

use korrekt_V2::circuit_analyzer::analyzer::Analyzer;
use korrekt_V2::io::analyzer_io_type::{
    self, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
};
use korrekt_V2::sample_circuits;

macro_rules! benchmark_with_size {
    ($c:expr, $size:expr) => {
        {
            let mut group = $c.benchmark_group(format!("underconstrained_30_matched_lookup_v2_interpreted"));
            group.sample_size(10);

            // Benchmark function
            group.bench_function(format!("size_{}", $size), |b| {
                b.iter_batched(
                    || {
                        let circuit = sample_circuits::pse_v1::lookup_circuits::thirty_matched_lookups::MyCircuit::<
                            Fr,
                            $size,
                        >(PhantomData);
                        let k: u32 = 11;
                        let analyzer_input = analyzer_io_type::AnalyzerInput {
                            verification_method: VerificationMethod::Random,
                            verification_input: VerificationInput {
                                instance_cells: HashMap::new(),
                                iterations: 5,
                            },
                            lookup_method: LookupMethod::Interpreted,
                        };
                        let analyzer = Analyzer::new(
                            &circuit,
                            k,
                            AnalyzerType::UnderconstrainedCircuit,
                            Some(&analyzer_input),
                        )
                        .unwrap();
                        (analyzer, analyzer_input)
                    },
                    |(mut analyzer, mut analyzer_input)| {
                        analyzer
                            .dispatch_analysis(&mut analyzer_input)
                            .unwrap();
                    },
                    criterion::BatchSize::SmallInput,
                );
            });

            group.finish();
        }
    };
}

fn main() {
    let mut criterion = Criterion::default();
    benchmark_with_size!(criterion, 5);
    benchmark_with_size!(criterion, 8);
    benchmark_with_size!(criterion, 13);
    benchmark_with_size!(criterion, 21);
    benchmark_with_size!(criterion, 34);
}
