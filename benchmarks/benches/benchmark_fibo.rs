#![allow(unused)]
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use halo2_proofs::halo2curves::bn256::Fr;
use num::BigInt;
use std::marker::PhantomData;

mod benchmark_fibo_v1;
mod benchmark_fibo_v2_inline;

use benchmark_fibo_v1::run_underconstrained_benchmark_for_specified_size as v1_benchmark;
use benchmark_fibo_v2_inline::run_underconstrained_benchmark_for_specified_size as v2_benchmark_inline;

macro_rules! run_underconstrained_benchmarks {
    ($c:expr, $($size:expr),*) => {
        let mut group = $c.benchmark_group("benchmark_fibo");
        group.sample_size(20);
        $(
            // Benchmark for version 1
            group.bench_with_input(BenchmarkId::new(format!("Version 1 - Size {}", $size), $size), &$size, |b, &_size| {
                b.iter(|| v1_benchmark::<$size>())
            });

            // Benchmark for version 2
            group.bench_with_input(BenchmarkId::new(format!("Version 2 - Size {}", $size), $size), &$size, |b, &_size| {
                b.iter(|| v2_benchmark_inline::<$size>())
            });
        )*
        group.finish();
    };
}

// Define a function that utilizes the macro to setup and run benchmarks
fn run_benchmarks(c: &mut Criterion) {
    run_underconstrained_benchmarks!(c, 5, 8, 13, 21, 34);
}

criterion_group!(benches, run_benchmarks);
criterion_main!(benches);
