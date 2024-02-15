mod benchmark_bit_decomp;
mod benchmark_fibo_v2;
mod benchmark_fibo_v1;

fn main() {
    let results_v1 = benchmark_fibo_v1::run_benchmark();
    let results_v2 = benchmark_fibo_v2::run_benchmark();

    println!("{:<10} {:<20} {:<20}", "Size", "Version 1 Time", "Version 2 Time");
    for ((size_v1, time_v1), (_, time_v2)) in results_v1.iter().zip(results_v2.iter()) {
        println!("{:<10} {:<20?} {:<20?}", size_v1, time_v1, time_v2);
    }
}
