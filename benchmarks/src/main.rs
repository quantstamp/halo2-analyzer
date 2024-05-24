use serde::Deserialize;
use serde_json::Result;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use walkdir::WalkDir;

#[derive(Deserialize, Debug)]
struct Estimates {
    mean: Metric,
}

#[derive(Deserialize, Debug)]
struct Metric {
    point_estimate: f64,
}

fn read_and_parse_estimates(file_path: &str) -> Result<Estimates> {
    let data = fs::read_to_string(file_path).unwrap();
    if data.is_empty() {
        eprintln!("Warning: No data found in {}", file_path);
    }
    match serde_json::from_str::<Estimates>(&data) {
        Ok(estimates) => Ok(estimates),
        Err(e) => {
            eprintln!("Error parsing JSON from {}: {}", file_path, e);
            Err(e)
        }
    }
}


fn main() -> Result<()> {
    let root_dir = "../target"; // Hardcoded to the directory where benchmarks are placed
    let mut benchmarks = BTreeMap::new();

    // Search through the `korrekt` directory for `estimates.json` files
    for entry in WalkDir::new(root_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().ends_with("new/estimates.json"))
    {
        let path = entry.path();
        let path_str = path.to_str().unwrap();
        let parts: Vec<&str> = path_str.split('/').collect();
        if let Some(size_part) = parts.iter().find(|&&s| s.starts_with("size_")) {
            let size: &str = *size_part;
            let benchmark_name = parts[parts.len() - 4];
            if let Ok(estimates) = read_and_parse_estimates(path_str) {
                benchmarks
                    .entry(size.to_string())
                    .or_insert_with(HashMap::new)
                    .insert(benchmark_name.to_string(), estimates.mean.point_estimate);
            }
        }
    }

    print_fibo_results(&benchmarks);

    print_lookup_results(&benchmarks);

    print_matched_lookup_results(&benchmarks);

    Ok(())
}

fn print_fibo_results(benchmarks: &BTreeMap<String, HashMap<String, f64>>) {
    // Prepare the output headers
    print!("Fibonacci Benchmark Results\n");
    println!("{:<10} {:<20} {:<20} {:<20} {:<20}", "Size", "Version 1 Time (ms)", "Version 2 Inline (ms)", "Version 2 Uninterpreted (ms)", "Version 2 Interpreted (ms)");

    // Iterate through the benchmark data
    for (size, results) in benchmarks {
        // Check if the size contains an entry for any of the benchmark categories
        let has_data = results.get("underconstrained_fibo_v1").is_some()
            || results.get("underconstrained_fibo_v2_inline").is_some()
            || results.get("underconstrained_fibo_v2_uninterpreted").is_some()
            || results.get("underconstrained_fibo_v2_interpreted").is_some();

        // Skip sizes that have no data in any category
        if has_data {
            println!("{:<10} {:<20.2} {:<20.2} {:<20.2} {:<20.2}",
                     size,
                     results.get("underconstrained_fibo_v1").unwrap_or(&0.0),
                     results.get("underconstrained_fibo_v2_inline").unwrap_or(&0.0),
                     results.get("underconstrained_fibo_v2_uninterpreted").unwrap_or(&0.0),
                     results.get("underconstrained_fibo_v2_interpreted").unwrap_or(&0.0)
            );
        }
    }
}

fn print_lookup_results(benchmarks: &BTreeMap<String, HashMap<String, f64>>) {
    println!("Lookup Benchmark Results");
    // Prepare the output headers
    println!("{:<10} {:<20} {:<20} {:<20} {:<20}", "Size", "Version 1 Time (ms)", "Version 2 Inline (ms)", "Version 2 Uninterpreted (ms)", "Version 2 Interpreted (ms)");

    // Iterate through the benchmark data
    for (size, results) in benchmarks {
        // Check if the size contains an entry for any of the benchmark categories
        let has_data = results.get("underconstrained_lookup_v1").is_some()
            || results.get("underconstrained_lookup_v2_inline").is_some()
            || results.get("underconstrained_lookup_v2_uninterpreted").is_some()
            || results.get("underconstrained_lookup_v2_interpreted").is_some();

        // Skip sizes that have no data in any category
        if has_data {
            println!("{:<10} {:<20.2} {:<20.2} {:<20.2} {:<20.2}",
                     size,
                     results.get("underconstrained_lookup_v1").unwrap_or(&0.0),
                     results.get("underconstrained_lookup_v2_inline").unwrap_or(&0.0),
                     results.get("underconstrained_lookup_v2_uninterpreted").unwrap_or(&0.0),
                     results.get("underconstrained_lookup_v2_interpreted").unwrap_or(&0.0)
            );
        }
    }
}

fn print_matched_lookup_results(benchmarks: &BTreeMap<String, HashMap<String, f64>>) {
    println!("Matched Lookup Benchmark Results");
    // Prepare the output headers
    println!("{:<10} {:<20} {:<20}", "Size", "Version 2 Inline (ms)", "Version 2 Interpreted (ms)");

    // Iterate through the benchmark data
    for (size, results) in benchmarks {
        // Check if the size contains an entry for any of the benchmark categories
        let has_data = results.get("underconstrained_multiple_matched_lookup_v2_inline").is_some()
            || results.get("underconstrained_multiple_matched_lookup_v2_interpreted").is_some();

        // Skip sizes that have no data in any category
        if has_data {
            println!("{:<10} {:<20.2} {:<20.2}",
                     size,
                     results.get("underconstrained_multiple_matched_lookup_v2_inline").unwrap_or(&0.0),
                     results.get("underconstrained_multiple_matched_lookup_v2_interpreted").unwrap_or(&0.0),
            );
        }
    }
}
