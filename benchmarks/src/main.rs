use serde::{Deserialize};
use serde_json::Result;
use std::collections::{BTreeMap, HashMap};
use std::{env, fs};
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
        .filter(|e| e.path().ends_with("new/estimates.json")) //&& e.file_name().to_string_lossy().contains("benchmark_fibo"))
    {
        let path = entry.path();
        let path_str = path.to_str().unwrap();
        let parts: Vec<&str> = path_str.split('/').collect();
        if let Some(size_part) = parts.iter().find(|&&s| s.starts_with("size_")) {
            let size: &str = *size_part;
            println!("Size: {} ", size);
            let benchmark_name = parts[parts.len() - 4];
            if let Ok(estimates) = read_and_parse_estimates(path_str) {
                benchmarks
                    .entry(size.to_string())
                    .or_insert_with(HashMap::new)
                    .insert(benchmark_name.to_string(), estimates.mean.point_estimate);
            }
        }
    }

    print_results(&benchmarks);

    Ok(())
}
fn print_results(benchmarks: &BTreeMap<String, HashMap<String, f64>>) {
    // Debug: print the entire benchmarks structure to see what's actually there

    println!("{:<10} {:<20} {:<20} {:<20} {:<20}", "Size", "Version 1 Time (ms)", "Version 2 Inline (ms)", "Version 2 Uninterpreted (ms)", "Version 2 Interpreted (ms)");
    for (size, results) in benchmarks {
        // Ensure you are using the exact keys that are used when inserting into the HashMap
        println!("{:<10} {:<20.2} {:<20.2} {:<20.2} {:<20.2}",
                 size,
                 results.get("underconstrained_fibo_v1").unwrap_or(&0.0),
                 results.get("underconstrained_fibo_v2").unwrap_or(&0.0),
                 results.get("some_other_benchmark_key_1").unwrap_or(&0.0),
                 results.get("some_other_benchmark_key_2").unwrap_or(&0.0)
        );
    }
}
