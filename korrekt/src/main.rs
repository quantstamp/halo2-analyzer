#[cfg(feature = "use_axiom_halo2_proofs")]
use korrekt::sample_circuits::axiom as sample_circuits;
#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::sample_circuits::pse as sample_circuits;
#[cfg(feature = "use_pse_v1_halo2_proofs")]
use korrekt::sample_circuits::pse_v1 as sample_circuits;
#[cfg(feature = "use_scroll_halo2_proofs")]
use korrekt::sample_circuits::scroll as sample_circuits;
#[cfg(feature = "use_zcash_halo2_proofs")]
use korrekt::sample_circuits::zcash as sample_circuits;
use std::{marker::PhantomData, path::Path, time::Instant};

use anyhow::{Context, Ok};
use korrekt::{
    circuit_analyzer::analyzer::Analyzer,
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationMethod,
    },
};
extern crate env_logger;
extern crate log;

use env_logger::Env;

use anyhow::Result;
use clap::{App, Arg, ArgMatches};
use korrekt::circuit_analyzer::halo2_proofs_libs::*;
use log::{info, warn};

fn main() -> Result<()> {
    //env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let matches = App::new("Halo2 Analyzer")
        .version("2.0")
        .author("fatemeh@guantstamp.com")
        .about("Analyzes circuits for various valnerabilities")
        .arg(Arg::new("profile")
        .short('p')
        .long("profile")
        .takes_value(true)
        .possible_values(&["specific_inline", "random_inline", "random_uninterpreted", "random_interpreted"])
        .conflicts_with_all(&["lookup", "iterations", "type", "verification"])
        .help("Select a predefined configuration profile"))
        .arg(Arg::new("type")
            .short('t')
            .long("type")
            .takes_value(true)
            .help("Type of analysis: unused_gates (ug), unused_columns (uc), unconstrained_cells (ucc), underconstrained_circuit (undcc)")
            .possible_values(&["unused_gates", "ug", "unused_columns", "uc", "unconstrained_cells", "ucc", "underconstrained_circuit", "undcc"])
            .required(true))
        .arg(Arg::new("lookup")
            .short('l')
            .long("lookup")
            .takes_value(true)
            .help("Sets the lookup method: uninterpreted (u), interpreted (i), inline (in)")
            .possible_values(&["uninterpreted", "u", "interpreted", "i", "inline", "in"])
            .required_if_eq_any(&[("type", "underconstrained_circuit"), ("type", "undcc")]))
        .arg(Arg::new("verification")
            .short('v')
            .long("verification")
            .takes_value(true)
            .help("Verification method: specific (s), random (r)")
            .possible_values(&["specific", "s", "random", "r"])
            .required_if_eq_any(&[("type", "underconstrained_circuit"), ("type", "undcc")]))
        .arg(Arg::new("iterations")
            .short('i')
            .long("iterations")
            .takes_value(true)
            .help("Number of iterations for random input verification (only needed if verification is 'random')")
            .required_if_eq_any(&[("verification", "random"),("verification", "r")]))
        .get_matches();

        let mut config = if let Some(profile) = matches.value_of("profile") {
            load_config_for_profile(profile)?
        }else {
        let analysis_type = parse_analysis_type(matches.value_of("type"));

        let verification_method = matches
            .value_of("verification")
            .map(parse_verification_method);

        let lookup_method = matches.value_of("lookup").map(parse_lookup_method);
        let iterations = matches
            .value_of("iterations")
            .map(|i| i.parse::<u128>().unwrap_or(1));

        info!("Analysis Type: {:?}", analysis_type);
        if let Some(lm) = lookup_method {
            info!("Lookup Method: {:?}", lm);
        }
        if let Some(vm) = verification_method {
            info!("Verification Method: {:?}", vm);
        }
        if let Some(it) = iterations {
            info!("Iterations: {}", it);
        }

        ensure_no_conflicting_args(&matches, &analysis_type, verification_method)?;

        setup_analyzer(
            lookup_method.unwrap_or(LookupMethod::None),
            iterations.unwrap_or(1),
            analysis_type,
            verification_method.unwrap_or(VerificationMethod::None),
        )?
    };
    run_analysis(&mut config)?;

    Ok(())
}
fn load_config_for_profile(profile: &str) -> Result<AnalyzerInput> {
    let config_path = format!("./src/config/{}.toml", profile);
    AnalyzerInput::load_config(Path::new(&config_path))
    .with_context(|| format!("Failed to load configuration for profile: {}", profile))
}
fn parse_lookup_method(input: &str) -> LookupMethod {
    match input {
        "uninterpreted" | "u" => LookupMethod::Uninterpreted,
        "interpreted" | "i" => LookupMethod::Interpreted,
        "inline" | "in" => LookupMethod::InlineConstraints,
        _ => LookupMethod::InlineConstraints, // Default case
    }
}

fn parse_verification_method(input: &str) -> VerificationMethod {
    match input {
        "specific" | "s" => VerificationMethod::Specific,
        "random" | "r" => VerificationMethod::Random,
        _ => VerificationMethod::Random, // Default case
    }
}

fn parse_analysis_type(input: Option<&str>) -> AnalyzerType {
    match input {
        Some("unused_gates") | Some("ug") => AnalyzerType::UnusedGates,
        Some("unused_columns") | Some("uc") => AnalyzerType::UnusedColumns,
        Some("unconstrained_cells") | Some("ucc") => AnalyzerType::UnconstrainedCells,
        Some("underconstrained_circuit") | Some("uncc") => AnalyzerType::UnderconstrainedCircuit,
        _ => {
            warn!("No analysis type specified, defaulting to 'UnderconstrainedCircuit'");
            AnalyzerType::UnderconstrainedCircuit
        }
    }
}
fn ensure_no_conflicting_args(
    matches: &ArgMatches,
    analysis_type: &AnalyzerType,
    verification_method: Option<VerificationMethod>,
) -> Result<()> {
    match analysis_type {
        AnalyzerType::UnusedGates
        | AnalyzerType::UnusedColumns
        | AnalyzerType::UnconstrainedCells => {
            if matches.is_present("lookup")
                || matches.is_present("verification")
                || matches.is_present("iterations")
            {
                return Err(anyhow::anyhow!(
                    "No additional flags should be set for the selected analysis type: {:?}",
                    analysis_type
                ));
            }
        }
        _ => {}
    }

    if matches!(analysis_type, AnalyzerType::UnderconstrainedCircuit) {
        match verification_method.unwrap() {
            VerificationMethod::Specific => {
                if matches.is_present("iterations") {
                    return Err(anyhow::anyhow!(
                    "No iterations flag should be set for the selected verification method: {:?}",
                    verification_method
                ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn setup_analyzer(
    lookup_method: LookupMethod,
    iterations: u128,
    analysis_type: AnalyzerType,
    verification_method: VerificationMethod,
) -> anyhow::Result<AnalyzerInput> {
    info!("Setting up analyzer with LookupMethod: {:?}, Iterations: {}, AnalysisType: {:?}, VerificationMethod: {:?}", lookup_method, iterations, analysis_type, verification_method);
    Ok(AnalyzerInput {
        verification_method,
        iterations,
        lookup_method,
    })
}

fn run_analysis(analyzer_input: &mut AnalyzerInput) -> anyhow::Result<()> {
    // Your circuit setup remains the same
    let circuit =
        sample_circuits::lookup_circuits::two_matched_lookups::MyCircuit::<
            Fr,
            34,
        >(PhantomData);
    let k = 11;

    // Start timer for Analyzer::new
    let start_new = Instant::now();
    let mut analyzer_setup = Analyzer::new(&circuit, k, AnalyzerType::UnderconstrainedCircuit, Some(analyzer_input))
        .unwrap();
    // End timer and print elapsed time
    let duration_new = start_new.elapsed();
    println!("Time elapsed in Analyzer::new: {:?}", duration_new);

    // Start timer for dispatch_analysis
    let start_dispatch = Instant::now();
    analyzer_setup.analyzer
        .dispatch_analysis(analyzer_input, &mut analyzer_setup.smt_file)
        .context("Failed to perform analysis!")?;
    // End timer and print elapsed time
    let duration_dispatch = start_dispatch.elapsed();
    println!("Time elapsed in dispatch_analysis: {:?}", duration_dispatch);

    Ok(())
}
