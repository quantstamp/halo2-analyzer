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
use std::{collections::HashMap, marker::PhantomData};

use anyhow::{Context, Ok};
use korrekt::{
    circuit_analyzer::analyzer::Analyzer,
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
    },
};
use num::{BigInt, Num};
extern crate env_logger;
extern crate log;

use env_logger::Env;

use anyhow::Result;
use clap::{App, Arg, ArgMatches};
use korrekt::circuit_analyzer::halo2_proofs_libs::*;
use log::{info, warn};

fn main() -> Result<()> {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let matches = App::new("Halo2 Analyzer")
        .version("2.0")
        .author("fatemeh@guantstamp.com")
        .about("Analyzes circuits for various valnerabilities")
        .arg(Arg::new("profile")
            .short('p')
            .long("profile")
            .takes_value(true)
            .help("Select a predefined configuration profile: default, specific_public_input, random_public_input_five_iterations, random_uninterpreted, random_interpreted")
            .conflicts_with_all(&["lookup", "iterations", "type", "verification"]))
        .arg(Arg::new("type")
            .short('t')
            .long("type")
            .takes_value(true)
            .help("Type of analysis: unused_gates, unused_columns, unconstrained_cells, underconstrained_circuit")
            .required(true))
        .arg(Arg::new("lookup")
            .short('l')
            .long("lookup")
            .takes_value(true)
            .help("Sets the lookup method: uninterpreted, interpreted, inline")
            .required_if_eq("type", "underconstrained_circuit"))
        .arg(Arg::new("verification")
            .short('v')
            .long("verification")
            .takes_value(true)
            .help("Verification method: specific or random")
            .required_if_eq("type", "underconstrained_circuit"))
        .arg(Arg::new("iterations")
            .short('i')
            .long("iterations")
            .takes_value(true)
            .help("Number of iterations for random input verification")
            .required_if_eq("verification", "random"))
        .get_matches();

    let mut config = if let Some(profile) = matches.value_of("profile") {
        match profile {
            "default" => AnalyzerInput::default(),
            "specific_public_input" => AnalyzerInput::specific_public_input_inline_lookup(),
            "random_public_input_five_iterations" => {
                AnalyzerInput::random_public_input_five_iterations_inline_lookup()
            }
            "random_uninterpreted" => {
                AnalyzerInput::random_public_input_five_iterations_uninterpreted_lookup()
            }
            "random_interpreted" => {
                AnalyzerInput::random_public_input_five_iterations_interpreted_lookup()
            }
            _ => return Err(anyhow::anyhow!("Invalid configuration profile selected")),
        }
    } else {
        let analysis_type = parse_analysis_type(matches.value_of("type"));
        
        let verification_method = matches
            .value_of("verification")
            .map(parse_verification_method);

        ensure_no_conflicting_args(&matches, &analysis_type, verification_method.unwrap())?;
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

        setup_analyzer(
            lookup_method.unwrap(),
            iterations.unwrap_or(1),
            analysis_type,
            verification_method.unwrap(),
        )?
    };
    run_analysis(&mut config)?;

    Ok(())
}
fn parse_lookup_method(input: &str) -> LookupMethod {
    match input {
        "uninterpreted" => LookupMethod::Uninterpreted,
        "interpreted" => LookupMethod::Interpreted,
        "inline" => LookupMethod::InlineConstraints,
        _ => LookupMethod::InlineConstraints, // Default case
    }
}

fn parse_verification_method(input: &str) -> VerificationMethod {
    match input {
        "specific" => VerificationMethod::Specific,
        "random" => VerificationMethod::Random,
        _ => VerificationMethod::Random, // Default case
    }
}

fn parse_analysis_type(input: Option<&str>) -> AnalyzerType {
    match input {
        Some("unused_gates") => AnalyzerType::UnusedGates,
        Some("unused_columns") => AnalyzerType::UnusedColumns,
        Some("unconstrained_cells") => AnalyzerType::UnconstrainedCells,
        Some("underconstrained_circuit") => AnalyzerType::UnderconstrainedCircuit,
        _ => {
            warn!("No analysis type specified, defaulting to 'UnderconstrainedCircuit'");
            AnalyzerType::UnderconstrainedCircuit
        }
    }
}
fn ensure_no_conflicting_args(
    matches: &ArgMatches,
    analysis_type: &AnalyzerType,
    verification_method: VerificationMethod,
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
    match verification_method {
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
        analysis_type,
        verification_method,
        verification_input: VerificationInput {
            instances_string: HashMap::new(),
            iterations,
        },
        lookup_method,
    })
}

fn run_analysis(input: &mut AnalyzerInput) -> anyhow::Result<()> {
    let circuit = sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
    let k = 6;

    let mut analyzer = Analyzer::new(&circuit, k).unwrap();

    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();

    analyzer
        .dispatch_analysis(input, &prime)
        .context("Failed to perform analysis!")?;
    Ok(())
}
