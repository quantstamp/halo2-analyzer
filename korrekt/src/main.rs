use clap::{App, Arg};
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

use crate::circuit_analyzer::halo2_proofs_libs::*;

use anyhow::{Context, Ok};
use korrekt::{
    circuit_analyzer::{self, analyzer::Analyzer},
    io::analyzer_io_type::{
        AnalyzerInput, AnalyzerType, LookupMethod, VerificationInput, VerificationMethod,
    },
};
use num::{BigInt, Num};
extern crate env_logger;
extern crate log;

use env_logger::Env;

use anyhow::Result;
use korrekt::circuit_analyzer::halo2_proofs_libs::*;
use log::{info, warn};

fn main() -> Result<()> {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let matches = App::new("Circuit Analyzer")
        .version("1.0")
        .author("Your Name <your_email@example.com>")
        .about("Analyzes circuits using different parameters and methods")
        .arg(Arg::new("profile")
        .short('p')
        .long("profile")
        .takes_value(true)
        .help("Select a predefined configuration profile: default, specific_public_input, random_public_input_five_iterations, random_uninterpreted, random_interpreted"))
        .arg(Arg::new("lookup")
            .short('l')
            .long("lookup")
            .takes_value(true)
            .help("Sets the lookup method: uninterpreted, interpreted, inline"))
        .arg(Arg::new("iterations")
            .short('i')
            .long("iterations")
            .takes_value(true)
            .help("Number of iterations for random input verification"))
        .arg(Arg::new("type")
            .short('t')
            .long("type")
            .takes_value(true)
            .help("Type of analysis: unused_gates, unused_columns, unconstrained_cells, underconstrained_circuit"))
        .arg(Arg::new("verification")
            .short('v')
            .long("verification")
            .takes_value(true)
            .help("Verification method: specific or random"))
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
        let lookup_method = parse_lookup_method(matches.value_of("lookup"));
        let iterations = matches
            .value_of("iterations")
            .unwrap_or("1")
            .parse::<u128>()
            .unwrap_or(1);
        let analysis_type = parse_analysis_type(matches.value_of("type"));
        let verification_method = parse_verification_method(matches.value_of("verification"));

        let analyzer_input = setup_analyzer(
            lookup_method,
            iterations,
            analysis_type,
            verification_method,
        )?;
        analyzer_input
    };

    run_analysis(&mut config)?;

    Ok(())
}

fn parse_lookup_method(input: Option<&str>) -> LookupMethod {
    match input {
        Some("uninterpreted") => LookupMethod::Uninterpreted,
        Some("interpreted") => LookupMethod::Interpreted,
        Some("inline") => LookupMethod::InlineConstraints,
        _ => {
            warn!("No lookup method provided, defaulting to 'InlineConstraints'");
            LookupMethod::InlineConstraints
        }
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

fn parse_verification_method(input: Option<&str>) -> VerificationMethod {
    match input {
        Some("specific") => VerificationMethod::Specific,
        Some("random") => VerificationMethod::Random,
        _ => {
            warn!("No verification method specified, using 'Random' as default");
            VerificationMethod::Random
        }
    }
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
