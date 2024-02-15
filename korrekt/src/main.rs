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
use std::marker::PhantomData;

use crate::circuit_analyzer::halo2_proofs_libs::*;

use anyhow::{Context, Ok, Result};
use korrekt::{circuit_analyzer::{self, analyzer::Analyzer}, io};
use num::{BigInt, Num};
extern crate log;
extern crate env_logger;

use log::{info, LevelFilter};
use env_logger::Env;
fn main() -> Result<(), anyhow::Error> {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let circuit =
        sample_circuits::lookup_circuits::multiple_lookups_zcash::MyCircuit::<Fr>(PhantomData);
    let k = 6;

    let mut analyzer = Analyzer::new(&circuit, k).unwrap();


    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();

    let analyzer_type = io::analyzer_io::retrieve_user_input_for_analyzer_type()
        .context("Failed to retrieve the user inputs!")?;

    let t = analyzer
        .dispatch_analysis(analyzer_type, &prime)
        .context("Failed to perform analysis!")?;
    Ok(())
}
