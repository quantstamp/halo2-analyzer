use std::marker::PhantomData;
#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::sample_circuits::pse as sample_circuits;
#[cfg(feature = "use_zcash_halo2_proofs")]
use korrekt::sample_circuits::zcash as sample_circuits;
#[cfg(feature = "use_axiom_halo2_proofs")]
use korrekt::sample_circuits::axiom as sample_circuits;

use crate::circuit_analyzer::halo2_proofs_libs::*;

use anyhow::{Context, Ok, Result};
use korrekt::{circuit_analyzer, io};
use num::{BigInt, Num};

fn main() -> Result<(), anyhow::Error> {
    // let circuit =
    //     sample_circuits::copy_constraint::fibonacci_constant_init::FibonacciCircuit::<Fr>(PhantomData);
    // let k: u32 = 5;
    
    // let mut analyzer = circuit_analyzer::analyzer::Analyzer::new(&circuit,k).unwrap();//,vec![public_input]).unwrap();

    // let modulus = bn256::fr::MODULUS_STR;
    // let without_prefix = modulus.trim_start_matches("0x");
    // let prime = BigInt::from_str_radix(without_prefix, 16)
    //     .unwrap()
    //     .to_string();
    // let modulus = bn256::fr::MODULUS_STR;
    // let without_prefix = modulus.trim_start_matches("0x");
    // let prime = BigInt::from_str_radix(without_prefix, 16)
    //     .unwrap()
    //     .to_string();

    // let analyzer_type = io::analyzer_io::retrieve_user_input_for_analyzer_type()
    //     .context("Failed to retrieve the user inputs!")?;

    // let t = analyzer
    //     .dispatch_analysis(analyzer_type, &prime)
    //     .context("Failed to perform analysis!")?;
    Ok(())
}