use std::marker::PhantomData;
#[cfg(feature = "use_zcash_halo2_proofs")]
use halo2curves::bn256;
#[cfg(feature = "use_zcash_halo2_proofs")]
use zcash_halo2_proofs::pasta::Fp as Fr;


#[cfg(feature = "use_pse_halo2_proofs")]
use pse_halo2_proofs::halo2curves::bn256::Fr;
#[cfg(feature = "use_pse_halo2_proofs")]
use halo2curves::bn256;
#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::sample_circuits::pse as sample_circuits;
#[cfg(feature = "use_zcash_halo2_proofs")]
use korrekt::sample_circuits::zcash as sample_circuits;

use anyhow::{Context, Ok, Result};
use korrekt::{circuit_analyzer, io};
use num::{BigInt, Num};

fn main() -> Result<(), anyhow::Error> {
    let circuit: sample_circuits::copy_constraint::fibonacci::FibonacciCircuit<_> =
        sample_circuits::copy_constraint::fibonacci::FibonacciCircuit::<Fr>(PhantomData);
    let k: u32 = 5;
    
    let mut analyzer = circuit_analyzer::analyzer::Analyzer::new(&circuit,k).unwrap();//,vec![public_input]).unwrap();

    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();
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
