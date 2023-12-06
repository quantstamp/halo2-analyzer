use halo2_proofs::dev::MockProver;
use halo2curves::bn256;
use halo2curves::bn256::Fr;
//use pasta_curves::arithmetic::FieldExt;
//use ff::Field;
use anyhow::{Context, Ok, Result};
use korrekt::{circuit_analyzer, io, sample_circuits};
use num::{BigInt, Num};
use halo2_proofs::pasta::Fp;
use group::ff::Field;
use crate::circuit_analyzer::analyzer::Analyzer;

fn main() -> Result<(), anyhow::Error> {
    //How to run our analysis on a circuit.
    let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<Fp>::default();
    let mut analyzer = Analyzer::from(&circuit);
    let k = 11;

    let public_input = vec![Fp::from(3)];
    let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();

    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    //let prime = "307";
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();

    let analyzer_type = io::analyzer_io::retrieve_user_input_for_analyzer_type()
        .context("Failed to retrieve the user inputs!")?;

    analyzer
        .dispatch_analysis(analyzer_type, prover.fixed, &prime)
        .context("Failed to perform analysis!")?;
    Ok(())
}
