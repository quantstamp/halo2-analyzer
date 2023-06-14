use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256;
use halo2_proofs::halo2curves::bn256::Fr;

use anyhow::{Context, Ok, Result};
use korrekt::{circuit_analyzer, io, sample_circuits};
use num::{BigInt, Num};

fn main() -> Result<(), anyhow::Error> {
    //How to run our analysis on a circuit.
    let circuit =
        sample_circuits::lookup_circuits::lookup_underconstrained::MyCircuit::<Fr>::default();
    let mut analyzer = circuit_analyzer::analyzer::Analyzer::from(&circuit);
    let k = 6;

    let a = Fr::from(1);
    let b = Fr::from(1);
    let out = Fr::from(6);

    let public_input = vec![a, b, out];

    let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
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
