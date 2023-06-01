use halo2_proofs::{dev::MockProver, pasta::Fp};

mod benchmarks;
mod circuit_analyzer;
mod io;
mod sample_circuits;
mod smt_solver;
mod test;

use anyhow::{Context, Ok, Result};

use std::marker::PhantomData;

fn main() -> Result<(), anyhow::Error> {
    //How to run our analysis on a circuit.
    let circuit = sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fp>(PhantomData);
    let mut analyzer = circuit_analyzer::analyzer::Analyzer::create_with_circuit(&circuit);
    let k = 6;

    let a = Fp::from(1);
    let b = Fp::from(1);
    let out = Fp::from(6);

    let public_input = vec![a, b, out];

    let prover: MockProver<Fp> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

    let analyzer_type = io::analyzer_io::retrieve_user_input_for_analyzer_type()
        .context("Failed to retrieve the user inputs!")?;

    analyzer
        .dispatch_analysis(analyzer_type, prover.fixed)
        .context("Failed to perform analysis!")?;
    Ok(())
}
