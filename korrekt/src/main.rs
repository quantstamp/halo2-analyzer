//use std::marker::PhantomData;
use halo2_proofs::{dev::MockProver, pasta::Fp};

mod benchmarks;
mod circuit_analyzer;
mod io;
mod sample_circuits;
mod smt_solver;
mod test;

use anyhow::{Context, Error, Ok, Result};
use io::analyzer_io;

use crate::circuit_analyzer::analyzer::Analyzer;
use crate::io::{
    analyzer_io_type,
    analyzer_io_type::{AnalyzerOutputStatus, VerificationInput, VerificationMethod},
};
use std::collections::HashMap;
use std::marker::PhantomData;

fn main() -> Result<(), anyhow::Error> {
    // How to run our analysis on a circuit.
    let circuit = sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fp>(PhantomData);
    //let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = circuit_analyzer::analyzer::Analyzer::create_with_circuit(&circuit);
    let k = 6;

    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(6); // F[9]

    let public_input = vec![a, b, out];

    let prover: MockProver<Fp> = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();

    let analyzer_type =io::analyzer_io::retrieve_user_input_for_analyzer_type().context("Failed to retrieve the user inputs!")?;
    
    analyzer.dispatch_analysis(analyzer_type, prover.fixed).context("Failed to perform analysis!")?;

    // The benchmark for underconstrained analysis.
    //benchmark::run_benchmark();
    Ok(())
}
