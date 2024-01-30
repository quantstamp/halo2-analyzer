

#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::{circuit_analyzer::{analyzer::Analyzer, halo2_proofs_libs::*}, sample_circuits::pse::copy_constraint::fibonacci_constant_init};
#[cfg(feature = "use_axiom_halo2_proofs")]
use korrekt::{sample_circuits::axiom::copy_constraint::fibonacci_pse_base}; //sample_circuits::axiom::copy_constraint::fibo_gpt};
#[cfg(feature = "use_axiom_halo2_proofs")]
use korrekt::{io::{
        self,
        analyzer_io_type::{self, VerificationInput, VerificationMethod},
    }, sample_circuits::axiom::copy_constraint::{fibonacci, fibonacci_old}
};
#[cfg(feature = "use_zcash_halo2_proofs")]
use halo2curves::bn256;
use zcash_halo2_proofs::pasta::Fp as Fr;
#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::{io::{
        self,
        analyzer_io_type::{self, VerificationInput, VerificationMethod},
    }, sample_circuits::pse::copy_constraint::{fibonacci}
};
#[cfg(feature = "use_zcash_halo2_proofs")]
use korrekt::{circuit_analyzer::analyzer::Analyzer,io::{
        self,
        analyzer_io_type::{self, VerificationInput, VerificationMethod},
    }, sample_circuits::zcash::copy_constraint::{fibonacci}
};
//use std::marker::PhantomData;

#[cfg(feature = "use_axiom_halo2_proofs")]
use korrekt::sample_circuits::axiom as sample_circuits;
#[cfg(feature = "use_pse_halo2_proofs")]
use korrekt::sample_circuits::pse as sample_circuits;
#[cfg(feature = "use_zcash_halo2_proofs")]
use korrekt::sample_circuits::zcash as sample_circuits;

use anyhow::{Context, Ok, Result};
use num::{BigInt, Num};

fn main() -> Result<(), anyhow::Error> {
    //let circuit:sample_circuits::bit_decomposition::two_bit_decomp_axiom::TwoBitDecompCircuit<Fr> = sample_circuits::bit_decomposition::two_bit_decomp_axiom::TwoBitDecompCircuit::default();
    //let public_input: Vec<Fr> = vec![Fr::from(3)];
    let circuit = fibonacci::FibonacciCircuit::<Fr>::default();
    //let public_input = vec![Fr::from(1),Fr::from(1),Fr::from(3)];
    // let circuit:fibo_gpt::FibonacciCircuit<Fr> = fibo_gpt::FibonacciCircuit {
    //     initial: 1u64.into(),
    //     steps: 10,
    // };
    let k: u32 = 5;

    let mut analyzer = Analyzer::new(&circuit, k).unwrap();

    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();

    // let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
    //     verification_method: VerificationMethod::Specific,
    //     verification_input: VerificationInput {
    //         instances_string: analyzer.instace_cells.clone(),
    //         iterations: 5,
    //     },
    // };
    let analyzer_type = io::analyzer_io::retrieve_user_input_for_analyzer_type()
    .context("Failed to retrieve the user inputs!")?;
    let output_status = analyzer
        .dispatch_analysis(analyzer_type, &prime)
        .unwrap()
        .output_status;

    //let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![]).unwrap();
    //prover.verify().unwrap();
    //println!("{:?}",prover);
    //println!("analyzer.permutation: {:?}",analyzer.permutation);
    Ok(())
}
