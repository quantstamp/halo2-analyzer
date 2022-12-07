use std::marker::PhantomData;
use halo2_examples::fibonacci::example1::MyCircuit;
//use super::MyCircuit;
use halo2_proofs::{dev::MockProver, pasta::Fp};

fn main() {
    println!("Printing out constraints in Halo2 Constraint format:");
    
    let k = 4;
    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(55); // F[9]

    let circuit = MyCircuit(PhantomData);

    let mut public_input = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    prover.assert_satisfied();

    public_input[2] += Fp::one();
    let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();

}