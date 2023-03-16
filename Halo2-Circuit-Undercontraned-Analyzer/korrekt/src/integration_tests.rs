
#[cfg(test)]
mod tests {
    use crate::sample_circuits;
    use crate::analyzer;
    use halo2_proofs::{pasta::Fp as Fr, dev::MockProver};
    #[test]
    fn create_play_circuit() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }
    #[test]
    fn create_multi_play_circuit() {
        let circuit = sample_circuits::MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }
}