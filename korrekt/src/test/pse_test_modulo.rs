#[cfg(test)]
mod test {
    use crate::circuit_analyzer::analyzer::Analyzer;
    use crate::io::{
        analyzer_io_type,
        analyzer_io_type::{AnalyzerOutputStatus, VerificationInput, VerificationMethod},
    };
    use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
    use halo2_proofs::{
        arithmetic::FieldExt,
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::bn256,
        halo2curves::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
        poly::Rotation,
    };
    use num::{BigInt, Num};
    use std::marker::PhantomData;


    use zkevm_circuits::evm_circuit::util::math_gadget::ModGadget;
    use zkevm_circuits::{
        evm_circuit::util::{
            self, constraint_builder::ConstraintBuilder, math_gadget::*, sum, CachedRegion,
        },
        util::Expr,
    };
    use eth_types::{Field, ToLittleEndian, Word};

    use crate::test::test_util::*;
    use zkevm_circuits::evm_circuit::*;
    use halo2_proofs::halo2curves::bn256::Fr;

    #[derive(Clone)]
    /// ModGadgetTestContainer: require(a % n == r)
    struct ModGadgetTestContainer<F> {
        mod_gadget: ModGadget<F>,
        a: util::Word<F>,
        n: util::Word<F>,
        r: util::Word<F>,
    }

    impl<F: Field> MathGadgetContainer<F> for ModGadgetTestContainer<F> {
        fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
            let a = cb.query_word();
            let n = cb.query_word();
            let r = cb.query_word();
            let mod_gadget = ModGadget::<F>::construct(cb, [&a, &n, &r]);
            ModGadgetTestContainer {
                mod_gadget,
                a,
                n,
                r,
            }
        }

        fn assign_gadget_container(
            &self,
            witnesses: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error> {
            let a = witnesses[0];
            let n = witnesses[1];
            let a_reduced = witnesses[2];
            let offset = 0;

            self.a.assign(region, offset, Some(a.to_le_bytes()))?;
            self.n.assign(region, offset, Some(n.to_le_bytes()))?;
            self.r
                .assign(region, offset, Some(a_reduced.to_le_bytes()))?;
            self.mod_gadget.assign(region, 0, a, n, a_reduced, F::one())
        }
    }

    // #[test]
    // fn test_mod_n_expected_rem() {
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![Word::from(0), Word::from(0), Word::from(0)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![Word::from(1), Word::from(0), Word::from(0)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![Word::from(548), Word::from(50), Word::from(48)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![Word::from(30), Word::from(50), Word::from(30)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![WORD_LOW_MAX, Word::from(1024), Word::from(1023)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![WORD_HIGH_MAX, Word::from(1024), Word::from(0)],
    //         true,
    //     );
    //     try_test!(
    //         ModGadgetTestContainer<Fr>,
    //         vec![WORD_CELL_MAX, Word::from(2), Word::from(0)],
    //         true,
    //     );
    // }

    #[test]
    fn test_mod_n_unexpected_rem() {
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(1), Word::from(1), Word::from(1)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(46), Word::from(50), Word::from(48)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_LOW_MAX, Word::from(999999), Word::from(888888)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_CELL_MAX, Word::from(999999999), Word::from(666666666)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_HIGH_MAX, Word::from(999999), Word::from(777777)],
            false,
        );
    }
}