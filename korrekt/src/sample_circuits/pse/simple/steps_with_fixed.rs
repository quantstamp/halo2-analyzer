// ANCHOR: full
use std::{marker::PhantomData, net::IpAddr};

use pse_halo2_proofs::{
    circuit::{layouter, AssignedCell, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

use ff::{Field, PrimeField};

// ANCHOR: witness
pub struct TestCircuit<F: Field> {
    _ph: PhantomData<F>,
    a: Value<F>, // secret
    b: Value<F>, // secret
}

impl<Fr: PrimeField> Default for TestCircuit<Fr> {
    fn default() -> Self {
        TestCircuit {
            _ph: PhantomData,
            a: Value::known(Fr::from_u128(2)),
            b: Value::known(Fr::from_u128(4)),
        }
    }
}
// ANCHOR_END: witness

#[derive(Clone, Debug)]
pub struct TestConfig<F: PrimeField> {
    _ph: PhantomData<F>,
    advice: Column<Advice>,
    fixed: Column<Fixed>,
    arith: ArithmeticChip<F>,
}

#[derive(Debug, Clone)]
struct ArithmeticChip<F: PrimeField> {
    q_add: Selector,
    q_mul: Selector,
    q_fix: Selector,
    advice: Column<Advice>,
    fixed: Column<Fixed>,
    _ph: PhantomData<F>,
}

impl<F: PrimeField> ArithmeticChip<F> {
    // allocate a new unconstrained value
    fn free(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<F>, // this something prover knowns
    ) -> Result<AssignedCell<F, F>, Error> {
        // the region is going to have a height of 1
        // | Advice (advice) | Selector (q_mul) |
        // |              w0 |                0 |
        layouter.assign_region(
            || "free",
            |mut region| {
                let w0 = region.assign_advice(|| "w0", self.advice, 0, || value)?;
                Ok(w0)
            },
        )
    }

    // input = constant
    fn fixed(
        &self,
        layouter: &mut impl Layouter<F>,
        input: AssignedCell<F, F>,
        constant: F, // verifier (fixed in circuit)
    ) -> Result<(), Error> {
        // | Advice (advice) | Selector (q_fix) | Fixed (fixed) |
        // |             w0  |                1 |            c0 |
        layouter.assign_region(
            || "fixed",
            |mut region| {
                let w0 =
                    region.assign_advice(|| "w0", self.advice, 0, || input.value().cloned())?;
                let c0 = region.assign_fixed(|| "c0", self.fixed, 0, || Value::known(constant))?;

                // force input = w0
                region.constrain_equal(w0.cell(), input.cell())?;
                //println!("input is: {:?}", input);
                c0.copy_advice(|| "annotation", &mut region, self.advice, 0)?;
                self.q_fix.enable(&mut region, 0)?;
                Ok(())
            },
        )
    }

    // helper function to generate multiplication gates
    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // the region is going to have a height of 3
        // | Advice (advice) | Selector (q_mul) |
        // |              w0 |                1 |
        // |              w1 |                0 |
        // |              w2 |                0 |
        layouter.assign_region(
            || "mul",
            |mut region| {
                // turn on the gate
                self.q_mul.enable(&mut region, 0)?;

                // assign the witness value to the advice column
                let w0 = region.assign_advice(|| "w0", self.advice, 0, || lhs.value().cloned())?;

                let w1 = region.assign_advice(|| "w1", self.advice, 1, || rhs.value().cloned())?;

                let w2 = region.assign_advice(
                    || "w2",
                    self.advice,
                    2,
                    || lhs.value().cloned() * rhs.value().cloned(),
                )?;

                region.constrain_equal(w0.cell(), lhs.cell())?;
                region.constrain_equal(w1.cell(), rhs.cell())?;

                Ok(w2)
            },
        )
    }

    // helper function to generate multiplication gates
    fn add(
        &self,
        layouter: &mut impl Layouter<F>,
        lhs: AssignedCell<F, F>,
        rhs: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        // the region is going to have a height of 3
        // | Advice (advice) | Selector (q_mul) |
        // |              w0 |                1 |
        // |              w1 |                0 |
        // |              w2 |                0 |
        layouter.assign_region(
            || "add",
            |mut region| {
                // turn on the gate
                self.q_add.enable(&mut region, 0)?;

                // assign the witness value to the advice column
                let w0 = region.assign_advice(|| "w0", self.advice, 0, || lhs.value().cloned())?;

                let w1 = region.assign_advice(|| "w1", self.advice, 1, || rhs.value().cloned())?;

                let w2 = region.assign_advice(
                    || "w2",
                    self.advice,
                    2,
                    || lhs.value().cloned() + rhs.value().cloned(),
                )?;

                region.constrain_equal(w0.cell(), lhs.cell())?;
                region.constrain_equal(w1.cell(), rhs.cell())?;

                Ok(w2)
            },
        )
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: Column<Advice>,
        fixed: Column<Fixed>,
    ) -> Self {
        let q_mul = meta.complex_selector();
        let q_add = meta.complex_selector();
        let q_fix = meta.complex_selector();

        // if q_fix = 1: c0 = w0
        meta.create_gate("fixed", |meta| {
            let w0 = meta.query_advice(advice, Rotation::cur());
            let c0 = meta.query_fixed(fixed, Rotation::cur());
            let q_fix = meta.query_selector(q_fix);
            vec![q_fix * (w0 - c0)]
        });

        // define a new gate:
        // next = curr + 1 if q_enable is 1
        meta.create_gate("vertical-mul", |meta| {
            //            | Advice |
            // current -> |     w0 |
            //            |     w1 |
            //            |     w2 |
            let w0 = meta.query_advice(advice, Rotation::cur()); // current row
            let w1 = meta.query_advice(advice, Rotation::next()); // next row
            let w2 = meta.query_advice(advice, Rotation(2)); // next next row

            let q_mul = meta.query_selector(q_mul);

            // w2 = w1 * w0 <-- sat.
            vec![q_mul * (w1 * w0 - w2)]
        });

        // define a new gate:
        // next = curr + 1 if q_enable is 1
        meta.create_gate("vertical-add", |meta| {
            //            | Advice |
            // current -> |     w0 |
            //            |     w1 |
            //            |     w2 |
            let w0 = meta.query_advice(advice, Rotation::cur()); // current row
            let w1 = meta.query_advice(advice, Rotation::next()); // next row
            let w2 = meta.query_advice(advice, Rotation(2)); // next next row

            let q_add = meta.query_selector(q_add);

            // w2 = w1 * w0 <-- sat.
            vec![q_add * (w1 + w0 - w2)]
        });

        ArithmeticChip {
            q_add,
            q_mul,
            q_fix,
            advice,
            fixed,
            _ph: PhantomData,
        }
    }
}

impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        TestCircuit {
            _ph: PhantomData,
            a: Value::unknown(),
            b: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = meta.advice_column();
        let fixed = meta.fixed_column();

        // this will allow us to have equality constraints
        meta.enable_equality(advice);
        meta.enable_equality(fixed);

        let arith = ArithmeticChip::configure(meta, advice, fixed);

        TestConfig {
            _ph: PhantomData,
            fixed,
            advice,
            arith,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config, //
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let a = config.arith.free(&mut layouter, self.a)?;
        let b = config.arith.free(&mut layouter, self.b)?;
        let c = config.arith.mul(&mut layouter, a.clone(), b.clone())?;
        let d = config.arith.mul(&mut layouter, a.clone(), c.clone())?;
        config.arith.fixed(&mut layouter, c, F::from_u128(8))?;
        config.arith.fixed(&mut layouter, d, F::from_u128(16))?;
        Ok(())
    }
}
