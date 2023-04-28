use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector,
};
use halo2_proofs::circuit::{Layouter, Value, SimpleFloorPlanner};
use halo2_proofs::plonk::Error;
use halo2_proofs::poly::Rotation;

pub struct BitDecompositon<F: FieldExt, const COUNT: usize> {
    b: [F; COUNT],
    // TODO: Consider adding the non decomposed version of b
}

#[derive(Clone)]
pub struct BitDecompositonConfig<const COUNT: usize> {
    b: [Column<Advice>; COUNT],
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt, const COUNT: usize> BitDecompositon<F, COUNT> {
    // pub fn new(b: [F; COUNT]) -> Self {
    //     BitDecompositon {
    //         b
    //     }
    // }
}

impl<F: FieldExt, const COUNT: usize> Default for BitDecompositon<F, COUNT> {
    fn default() -> Self {
        BitDecompositon {
            b: [F::one(); COUNT]
        }
    }
}

impl<F: FieldExt, const COUNT: usize> Circuit<F> for BitDecompositon<F, COUNT> {
    type Config = BitDecompositonConfig<COUNT>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // TODO: make this look prettier later!
        let mut b: [Column<Advice>; COUNT] = [Column::new(0, Advice); COUNT];
        for i in 0..COUNT {
            b[i] = meta.advice_column();
        }
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // define gates
        for i in 0..COUNT {
            // TODO: Figure out how to annotate with i set dynamically 
            meta.create_gate("bi_binary_check", |meta| {
                let a = meta.query_advice(b[i], Rotation::cur());
                let dummy = meta.query_selector(s);
                vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
                // bi * (1-bi)
            });
        }

        meta.create_gate("equality", |meta| {
            let mut exp = Expression::Constant(F::from(0));
            let mut t  = F::from(1);
            for i in 0..COUNT {
                let bi = meta.query_advice(b[i], Rotation::cur());
                exp = exp + Expression::Constant(t) * bi;
                t = t * F::from(2);
            }

            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            // vec![dummy * (a + b - c)]
            vec![dummy * (exp - c)]
        });

        let cfg = Self::Config {
            b,
            x,
            i,
            s,
        };

        cfg
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let out = layouter
            .assign_region(
                || "The Region",
                |mut region| {
                    config.s.enable(&mut region, 0)?;
                    for i in 0..COUNT {
                        region.assign_advice(|| "bi", config.b[i], 0, || Value::known(self.b[0]))?;
                    }
                    
                    let mut compose_b = F::from(0);
                    for i in 0..COUNT-1 {
                        compose_b = F::from(2)*compose_b + self.b[COUNT-1-i];
                    }
                    compose_b = compose_b + self.b[0];
                    
                    let out = region.assign_advice(
                        || "x",
                        config.x,
                        0,
                        || Value::known(compose_b),
                    )?;

                    Ok(out)
                },
            )
            .unwrap();
        // expose the public input
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}


pub struct BitDecompositonUnderConstrained<F: FieldExt, const COUNT: usize> {
    b: [F; COUNT],
    // TODO: Consider adding the non decomposed version of b
}

#[derive(Clone)]
pub struct BitDecompositonUnderConstrainedConfig<const COUNT: usize> {
    b: [Column<Advice>; COUNT],
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt, const COUNT: usize> BitDecompositonUnderConstrained<F, COUNT> {
    pub fn new(b: [F; COUNT]) -> Self {
        BitDecompositonUnderConstrained {
            b
        }
    }
}

impl<F: FieldExt, const COUNT: usize> Default for BitDecompositonUnderConstrained<F, COUNT> {
    fn default() -> Self {
        BitDecompositonUnderConstrained {
            b: [F::one(); COUNT]
        }
    }
}

impl<F: FieldExt, const COUNT: usize> Circuit<F> for BitDecompositonUnderConstrained<F, COUNT> {
    type Config = BitDecompositonUnderConstrainedConfig<COUNT>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // TODO: make this look prettier later!
        let mut b: [Column<Advice>; COUNT] = [Column::new(0, Advice); COUNT];
        for i in 0..COUNT {
            b[i] = meta.advice_column();
        }
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // define gates
        // NOTICE: introducing under-constrained bug
        // The for loop has to start from 1, but we introduce the bug by starting from 0
        // hence b[0] will be left not constrained properly.
        for i in 1..COUNT {
            // TODO: Figure out how to annotate with i set dynamically 
            meta.create_gate("bi_binary_check", |meta| {
                let a = meta.query_advice(b[i], Rotation::cur());
                let dummy = meta.query_selector(s);
                vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
                // bi * (1-bi)
            });
        }

        meta.create_gate("equality", |meta| {
            let mut exp = Expression::Constant(F::from(0));
            let mut t  = F::from(1);
            for i in 0..COUNT {
                let bi = meta.query_advice(b[i], Rotation::cur());
                exp = exp + Expression::Constant(t) * bi;
                t = t * F::from(2);
            }

            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            // vec![dummy * (a + b - c)]
            vec![dummy * (exp - c)]
        });

        let cfg = Self::Config {
            b,
            x,
            i,
            s,
        };

        cfg
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let out = layouter
            .assign_region(
                || "The Region",
                |mut region| {
                    config.s.enable(&mut region, 0)?;
                    for i in 0..COUNT {
                        region.assign_advice(|| "bi", config.b[i], 0, || Value::known(self.b[0]))?;
                    }
                    
                    let mut compose_b = F::from(0);
                    for i in 0..COUNT-1 {
                        compose_b = F::from(2)*compose_b + self.b[COUNT-1-i];
                    }
                    compose_b = compose_b + self.b[0];
                    
                    let out = region.assign_advice(
                        || "x",
                        config.x,
                        0,
                        || Value::known(compose_b),
                    )?;

                    Ok(out)
                },
            )
            .unwrap();
        // expose the public input
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}
