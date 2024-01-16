use std::{collections::{HashSet, HashMap}, ops::Range};

use anyhow:: Result;
use halo2_proofs::{
    arithmetic::{FieldExt as Field, Group},
    circuit::{self, Value},
    dev::{CellValue, Region},
    plonk::{
        permutation, Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem,
        Error as Error, Fixed, FloorPlanner, Instance, Selector,
    },
};

#[derive(Debug)]
pub struct Analyzable<F: Field> {
    pub k: u32,
    pub cs: ConstraintSystem<F>,
    /// The regions in the circuit.
    pub regions: Vec<Region>,
    /// The current region being assigned to. Will be `None` after the circuit has been
    /// synthesized.
    pub current_region: Option<Region>,
    // The fixed cells in the circuit, arranged as [column][row].
    pub fixed: Vec<Vec<CellValue<F>>>,
    // The advice cells in the circuit, arranged as [column][row].
    pub selectors: Vec<Vec<bool>>,
    pub permutation: permutation::keygen::Assembly,
    // A range of available rows for assignment and copies.
    pub usable_rows: Range<usize>,
}

impl<F: Field + Group> Assignment<F> for Analyzable<F> {
    fn enter_region<NR, N>(&mut self, name: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        assert!(self.current_region.is_none());
        self.current_region = Some(Region {
            name: name().into(),
            columns: HashSet::default(),
            rows: None,
            enabled_selectors: HashMap::default(),
            cells: HashMap::default(),
        });
    }

    fn exit_region(&mut self) {
        self.regions.push(self.current_region.take().unwrap());
    }

    fn enable_selector<A, AR>(
        &mut self,
        _: A,
        selector: &Selector,
        row: usize,
    ) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // Track that this selector was enabled. We require that all selectors are enabled
        // inside some region (i.e. no floating selectors).
        self.current_region
            .as_mut()
            .unwrap()
            .enabled_selectors
            .entry(*selector)
            .or_default()
            .push(row);

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(
        &self,
        column: Column<Instance>,
        row: usize,
    ) -> Result<circuit::Value<F>, Error> {
        Ok(Value::unknown())
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> circuit::Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if let Some(region) = self.current_region.as_mut() {
            region.update_extent(column.into(), row);
            region
                .cells
                .entry((column.into(), row))
                .and_modify(|count| *count += 1)
                .or_default();
        }

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> circuit::Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        if let Some(region) = self.current_region.as_mut() {
            region.update_extent(column.into(), row);
            region
                .cells
                .entry((column.into(), row))
                .and_modify(|count| *count += 1)
                .or_default();
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .ok_or(Error::BoundsFailure)? =
            CellValue::Assigned(to().into_field().evaluate().assign()?);

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.permutation
            .copy(left_column, left_row, right_column, right_row)
    }

    fn fill_from_row(
        &mut self,
        col: Column<Fixed>,
        from_row: usize,
        to: circuit::Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        for row in self.usable_rows.clone().skip(from_row) {
            self.assign_fixed(|| "", col, row, || to)?;
        }

        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
    }

    fn pop_namespace(&mut self, _: Option<String>) {}
}

impl<'b, F: Field> Analyzable<F> {
    pub fn ConfigAndSynthesize<ConcreteCircuit: Circuit<F>>(
        circuit: &ConcreteCircuit,
        k: u32,
        //instance: Vec<Vec<F>>,
    ) -> Result<Self, Error> {
        let n = 1 << k;
        let mut cs = ConstraintSystem::default();
        let config = ConcreteCircuit::configure(&mut cs);
        let cs = cs;

        if n < cs.minimum_rows() {
            return Err(Error::not_enough_rows_available(k));
        }

        // Fixed columns contain no blinding factors.
        let fixed = vec![vec![CellValue::Unassigned; n]; cs.num_fixed_columns];
        let selectors = vec![vec![false; n]; cs.num_selectors];
        // Advice columns contain blinding factors.
        let blinding_factors = cs.blinding_factors();
        let usable_rows = n - (blinding_factors + 1);
        let permutation = permutation::keygen::Assembly::new(n, &cs.permutation);
        let constants = cs.constants.clone();

        let mut analyzable = Analyzable {
            k,
            cs,
            regions: vec![],
            current_region: None,
            fixed,
            selectors,
            permutation,
            usable_rows: 0..usable_rows,
        };

        ConcreteCircuit::FloorPlanner::synthesize(&mut analyzable, circuit, config, constants)?;

        let (cs, selector_polys) = analyzable.cs.compress_selectors(analyzable.selectors.clone());
        analyzable.cs = cs;
        analyzable
            .fixed
            .extend(selector_polys.clone().into_iter().map(|poly| {
                let mut v = vec![CellValue::Unassigned; n];
                for (v, p) in v.iter_mut().zip(&poly[..]) {
                    *v = CellValue::Assigned(*p);
                }
                v
            }));

        Ok(analyzable)
    }
}