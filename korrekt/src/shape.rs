use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::layouter::{RegionColumn, RegionLayouter};
use halo2_proofs::circuit::{Cell, RegionIndex, Value};
use halo2_proofs::plonk::{Advice, Any, Assigned, Column, Error, Fixed, Instance, Selector};
use halo2_proofs::poly::Rotation;

use std::cmp;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct AnalyticalShape {
    pub name: String,
    pub region_index: RegionIndex,
    pub selectors: HashSet<RegionColumn>,
    pub columns: HashSet<(RegionColumn, Rotation)>,
    pub row_count: usize,

    pub __enabled_selectors: HashSet<String>,

    pub __advice_eq_table: HashMap<String, String>,
    pub __eq_table: HashMap<String, String>,
}

impl AnalyticalShape {
    pub fn new(name: String, index: usize) -> Self {
        AnalyticalShape {
            region_index: index.into(),
            columns: HashSet::new(),
            selectors: HashSet::new(),
            row_count: 0,
            name,
            __enabled_selectors: HashSet::new(),
            __advice_eq_table: HashMap::new(),
            __eq_table: HashMap::new(),
        }
    }

    pub fn selectors(&self) -> Vec<Selector> {
        let mut selectors = vec![];
        for (column, _rotation) in self.columns.iter() {
            match column {
                RegionColumn::Column(_) => (),
                RegionColumn::Selector(selector) => selectors.push(selector.clone()),
            }
        }
        selectors
    }
}

impl<F: Field> RegionLayouter<F> for AnalyticalShape {
    fn enable_selector<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        selector: &Selector,
        offset: usize,
    ) -> Result<(), Error> {
        // Track the selector's fixed column as part of the region's shape.
        self.__enabled_selectors.insert(format!(
            "S-{:?}-{}-{}",
            self.region_index.0,
            i32::try_from(selector.0.clone()).ok().unwrap(),
            i32::try_from(offset).ok().unwrap()
        ));
        self.columns
            .insert(((*selector).into(), Rotation(offset as i32)));
        self.row_count = cmp::max(self.row_count, offset + 1);
        Ok(())
    }

    fn assign_advice<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        _to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.columns
            .insert((Column::<Any>::from(column).into(), Rotation(offset as i32)));
        self.row_count = cmp::max(self.row_count, offset + 1);

       //let mut value = Value::unknown();
       let _c =column;
    //    let _vv = {
    //                 let v = _to();
    //                 let value_f = v.to_field();
    //                 value = v;
    //                 value_f
    //             };

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn assign_advice_from_constant<'v>(
        &'v mut self,
        annotation: &'v (dyn Fn() -> String + 'v),
        column: Column<Advice>,
        offset: usize,
        constant: Assigned<F>,
    ) -> Result<Cell, Error> {
        // The rest is identical to witnessing an advice cell.
        self.assign_advice(annotation, column, offset, &mut || Value::known(constant))
    }

    fn assign_advice_from_instance<'v>(
        &mut self,
        _annotation: &'v (dyn Fn() -> String + 'v),
        _instance: Column<Instance>,
        _row: usize,
        _advice: Column<Advice>,
        _offset: usize,
    ) -> Result<(Cell, Value<F>), Error> {
        //todo!()
        let left = format!(
            "I-{:?}-{}-{:?}",
            self.region_index.0,
            _instance.index(),
            _row
        );

        let right = format!(
            "A-{:?}-{}-{:?}",
            self.region_index.0,
            _advice.index(),
            _offset
        );

        self.__eq_table.insert(left, right);
        //self.columns.insert(Column::<Any>::from(advice).into());
        self.columns.insert((
            Column::<Any>::from(_advice).into(),
            Rotation(_offset as i32),
        ));
        self.row_count = cmp::max(self.row_count, _offset + 1);

        Ok((
            Cell {
                region_index: self.region_index,
                row_offset: _offset,
                column: _advice.into(),
            },
            Value::unknown(),
        ))
    }

    fn assign_fixed<'v>(
        &'v mut self,
        _: &'v (dyn Fn() -> String + 'v),
        column: Column<Fixed>,
        offset: usize,
        _to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
    ) -> Result<Cell, Error> {
        self.columns
            .insert((Column::<Any>::from(column).into(), Rotation(offset as i32)));
        self.row_count = cmp::max(self.row_count, offset + 1);

        Ok(Cell {
            region_index: self.region_index,
            row_offset: offset,
            column: column.into(),
        })
    }

    fn constrain_constant(&mut self, _cell: Cell, _constant: Assigned<F>) -> Result<(), Error> {
        // Global constants don't affect the region shape.
        Ok(())
    }

    fn constrain_equal(&mut self, _left: Cell, _right: Cell) -> Result<(), Error> {
        // Equality constraints don't affect the region shape.

        let left_name = format!(
            "A-{:?}-{}-{:?}",
            _left.region_index.0,
            _left.column.index(),
            _left.row_offset
        );

        let right_name = format!(
            "A-{:?}-{}-{:?}",
            _right.region_index.0,
            _right.column.index(),
            _right.row_offset
        );

        self.__advice_eq_table.insert(left_name, right_name);
        Ok(())
    }
}
