use halo2_proofs::circuit:: {RegionIndex, Cell, Value};
use halo2_proofs::plonk::{Error, Column, Fixed, Assigned, Selector, Any, Advice, Instance};
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::layouter::{RegionLayouter, RegionColumn};
use halo2_proofs::poly::Rotation;

use std::collections::HashSet;
use std::cmp;

#[derive(Clone, Debug)]
pub struct AnalyticalShape {
    pub name: String,
    pub region_index: RegionIndex,
    pub selectors: HashSet<RegionColumn>,
    pub columns: HashSet<(RegionColumn,  Rotation)>,
    pub row_count: usize,
}

impl AnalyticalShape {
    pub fn new(name: String, index: usize) -> Self {
        AnalyticalShape { 
            region_index: index.into() , 
            columns: HashSet::new(), 
            selectors: HashSet::new(),
            row_count: 0,
            name
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
        self.columns.insert(((*selector).into(), Rotation(offset as i32)));
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
        self.columns.insert((Column::<Any>::from(column).into(), Rotation(offset as i32)));
        self.row_count = cmp::max(self.row_count, offset + 1);

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
        _: &'v (dyn Fn() -> String + 'v),
        _: Column<Instance>,
        _: usize,
        _advice: Column<Advice>,
        _offset: usize,
    ) -> Result<(Cell, Value<F>), Error> {
        //todo!()

        //self.columns.insert(Column::<Any>::from(advice).into());
        self.columns.insert((Column::<Any>::from(_advice).into(), Rotation(_offset as i32)));
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
        self.columns.insert((Column::<Any>::from(column).into(), Rotation(offset as i32)));
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
        Ok(())
    }
}