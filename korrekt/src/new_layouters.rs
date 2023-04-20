// use std::cmp;
// use std::collections::HashMap;
// use std::fmt;
// use std::marker::PhantomData;

// use halo2_proofs::arithmetic::Field;

// use halo2_proofs::{
//     circuit::{
//         layouter::{RegionColumn, RegionLayouter, RegionShape, TableLayouter},
//         Cell, Layouter, Region, RegionIndex, RegionStart, Table, Value,
//     },
//     plonk::{
//         Advice, Any, Assigned, Assignment, Circuit, Column, Error, Fixed, FloorPlanner, Instance,
//         Selector, TableColumn,
//     },
// };

// use crate::shape::AnalyticalShape;

// /// A [`Layouter`] for a single-chip circuit.
// pub struct AnalyticLayouter<'a, F: Field, CS: Assignment<F> + 'a> {
//     cs: &'a mut CS,
//     constants: Vec<Column<Fixed>>,
//     /// Stores the starting row for each region.
//     pub regions: Vec<AnalyticalShape>,
//     /// Stores the first empty row for each column.
//     columns: HashMap<RegionColumn, usize>,
//     /// Stores the table fixed columns.
//     table_columns: Vec<TableColumn>,
//     _marker: PhantomData<F>,


//     pub __regions: Vec<AnalyticalShape>,
//     pub __eq_table: HashMap<String,String>,
// }

// impl<'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for AnalyticLayouter<'a, F, CS> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_struct("AnalyticLayouter")
//             .field("regions", &self.regions)
//             .field("columns", &self.columns)
//             .finish()
//     }
// }

// impl<'a, F: Field, CS: Assignment<F>> AnalyticLayouter<'a, F, CS> {
//     /// Creates a new single-chip layouter.
//     pub fn new(cs: &'a mut CS, constants: Vec<Column<Fixed>>) -> Result<Self, Error> {
//         let ret = AnalyticLayouter {
//             cs,
//             constants,
//             regions: vec![],
//             columns: HashMap::default(),
//             table_columns: vec![],
//             _marker: PhantomData,
//             __regions: vec![],
//             __eq_table: HashMap::new(),
//         };
//         Ok(ret)
//     }
// }

// impl<'a, F: Field, CS: Assignment<F> + 'a> Layouter<F> for AnalyticLayouter<'a, F, CS> {
//     type Root = Self;

//     fn assign_region<A, AR, N, NR>(&mut self, name: N, mut assignment: A) -> Result<AR, Error>
//     where
//         A: FnMut(Region<'_, F>) -> Result<AR, Error>,
//         N: Fn() -> NR,
//         NR: Into<String>,
//     {
//         let region_index = self.regions.len();

//         let mut shape: AnalyticalShape = AnalyticalShape::new(name().into(), region_index.into());

//         let region: &mut dyn RegionLayouter<F> = &mut shape;
//         let result = assignment(region.into())?;
//         let a  = assignment;

//         // save region

//         self.regions.push(shape);
//         println!("assignment\n: {:?}",self.regions);

//         Ok(result)
//     }

//     fn assign_table<A, N, NR>(&mut self, name: N, mut assignment: A) -> Result<(), Error>
//     where
//         A: FnMut(Table<'_, F>) -> Result<(), Error>,
//         N: Fn() -> NR,
//         NR: Into<String>,
//     {
//         // Maintenance hazard: there is near-duplicate code in `v1::AssignmentPass::assign_table`.
//         // Assign table cells.
//         self.cs.enter_region(name);
//         let mut table = SimpleTableLayouter::new(self.cs, &self.table_columns);
//         {
//             let table: &mut dyn TableLayouter<F> = &mut table;
//             assignment(table.into())
//         }?;
//         let default_and_assigned = table.default_and_assigned;
//         self.cs.exit_region();

//         // Check that all table columns have the same length `first_unused`,
//         // and all cells up to that length are assigned.
//         let first_unused = {
//             match default_and_assigned
//                 .values()
//                 .map(|(_, assigned)| {
//                     if assigned.iter().all(|b| *b) {
//                         Some(assigned.len())
//                     } else {
//                         None
//                     }
//                 })
//                 .reduce(|acc, item| match (acc, item) {
//                     (Some(a), Some(b)) if a == b => Some(a),
//                     _ => None,
//                 }) {
//                 Some(Some(len)) => len,
//                 _ => return Err(Error::Synthesis), // TODO better error
//             }
//         };

//         // Record these columns so that we can prevent them from being used again.
//         for column in default_and_assigned.keys() {
//             self.table_columns.push(*column);
//         }

//         for (col, (default_val, _)) in default_and_assigned {
//             // default_val must be Some because we must have assigned
//             // at least one cell in each column, and in that case we checked
//             // that all cells up to first_unused were assigned.
//             self.cs
//                 .fill_from_row(col.inner(), first_unused, default_val.unwrap())?;
//         }

//         Ok(())
//     }

//     fn constrain_instance(
//         &mut self,
//         _cell: Cell,
//         _column: Column<Instance>,
//         _row: usize,
//     ) -> Result<(), Error> {

//         let left = format!("A-{}-{:?}", _cell.column.index(),_cell.row_offset);

//         let right = format!("A-{}-{:?}", _column.index(),_row);

//         self.__eq_table.insert(left,right);
//         Ok(())
//     }

//     fn get_root(&mut self) -> &mut Self::Root {
//         self
//     }

//     fn push_namespace<NR, N>(&mut self, name_fn: N)
//     where
//         NR: Into<String>,
//         N: FnOnce() -> NR,
//     {
//         self.cs.push_namespace(name_fn)
//     }

//     fn pop_namespace(&mut self, gadget_name: Option<String>) {
//         self.cs.pop_namespace(gadget_name)
//     }
// }

// struct AnalyticLayouterRegion<'r, 'a, F: Field, CS: Assignment<F> + 'a> {
//     layouter: &'r mut AnalyticLayouter<'a, F, CS>,
//     region_index: RegionIndex,
//     /// Stores the constants to be assigned, and the cells to which they are copied.
//     constants: Vec<(Assigned<F>, Cell)>,


//     pub __advice_eq_table: HashMap<String,String>

// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug
//     for AnalyticLayouterRegion<'r, 'a, F, CS>
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_struct("AnalyticLayouterRegion")
//             .field("layouter", &self.layouter)
//             .field("region_index", &self.region_index)
//             .finish()
//     }
// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> AnalyticLayouterRegion<'r, 'a, F, CS> {
//     fn new(layouter: &'r mut AnalyticLayouter<'a, F, CS>, region_index: RegionIndex) -> Self {
//         AnalyticLayouterRegion {
//             layouter,
//             region_index,
//             constants: vec![],
//             __advice_eq_table: HashMap::new(),
//         }
//     }
// }



// /// The default value to fill a table column with.
// ///
// /// - The outer `Option` tracks whether the value in row 0 of the table column has been
// ///   assigned yet. This will always be `Some` once a valid table has been completely
// ///   assigned.
// /// - The inner `Value` tracks whether the underlying `Assignment` is evaluating
// ///   witnesses or not.
// type DefaultTableValue<F> = Option<Value<Assigned<F>>>;

// pub(crate) struct SimpleTableLayouter<'r, 'a, F: Field, CS: Assignment<F> + 'a> {
//     cs: &'a mut CS,
//     used_columns: &'r [TableColumn],
//     // maps from a fixed column to a pair (default value, vector saying which rows are assigned)
//     pub(crate) default_and_assigned: HashMap<TableColumn, (DefaultTableValue<F>, Vec<bool>)>,
// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> fmt::Debug for SimpleTableLayouter<'r, 'a, F, CS> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_struct("SimpleTableLayouter")
//             .field("used_columns", &self.used_columns)
//             .field("default_and_assigned", &self.default_and_assigned)
//             .finish()
//     }
// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> SimpleTableLayouter<'r, 'a, F, CS> {
//     pub(crate) fn new(cs: &'a mut CS, used_columns: &'r [TableColumn]) -> Self {
//         SimpleTableLayouter {
//             cs,
//             used_columns,
//             default_and_assigned: HashMap::default(),
//         }
//     }
// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> TableLayouter<F>
//     for SimpleTableLayouter<'r, 'a, F, CS>
// {
//     fn assign_cell<'v>(
//         &'v mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         column: TableColumn,
//         offset: usize,
//         to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
//     ) -> Result<(), Error> {
//         if self.used_columns.contains(&column) {
//             return Err(Error::Synthesis); // TODO better error
//         }

//         let entry = self.default_and_assigned.entry(column).or_default();

//         let mut value = Value::unknown();
//         self.cs.assign_fixed(
//             annotation,
//             column.inner(),
//             offset, // tables are always assigned starting at row 0
//             || {
//                 let res = to();
//                 value = res;
//                 res
//             },
//         )?;

//         match (entry.0.is_none(), offset) {
//             // Use the value at offset 0 as the default value for this table column.
//             (true, 0) => entry.0 = Some(value),
//             // Since there is already an existing default value for this table column,
//             // the caller should not be attempting to assign another value at offset 0.
//             (false, 0) => return Err(Error::Synthesis), // TODO better error
//             _ => (),
//         }
//         if entry.1.len() <= offset {
//             entry.1.resize(offset + 1, false);
//         }
//         entry.1[offset] = true;

//         Ok(())
//     }
// }

// impl<'r, 'a, F: Field, CS: Assignment<F> + 'a> RegionLayouter<F>
//     for AnalyticLayouterRegion<'r, 'a, F, CS>
// {
//     fn enable_selector<'v>(
//         &'v mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         selector: &Selector,
//         offset: usize,
//     ) -> Result<(), Error> {
//         // Track the selector's fixed column as part of the region's shape.
//         self.columns.insert(((*selector).into(), Rotation(offset as i32)));
//         self.row_count = cmp::max(self.row_count, offset + 1);
//         Ok(())
//     }

//     fn assign_advice<'v>(
//         &'v mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         column: Column<Advice>,
//         offset: usize,
//         to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
//     ) -> Result<Cell, Error> {
//         self.layouter.cs.assign_advice(
//             annotation,
//             column,
//             *self.layouter.regions[*self.region_index] + offset,
//             to,
//         )?;

//         Ok(Cell {
//             region_index: self.region_index,
//             row_offset: offset,
//             column: column.into(),
//         })
//     }

//     fn assign_advice_from_constant<'v>(
//         &'v mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         column: Column<Advice>,
//         offset: usize,
//         constant: Assigned<F>,
//     ) -> Result<Cell, Error> {
//         let advice =
//             self.assign_advice(annotation, column, offset, &mut || Value::known(constant))?;
//         self.constrain_constant(advice, constant)?;

//         Ok(advice)
//     }

//     fn assign_advice_from_instance<'v>(
//         &mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         instance: Column<Instance>,
//         row: usize,
//         advice: Column<Advice>,
//         offset: usize,
//     ) -> Result<(Cell, Value<F>), Error> {
//         let value = self.layouter.cs.query_instance(instance, row)?;

//         let cell = self.assign_advice(annotation, advice, offset, &mut || value.to_field())?;

//         self.layouter.cs.copy(
//             cell.column,
//             *self.layouter.regions[*cell.region_index] + cell.row_offset,
//             instance.into(),
//             row,
//         )?;

//         Ok((cell, value))
//     }

//     fn assign_fixed<'v>(
//         &'v mut self,
//         annotation: &'v (dyn Fn() -> String + 'v),
//         column: Column<Fixed>,
//         offset: usize,
//         to: &'v mut (dyn FnMut() -> Value<Assigned<F>> + 'v),
//     ) -> Result<Cell, Error> {
//         self.layouter.cs.assign_fixed(
//             annotation,
//             column,
//             *self.layouter.regions[*self.region_index] + offset,
//             to,
//         )?;

//         Ok(Cell {
//             region_index: self.region_index,
//             row_offset: offset,
//             column: column.into(),
//         })
//     }

//     fn constrain_constant(&mut self, cell: Cell, constant: Assigned<F>) -> Result<(), Error> {
//         self.constants.push((constant, cell));
//         Ok(())
//     }

//     fn constrain_equal(&mut self, left: Cell, right: Cell) -> Result<(), Error> {
//         let left_name = format!("A-{}-{:?}", left.column.index(),left.row_offset);

//         let right_name = format!("A-{}-{:?}", right.column.index(),right.row_offset);

//         self.__advice_eq_table.insert(left_name,right_name);

//         self.layouter.cs.copy(
//             left.column,
//             *self.layouter.regions[*left.region_index] + left.row_offset,
//             right.column,
//             *self.layouter.regions[*right.region_index] + right.row_offset,
//         )?;

//         Ok(())
//     }
// }