[AnalyticalShape { name: "first row", region_index: RegionIndex(0), selectors: {}, columns: {(Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-1, selectors: {}, columns: {(Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-2, selectors: {}, columns: {(Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-3, selectors: {}, columns: {(Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-4, selectors: {}, columns: {(Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-5, selectors: {}, columns: {(Column(Column { index: 2, column_type: Advice }), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-6, selectors: {}, columns: {(Column(Column { index: 1, column_type: Advice }), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Column(Column { index: 2, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0))}, row_count: 1 }, AnalyticalShape { name: "next row", region_index: R-7, selectors: {}, columns: {(Column(Column { index: 2, column_type: Advice }), Rotation(0)), (Column(Column { index: 0, column_type: Advice }), Rotation(0)), (Selector(Selector(0, true)), Rotation(0)), (Column(Column { index: 1, column_type: Advice }), Rotation(0))}, row_count: 1 }]


ConstraintSystem { 
    num_fixed_columns: 0, num_advice_columns: 3, num_instance_columns: 1, num_selectors: 1, selector_map: [], gates: 
    [Gate { name: "add", constraint_names: [""], polys: [Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }, Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }), Negated(Advice { query_index: 2, column_index: 2, rotation: Rotation(0) })))], queried_selectors: [Selector(0, true)], queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 1, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 2, column_type: Advice }, rotation: Rotation(0) }] }]
    , advice_queries: 
    [
        (Column { index: 0, column_type: Advice }, Rotation(0)), 
        (Column { index: 1, column_type: Advice }, Rotation(0)), 
        (Column { index: 2, column_type: Advice }, Rotation(0))
    ], num_advice_queries: [1, 1, 1], instance_queries: [(Column { index: 0, column_type: Instance }, Rotation(0))], fixed_queries: [], permutation: Argument { columns: [Column { index: 0, column_type: Advice }, Column { index: 1, column_type: Advice }, Column { index: 2, column_type: Advice }, Column { index: 0, column_type: Instance }] }, lookups: [], constants: [], minimum_degree: None }


("A-R-1-1-0", "A-R-1-2-0")
("A-R-1-0-0", "A-R-1-1-0")
("A-R-2-1-0", "A-R-2-2-0")
("A-R-2-0-0", "A-R-2-2-0")
("A-R-3-0-0", "A-R-3-2-0")
("A-R-3-1-0", "A-R-3-2-0")
("A-R-4-1-0", "A-R-4-2-0")
("A-R-4-0-0", "A-R-4-2-0")
("A-R-5-1-0", "A-R-5-2-0")
("A-R-5-0-0", "A-R-5-2-0")
("A-R-6-1-0", "A-R-6-2-0")
("A-R-6-0-0", "A-R-6-2-0")
("A-R-7-0-0", "A-R-7-2-0")
("A-R-7-1-0", "A-R-7-2-0")

