ConstraintSystem { 
    num_fixed_columns: 3, 
    num_advice_columns: 3, 
    num_instance_columns: 1, 
    num_selectors: 2, 
    selector_map: [], 
    gates: [Gate {
         name: "add", 
         constraint_names: [""], 
         polys: [
            Product(
                Selector(
                    Selector(0, true)), 
                    Sum(
                        Sum(
                            Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }, 
                            Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }
                        ), 
                        Negated(Advice { query_index: 2, column_index: 2, rotation: Rotation(0) })
                    )
                )
        ], 
        queried_selectors: [Selector(0, true)], 
        queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 1, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 2, column_type: Advice }, rotation: Rotation(0) }] 
    }
    ], 
    advice_queries: [
        (Column { index: 0, column_type: Advice }, Rotation(0)), 
        (Column { index: 1, column_type: Advice }, Rotation(0)), 
        (Column { index: 2, column_type: Advice }, Rotation(0))
    ], 
    num_advice_queries: [1, 1, 1], 
    instance_queries: [(Column { index: 0, column_type: Instance }, Rotation(0))], 
    fixed_queries: [
        (Column { index: 0, column_type: Fixed }, Rotation(0)), 
        (Column { index: 1, column_type: Fixed }, Rotation(0)), 
        (Column { index: 2, column_type: Fixed }, Rotation(0))], 
        permutation: Argument { columns: [Column { index: 0, column_type: Advice }, Column { index: 1, column_type: Advice }, Column { index: 2, column_type: Advice }, Column { index: 0, column_type: Instance }] }, 
        lookups: [
            Argument { 
                input_expressions: [
                    Product(Selector(Selector(1, false)), Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }), 
                    Product(Selector(Selector(1, false)), Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }), 
                    Product(Selector(Selector(1, false)), Advice { query_index: 2, column_index: 2, rotation: Rotation(0) })
                ], 
                table_expressions: [Fixed { query_index: 0, column_index: 0, rotation: Rotation(0) }, Fixed { query_index: 1, column_index: 1, rotation: Rotation(0) }, Fixed { query_index: 2, column_index: 2, rotation: Rotation(0) }] }], constants: [], minimum_degree: None }