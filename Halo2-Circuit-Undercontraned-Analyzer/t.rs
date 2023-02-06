
       Expression poly Product(Product(Selector(Selector(0, true)), Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) })))

       (Selector(0, true)) * q1c0r0  * (1 - q1c0r0)


       Expression poly Product(Product(Selector(Selector(0, true)), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })))
        
       (Selector(0, true)) * q2c1r0  * (1 -q2c1r0)

       Expression poly Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }, Product(Constant(0x0000000000000000000000000000000000000000000000000000000000000002), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })), Negated(Advice { query_index: 0, column_index: 2, rotation: Rotation(0) })))
       
       (Selector(0, true)) * (((q1c0r0 + (2 * q2c1r0)) - q0c2r0 ))
//-------------------------------------------------------------------------------------------
        S0t * c0 * (1 - c0) = 0 &&// b0 * (1-b0) = 0
        S0t * c1 * (1 - c1) = 0 &&// b1 * (1-b1) = 0
        S0t * (c0 + (2 * c1) - c2) = 0// b0 + 2*b1 - x = 0
//-------------------------------------------------------------------------------------------


= (* s a (+ 1 (- a))) 



AnalyticLayouter {
         regions: [AnalyticalShape { name: "The Region",
                                     region_index: RegionIndex(0), 
                                     selectors: {},
                                     columns: {
                                        (Column(Column { index: 2, column_type: Advice }), Rotation(0)),
                                        (Column(Column { index: 0, column_type: Advice }), Rotation(0)),
                                        (Column(Column { index: 1, column_type: Advice }), Rotation(0)),
                                        (Selector(Selector(0, true)), Rotation(0))},
                                        row_count: 1 }]
         , _ph: PhantomData<pasta_curves::fields::fp::Fp> }



         ConstraintSystem 
         { 
                num_fixed_columns: 0, num_advice_columns: 3, num_instance_columns: 1, num_selectors: 1, selector_map: [], 
                        gates: 
                        [
                                Gate {
                                name: "b0_binary_check", 
                                constraint_names: [""],
                                polys: 
                                [Product(Product(Selector(Selector(0, true)), Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) })))]
                                ,
                                queried_selectors: [Selector(0, true)], queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }] }
                                ,
                                Gate { 
                                        name: "b1_binary_check", constraint_names: [""], 
                                        polys:
                                        [Product(Product(Selector(Selector(0, true)), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })))]
                                        ,
                                        queried_selectors: [Selector(0, true)], queried_cells: [VirtualCell { column: Column { index: 1, column_type: Advice }, rotation: Rotation(0) }] 
                                }
                                ,
                                Gate { name: "equality", constraint_names: [""], polys: [Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }, Product(Constant(0x0000000000000000000000000000000000000000000000000000000000000002), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })), Negated(Advice { query_index: 0, column_index: 2, rotation: Rotation(0) })))]
                                ,
                                queried_selectors: [Selector(0, true)], queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 1, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 2, column_type: Advice }, rotation: Rotation(0) }] }
                         ]
                         , 
                         advice_queries: [(Column { index: 2, column_type: Advice }, Rotation(0)), (Column { index: 0, column_type: Advice }, Rotation(0)), (Column { index: 1, column_type: Advice }, Rotation(0))],
                         num_advice_queries: [1, 1, 1]
                         ,
                         instance_queries: [(Column { index: 0, column_type: Instance }, Rotation(0))]
                         ,
                         fixed_queries: []
                         ,
                         permutation: 
                         Argument { columns: [Column { index: 2, column_type: Advice }, Column { index: 0, column_type: Instance }] }
                         ,
                         lookups: []
                         ,
                         constants: [], minimum_degree: None
         }


         AnalyticLayouter {
                regions: [
                         AnalyticalShape {
                                name: "The Region",
                                region_index: RegionIndex(0), 
                                selectors: {}, 
                                columns: {
                                        (Column(Column { index: 2, column_type: Advice }), Rotation(0)), 
                                        (Column(Column { index: 1, column_type: Advice }), Rotation(0)), 
                                        (Column(Column { index: 0, column_type: Advice }), Rotation(0)), 
                                        (Selector(Selector(0, true)), Rotation(0))}, 
                                row_count: 1 }
                         ]
                , 
                _ph: PhantomData<pasta_curves::fields::fp::Fp>
         }
vars_list:{A2, A0, A1}





ConstraintSystem {
        num_fixed_columns: 0, num_advice_columns: 1, num_instance_columns: 1, num_selectors: 1, selector_map: [],
        gates: [
                Gate {
                        name: "b0_binary_check", 
                        constraint_names: [""], 
                        polys: [Product(Product(Selector(Selector(0, true)), Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 0, column_index: 0, rotation: Rotation(0) })))], 
                        queried_selectors: [Selector(0, true)], 
                        queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }] 
                }, 
                Gate { 
                        name: "b1_binary_check", 
                        constraint_names: [""], 
                        polys: [Product(Product(Selector(Selector(0, true)), Advice { query_index: 1, column_index: 0, rotation: Rotation(1) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 1, column_index: 0, rotation: Rotation(1) })))], 
                        queried_selectors: [Selector(0, true)], 
                        queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(1) }] 
                }, Gate { 
                        name: "equality", 
                        constraint_names: [""], 
                        polys: [Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }, Product(Constant(0x0000000000000000000000000000000000000000000000000000000000000002), Advice { query_index: 1, column_index: 0, rotation: Rotation(1) })), Negated(Advice { query_index: 2, column_index: 0, rotation: Rotation(2) })))], 
                        queried_selectors: [Selector(0, true)], 
                        queried_cells: [VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(0) }, VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(1) }, VirtualCell { column: Column { index: 0, column_type: Advice }, rotation: Rotation(2) }] 
                }
                ], 
                advice_queries: [
                        (Column { 
                                index: 0, 
                                column_type: Advice 
                        }, 
                        Rotation(0)), 
                        (Column { 
                                index: 0, 
                                column_type: Advice 
                        }, 
                        Rotation(1)), 
                        (Column { 
                                index: 0, 
                                column_type: Advice 
                        }, 
                        Rotation(2))
                        ], 
                        num_advice_queries: [3], 
                        instance_queries: [(Column { index: 0, column_type: Instance }, Rotation(0))], 
                        fixed_queries: [], 
                        permutation: Argument { 
                                columns: [Column { index: 0, column_type: Advice }, Column { index: 0, column_type: Instance }] 
                        }, 
                        lookups: [], 
                        constants: [], 
                        minimum_degree: None 
                }


                out
AssignedCell {
         value: Value { inner: None }, 
         cell: Cell { 
                region_index: RegionIndex(0), 
                row_offset: 0, 
                column: Column { index: 2, column_type: Advice } }, 
                _marker: PhantomData<pasta_curves::fields::fp::Fp> 
        }
out
AssignedCell {
         value: Value { inner: Some(0x0000000000000000000000000000000000000000000000000000000000000003) }, 
         cell: Cell { 
                region_index: RegionIndex(0), 
                row_offset: 0, 
                column: Column { index: 2, column_type: Advice } 
        }, 
        _marker: PhantomData<pasta_curves::fields::fp::Fp> 
}



instance:
{|A2-Rotation(0)|}
solver:
(declare-fun |A-1-Rotation(0)| () Int)
(declare-fun |A-2-Rotation(0)| () Int)
(declare-fun |A-0-Rotation(0)| () Int)
(assert (= (* 1 |A-1-Rotation(0)| (+ 1 (- |A-1-Rotation(0)|))) 0))
(assert (= (* 1 |A-1-Rotation(0)| (+ 1 (- |A-1-Rotation(0)|))) 0))
(assert (= (* 1 (+ |A-0-Rotation(0)| (* 2 |A-1-Rotation(0)|) (- |A-2-Rotation(0)|))) 0))

Model to be checked:
A-2-Rotation(0) -> 0
A-1-Rotation(0) -> 0
A-0-Rotation(0) -> 0

equivalent model with same instance column:
A-2-Rotation(0) -> (- 1)
A-0-Rotation(0) -> (- 3)
A-1-Rotation(0) -> 1

The circuit is underConstrained
----------------------Multi Circuit----------------------
instance:
{|A0-Rotation(0)|}
solver:
(declare-fun |A-0-Rotation(0)| () Int)
(declare-fun |A-0-Rotation(1)| () Int)
(declare-fun |A-0-Rotation(2)| () Int)
(assert (= (* 1 |A-0-Rotation(0)| (+ 1 (- |A-0-Rotation(0)|))) 0))
(assert (= (* 1 |A-0-Rotation(1)| (+ 1 (- |A-0-Rotation(1)|))) 0))



AnalyticLayouter { 
        regions: [
                AnalyticalShape { 
                        name: "The Region", 
                        region_index: RegionIndex(0), 
                        selectors: {}, 
                        columns: {
                                (Column(Column {index: 0, column_type: Advice}), Rotation(0)), 
                                (Selector(Selector(0, true)), Rotation(0)), 
                                (Column(Column { index: 0, column_type: Advice }), Rotation(1)), 
                                (Column(Column { index: 0, column_type: Advice }), Rotation(2))
                                }, 
                                row_count: 3 
                        }
                        ], 
                        _ph: PhantomData<pasta_curves::fields::fp::Fp> 
                }
