
       Expression poly Product(Product(Selector(Selector(0, true)), Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) })))

       (Selector(0, true)) * q1c0r0  * (1 - q1c0r0)


       Expression poly Product(Product(Selector(Selector(0, true)), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) }), Sum(Constant(0x0000000000000000000000000000000000000000000000000000000000000001), Negated(Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })))
        
       (Selector(0, true)) * q2c1r0  * (1 -q2c1r0)

       Expression poly Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 1, column_index: 0, rotation: Rotation(0) }, Product(Constant(0x0000000000000000000000000000000000000000000000000000000000000002), Advice { query_index: 2, column_index: 1, rotation: Rotation(0) })), Negated(Advice { query_index: 0, column_index: 2, rotation: Rotation(0) })))
       
       (Selector(0, true)) * (((q1c0r0 + (2 * q2c1r0)) - q0c2r0 ))
//-------------------------------------------------------------------------------------------
        S0t * q1c0r0 * (1 - q1c0r0) = 0 &&// b0 * (1-b0) = 0
        S0t * q2c1r0 * (1 - q2c1r0)// b1 * (1-b1) = 0
        S0t * (q1c0r0 + (2 * q2c1r0) - q0c2r0)// b0 + 2*b1 - c = 0
//-------------------------------------------------------------------------------------------
