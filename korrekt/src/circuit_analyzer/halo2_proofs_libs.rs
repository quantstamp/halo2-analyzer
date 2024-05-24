/// ZCASH
#[cfg(feature = "use_zcash_halo2_proofs")]
pub use zcash_halo2_proofs::{
    circuit::{self, AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    dev::{CellValue, Region},
    pasta::Fp as Fr,
    plonk::{
        permutation, Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error,
        Expression, Fixed, FloorPlanner, Instance, Selector,
    },
    poly::Rotation,
};

#[cfg(feature = "use_zcash_halo2_proofs")]
pub use group::ff::Field;

#[cfg(feature = "use_zcash_halo2_proofs")]
pub use halo2curves::bn256;

/// PSE
#[cfg(feature = "use_pse_halo2_proofs")]
pub use pse_halo2_proofs::{
    arithmetic::Field,
    circuit::{self, AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value},
    dev::metadata::Column as ColumnMetadata,
    dev::MockProver,
    dev::{CellValue, Region},
    halo2curves::bn256::Fr,
    plonk::{
        permutation, sealed, sealed::SealedPhase, Advice, Any, Assigned, Assignment, Challenge,
        Circuit, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed, FloorPlanner,
        Instance, Phase, Selector,
    },
    poly::Rotation,
};

#[cfg(feature = "use_pse_halo2_proofs")]
pub use halo2curves::bn256;

#[cfg(feature = "use_pse_v1_halo2_proofs")]
pub use group::Group;
/// PSE V1
#[cfg(feature = "use_pse_v1_halo2_proofs")]
pub use pse_v1_halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{self, AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value},
    dev::metadata::Column as ColumnMetadata,
    dev::MockProver,
    dev::{CellValue, Region},
    halo2curves::bn256::Fr,
    plonk::{
        permutation, Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error,
        Expression, Fixed, FloorPlanner, Instance, Selector, TableColumn,
    },
    poly::Rotation,
};

#[cfg(feature = "use_pse_v1_halo2_proofs")]
pub use halo2curves::bn256;

/// AXIOM
#[cfg(feature = "use_axiom_halo2_proofs")]
pub use axiom_halo2_proofs::{
    arithmetic::Field,
    circuit::{self, AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value},
    dev::metadata::Column as ColumnMetadata,
    dev::MockProver,
    dev::{AdviceCellValue, CellValue, Region},
    halo2curves::bn256::Fr,
    plonk::{
        permutation, sealed, sealed::SealedPhase, Advice, Any, Assigned, Assignment, Challenge,
        Circuit, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed, FloorPlanner,
        Instance, Phase, Selector,
    },
    poly::Rotation,
};

#[cfg(feature = "use_axiom_halo2_proofs")]
pub use halo2curves::bn256;

/// SCROLL
#[cfg(feature = "use_scroll_halo2_proofs")]
pub use scroll_halo2_proofs::{
    arithmetic::Field,
    circuit::{self, Cell, Value},
    dev::metadata::Column as ColumnMetadata,
    dev::MockProver,
    dev::{CellValue, Region},
    halo2curves::bn256::Fr,
    plonk::{
        permutation, sealed, sealed::SealedPhase, Advice, Any, Assigned, Assignment, Challenge,
        Circuit, Column, ConstraintSystem, Error, Expression, FirstPhase, Fixed, FloorPlanner,
        Instance, Phase, Selector,
    },
    poly,
    poly::Rotation,
};

#[cfg(feature = "use_scroll_halo2_proofs")]
pub use halo2curves::bn256;
