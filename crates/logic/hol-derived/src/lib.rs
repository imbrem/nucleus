//! Untrusted derived constructions over the checked HOL kernel.
//!
//! This crate contains traversal, package assembly, and proof orchestration
//! which can be replaced without changing the trusted kernel. Every result is
//! admitted only through public checked [`Kernel`](covalence_logic_hol::Kernel)
//! operations.

mod coproduct;
mod equality;
mod exists;
mod forall;
mod infinity;
mod model;
mod natural;
mod natural_arithmetic;
mod natural_rec;
mod subtype;
mod syntax;

pub use coproduct::{
    Coproduct, CoproductBranch, CoproductCandidate, CoproductCandidateLaws, CoproductCases,
    CoproductComputation, CoproductEliminator, CoproductError, CoproductExhaustiveness,
    CoproductExt, CoproductFixedCodomain, CoproductLaws, CoproductOpenedCases, CoproductSchema,
    CoproductSchemaProof, CoproductUniqueness, CoproductUniversal,
};
pub use equality::{
    EqualityError, ProvedEquality, equality_symmetry, equality_transitivity,
    function_extensionality,
};
pub use exists::{
    ExistsError, OpenedExists, OpenedExistsDecl, introduce_exists, open_exists, open_exists_at,
};
pub use forall::{ForallError, ProvedTerm, forall_elim};
pub use infinity::{
    Infinity, InfinityAxiomDecl, InfinityDecl, InfinityError, InfinityExt, InfinityProof,
};
pub use model::{
    ChosenModel, ChosenModelDecl, ChosenModelProof, ModelError, ModelExt, Substitution,
    eta_expand_at, substitute,
};
pub use natural::{NaturalError, NaturalExt, Naturals, NaturalsDecl, NaturalsProof};
pub use natural_arithmetic::{
    NaturalArithmetic, NaturalArithmeticDecl, NaturalArithmeticExt, NaturalArithmeticProof,
};
pub use natural_rec::{
    NaturalNameSupply, NaturalRecExt, NaturalRecGraph, NaturalRecGraphDecl, NaturalRecGraphProof,
    NaturalRecSchemas, NaturalRecursor, NaturalRecursorDecl, NaturalRecursorProof,
};
pub use subtype::{Subtype, SubtypeAxiomDecl, SubtypeDecl, SubtypeError, SubtypeExt, SubtypeProof};
pub use syntax::{SyntaxError, join_alpha_equivalent, join_alpha_equivalents, join_same_syntax};
