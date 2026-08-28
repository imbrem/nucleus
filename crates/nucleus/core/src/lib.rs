//! Auditable assembly of Nucleus's checked authority surface.
//!
//! Only the checked kernels re-exported here can create trusted facts. Script
//! parsing, namespace metadata, elaboration, automation, and init orchestration
//! live in the untrusted `covalence-nucleus` facade.

/// The Ethane HOL trusted computing base.
pub use covalence_logic_hol as hol;

/// LCF content-addressed facts used by Nucleus.
pub use covalence_logic_cas as cas;

/// Checked descriptors and userspace operations over the HOL kernel.
pub use covalence_logic_hol_derived::{
    ChosenModel, ExistsError, Infinity, InfinityError, InfinityExt, ModelError, ModelExt,
    NaturalError, NaturalExt, Naturals, OpenedExists, Substitution, Subtype, SubtypeError,
    SubtypeExt, open_exists, substitute,
};
