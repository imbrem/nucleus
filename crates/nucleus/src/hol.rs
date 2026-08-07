//! HOL-omega kernel-state protocol.
//!
//! [`Hol`] encloses a connection holding exactly the kernel-state schema:
//! one tagged object table for kinds/types/terms/context spines and one
//! theorem table of established judgements, plus the namespace/export
//! layer. The database serializes kernel state, never proof events; see
//! `hol/semantics.txt` for the normative semantic commitment and
//! `hol/schema.sql` for the physical schema. Both are covered by the
//! identity functions [`hol_semantics_id`] and [`hol_schema_id`]: one
//! current schema, no versioned compatibility surface.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::{O256, o256_path};
use covalence_lib_sqlite as sqlite;

pub mod rules;
pub mod syntax;
pub mod typing;
mod view;

pub use syntax::{
    HypsId, Ids, Kind, KindId, KindsId, Sort, SourceId, Substrate, TermId, Tm, Ty, TypeId, VarsId,
};
pub use typing::{Deep, DeepKind, DeepTm, DeepTy, MAX_DEPTH};
pub use view::{HolError, HolView};

/// The normative semantic commitment, byte for byte.
pub const SEMANTICS: &str = include_str!("hol/semantics.txt");

/// The physical schema installed into every kernel-state database.
pub const SCHEMA: &str = include_str!("hol/schema.sql");

/// Operations a connection policy may authorize or refuse.
///
/// One variant per primitive rule plus the syntax/namespace categories.
/// The vocabulary is part of the semantic identity even where the
/// implementation of a rule lands in a later change.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[expect(
    missing_docs,
    reason = "variants name rules specified in semantics.txt"
)]
pub enum Operation {
    InternSyntax,
    ReadSyntax,
    Assume,
    WeakenHyp,
    WeakenVar,
    WeakenKind,
    InstTm,
    InstTy,
    Truth,
    Refl,
    Sym,
    Trans,
    EqMp,
    MkComb,
    Abs,
    TyAbs,
    Beta,
    Eta,
    TyBeta,
    TyEta,
    Choice,
    DeductAntisym,
    AbsRep,
    RepAbs,
    Infinity,
    Export,
    ImportSource,
}

/// Connection-local authorization policy.
///
/// Policies take `&self` so borrowing views can authorize operations;
/// stateful accounting policies use interior mutability.
pub trait Policy {
    /// Returns whether the operation may proceed on this connection.
    fn allows(&self, operation: Operation) -> bool;
}

/// The permissive development policy.
#[derive(Clone, Copy, Debug, Default)]
pub struct AllowAll;

impl Policy for AllowAll {
    fn allows(&self, _operation: Operation) -> bool {
        true
    }
}

/// Protocol state for a HOL kernel-state connection.
pub struct Hol<P: Policy> {
    neutron: covalence_neutron::Connection,
    policy: P,
}

/// Failure to open or identify a kernel-state database.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolOpenError {
    /// The underlying connection could not be created.
    #[snafu(display("cannot open the kernel-state connection"), context(false))]
    Connection {
        /// Underlying connection failure.
        source: covalence_neutron::ConnectionError,
    },
    /// `SQLite` rejected schema installation or an identity query.
    #[snafu(display("cannot install or identify the kernel-state schema"))]
    Install {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}

impl<P: Policy> Hol<P> {
    /// Opens a fresh in-memory kernel-state database under `policy`.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection cannot be opened or the schema
    /// cannot be installed.
    pub fn open_in_memory(policy: P) -> Result<Self, HolOpenError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        sqlite::Statement::execute_batch(neutron.sqlite(), SCHEMA).context(InstallSnafu)?;
        Ok(Self { neutron, policy })
    }

    /// Borrows the underlying `SQLite` connection.
    #[must_use]
    pub fn sqlite(&self) -> &sqlite::Connection {
        self.neutron.sqlite()
    }

    /// Borrows the policy this kernel state was opened under.
    #[must_use]
    pub const fn policy(&self) -> &P {
        &self.policy
    }

    /// Returns the composite schema identity of this connection's database.
    ///
    /// # Errors
    ///
    /// Returns an error if the physical manifest cannot be read.
    pub fn schema_id(&self) -> Result<O256, HolOpenError> {
        let physical = crate::manifest::schema_manifest_id(self.sqlite()).context(InstallSnafu)?;
        Ok(hol_schema_id(physical))
    }
}

/// Returns the identity of the current semantic commitment.
#[must_use]
pub fn hol_semantics_id() -> O256 {
    o256_path!(::nucleus.hol.kernel_state.semantics.v1).tag(SEMANTICS.as_bytes())
}

/// Returns the composite semantic + physical schema identity.
#[must_use]
pub fn hol_schema_id(physical: O256) -> O256 {
    let mut bytes = [0_u8; 64];
    bytes[..32].copy_from_slice(hol_semantics_id().as_bytes());
    bytes[32..].copy_from_slice(physical.as_bytes());
    o256_path!(::nucleus.hol.kernel_state.sqlite_schema.v1).tag(bytes)
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::o256;
    use covalence_neutron::sql;

    use super::*;

    #[test]
    fn opens_and_installs_the_kernel_state_schema() {
        let connection = Hol::open_in_memory(AllowAll).expect("open kernel-state database");
        let tables = sql::query_row(
            connection.sqlite(),
            "SELECT count(*) FROM sqlite_schema WHERE type = 'table' AND name LIKE 'hol_%'",
            &[],
            |row| row.integer(0),
        )
        .expect("count kernel tables");
        assert_eq!(tables, Some(5));
    }

    #[test]
    fn schema_identity_is_deterministic_and_schema_sensitive() {
        let first = Hol::open_in_memory(AllowAll).expect("open first");
        let second = Hol::open_in_memory(AllowAll).expect("open second");
        let first_id = first.schema_id().expect("first identity");
        assert_eq!(first_id, second.schema_id().expect("second identity"));

        sqlite::Statement::execute_batch(
            second.sqlite(),
            "CREATE TABLE extra (value INTEGER) STRICT",
        )
        .expect("extend schema");
        assert_ne!(first_id, second.schema_id().expect("modified identity"));
    }

    #[test]
    fn policy_gates_are_consulted_per_operation() {
        struct DenyAll;
        impl Policy for DenyAll {
            fn allows(&self, _operation: Operation) -> bool {
                false
            }
        }
        assert!(AllowAll.allows(Operation::Beta));
        assert!(!DenyAll.allows(Operation::Beta));
    }

    #[test]
    fn semantics_identity_matches_fixed_vector() {
        // Pinned vector for the version-1 semantics bytes. Any edit to
        // hol/semantics.txt is a new schema identity and must update this
        // vector deliberately.
        assert_eq!(
            hol_semantics_id(),
            o256!("0b66dce1f3f6d950d023c2f8b215bfb9e83465a226eb3519eca3f690b4db020e")
        );
        assert_eq!(
            Hol::open_in_memory(AllowAll)
                .expect("open")
                .schema_id()
                .expect("identify"),
            o256!("2076f97317b93c7d8b4f771a0cb363d71d09d12147c427462eb57317eac122c7")
        );
    }
}
