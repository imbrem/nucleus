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

use crate::Connection;

pub mod namespace;
pub mod rules;
pub mod syntax;
pub mod typing;
mod view;

pub use namespace::ExportTarget;
pub use syntax::{
    HypsId, Ids, Kind, KindId, KindsId, NamespaceId, Sort, SourceId, Substrate, TermId, Tm, Ty,
    TypeId, VarsId,
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
    pub(crate) policy: P,
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

/// Failure to open a kernel-state database from a serialized image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolImageError {
    /// The image bytes could not be serialized or deserialized.
    #[snafu(display("cannot read or write the kernel-state image"), context(false))]
    Image {
        /// Underlying image failure.
        source: covalence_neutron::ImageError,
    },
    /// The schema identity could not be computed.
    #[snafu(display("cannot identify the kernel-state schema"))]
    Identify {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
    /// The image does not carry the current kernel-state schema.
    #[snafu(display("image schema identity {found} is not the expected {expected}"))]
    SchemaMismatch {
        /// The identity of the current kernel-state schema.
        expected: O256,
        /// The identity computed from the image.
        found: O256,
    },
}

impl<P: Policy> Connection<Hol<P>> {
    /// Opens a fresh in-memory kernel-state database under `policy`.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection cannot be opened or the schema
    /// cannot be installed.
    pub fn open_hol_in_memory(policy: P) -> Result<Self, HolOpenError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        neutron
            .sqlite()
            .execute_batch(SCHEMA)
            .context(InstallSnafu)?;
        Ok(Self::from_neutron(neutron, Hol { policy }))
    }

    /// Opens a serialized kernel-state image as a writable in-memory
    /// database under `policy`.
    ///
    /// The image's schema identity is checked against the current
    /// kernel-state schema before the connection is returned. This check
    /// admits the *schema*, never the rows: an image's theorem rows are
    /// trusted exactly as far as the image's provenance (regeneration, or
    /// a pinned content address), so callers establishing trust from a
    /// content hash must verify the bytes before opening them.
    ///
    /// # Errors
    ///
    /// Returns an error if the image cannot be deserialized, its schema
    /// identity cannot be computed, or the identity differs from the
    /// current kernel-state schema.
    pub fn open_hol_image(
        bytes: &covalence_neutron::Bytes,
        policy: P,
    ) -> Result<Self, HolImageError> {
        let neutron = covalence_neutron::Connection::deserialize(bytes)?;
        let connection = Self::from_neutron(neutron, Hol { policy });
        let expected = current_hol_schema_id().context(IdentifySnafu)?;
        let found = {
            let (neutron, _) = connection.parts();
            let physical =
                crate::manifest::schema_manifest_id(neutron.sqlite()).context(IdentifySnafu)?;
            hol_schema_id(physical)
        };
        if found != expected {
            return SchemaMismatchSnafu { expected, found }.fail();
        }
        Ok(connection)
    }

    /// Serializes this connection's database as a whole image.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot serialize the database.
    pub fn serialize_image(&self) -> Result<covalence_neutron::Bytes, HolImageError> {
        let (neutron, _) = self.parts();
        Ok(neutron.serialize()?)
    }

    /// Returns the composite schema identity of this connection's database.
    ///
    /// # Errors
    ///
    /// Returns an error if the physical manifest cannot be read.
    pub fn schema_id(&self) -> Result<O256, HolOpenError> {
        let (neutron, _) = self.parts();
        let physical =
            crate::manifest::schema_manifest_id(neutron.sqlite()).context(InstallSnafu)?;
        Ok(hol_schema_id(physical))
    }
}

/// Computes the schema identity of a fresh kernel-state installation.
fn current_hol_schema_id() -> Result<O256, sqlite::Error> {
    let fresh = sqlite::Connection::open_in_memory()?;
    fresh.execute_batch(SCHEMA)?;
    Ok(hol_schema_id(crate::manifest::schema_manifest_id(&fresh)?))
}

impl crate::Kernel {
    /// Opens a fresh in-memory HOL kernel-state connection under `policy`.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection cannot be opened or the schema
    /// cannot be installed.
    pub fn open_hol<P: Policy>(&self, policy: P) -> Result<Connection<Hol<P>>, HolOpenError> {
        Connection::open_hol_in_memory(policy)
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

    use super::*;

    #[test]
    fn opens_and_installs_the_kernel_state_schema() {
        let connection =
            Connection::open_hol_in_memory(AllowAll).expect("open kernel-state database");
        let (neutron, _) = connection.parts();
        let tables: i64 = neutron
            .sqlite()
            .query_row(
                "SELECT count(*) FROM sqlite_schema WHERE type = 'table'
                 AND name LIKE 'hol_%'",
                (),
                |row| row.get(0),
            )
            .expect("count kernel tables");
        assert_eq!(tables, 5);
    }

    #[test]
    fn schema_identity_is_deterministic_and_schema_sensitive() {
        let first = Connection::open_hol_in_memory(AllowAll).expect("open first");
        let second = Connection::open_hol_in_memory(AllowAll).expect("open second");
        let first_id = first.schema_id().expect("first identity");
        assert_eq!(first_id, second.schema_id().expect("second identity"));

        let (neutron, _) = second.parts();
        neutron
            .sqlite()
            .execute_batch("CREATE TABLE extra (value INTEGER) STRICT")
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
    fn images_round_trip_and_admit_only_the_current_schema() {
        let source = Connection::open_hol_in_memory(AllowAll).expect("open source");
        let truth = {
            let hol = source.view();
            hol.tm(syntax::Tm::Bool(true)).expect("intern true").raw()
        };
        let bytes = source.serialize_image().expect("serialize");

        let restored =
            Connection::<Hol<AllowAll>>::open_hol_image(&bytes, AllowAll).expect("reopen");
        let hol = restored.view();
        let reread = hol.tm_from_raw(truth).expect("revalidate");
        assert_eq!(hol.tm_node(reread).expect("node"), syntax::Tm::Bool(true));

        // A schema extension is a different identity and must be refused.
        let extended = Connection::open_hol_in_memory(AllowAll).expect("open extended");
        extended
            .parts()
            .0
            .sqlite()
            .execute_batch("CREATE TABLE extra (value INTEGER) STRICT")
            .expect("extend schema");
        let extended_bytes = extended.serialize_image().expect("serialize extended");
        assert!(matches!(
            Connection::<Hol<AllowAll>>::open_hol_image(&extended_bytes, AllowAll),
            Err(HolImageError::SchemaMismatch { .. })
        ));
    }

    #[test]
    fn kernel_opens_hol_connections() {
        let kernel = crate::Kernel::ephemeral();
        let connection = kernel.open_hol(AllowAll).expect("open through kernel");
        connection.schema_id().expect("identify");
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
            Connection::open_hol_in_memory(AllowAll)
                .expect("open")
                .schema_id()
                .expect("identify"),
            o256!("2076f97317b93c7d8b4f771a0cb363d71d09d12147c427462eb57317eac122c7")
        );
    }
}
