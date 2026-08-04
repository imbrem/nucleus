//! Transport-neutral control-plane contract for one Covalence kernel.
//!
//! This crate is deliberately above Nucleus. It describes routing, resource bounds, and owned
//! service values, but grants no logical authority and does not define a [`nucleus::Connection`]
//! protocol. A service's public key is an observed identity; consumers still decide what to trust.
//!
//! [`nucleus::Connection`]: https://docs.rs/covalence-nucleus/latest/covalence_nucleus/struct.Connection.html

use std::{error::Error as StdError, fmt};

use covalence_lib_hash::O256;

pub mod rpc;
pub mod wire;

/// Checked-in WIT source which normatively describes the typed service surface.
pub const CONTRACT_WIT: &str = include_str!("../wit/kernel-service.wit");

/// Maximum complete immutable image accepted by one call.
pub const MAX_IMAGE_BYTES: usize = 64 << 20;
/// Maximum UTF-8 `SQLite` statement accepted by one call.
pub const MAX_SQL_BYTES: usize = 1 << 20;
/// Maximum logical owned SQL outcome returned by one call.
///
/// The metric counts sequence lengths, UTF-8 text and blob bytes, and fixed-width scalars. It is
/// independent of any future transport encoding.
pub const MAX_SQL_OUTCOME_BYTES: usize = 16 << 20;
/// Maximum UTF-8 `SQLite` diagnostic carried by one failed statement.
pub const MAX_SQL_DIAGNOSTIC_BYTES: usize = 4 << 10;
/// Maximum image addresses returned by one listing.
pub const MAX_LISTED_IMAGES: usize = 1024;

const OPERATION_CONTRACT_DOMAIN: &[u8] = b"covalence/kernel-service/operation-contract/v0\0";
const OPERATION_SCHEMA_DOMAIN: &[u8] = b"covalence/kernel-service/operation-schema/v0\0";

/// One operation in the checked-in typed service contract.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Operation {
    /// Read observed kernel identity and supported operation contracts.
    Identity,
    /// Test whether an immutable image is resident.
    HasImage,
    /// List bounded resident image addresses.
    ListImages,
    /// Upload one complete immutable image.
    PutImage,
    /// Open one raw in-memory `SQLite` connection.
    OpenSql,
    /// Execute one `SQLite` statement.
    RunSql,
    /// Attach one resident image immutably.
    AttachImage,
    /// Close one raw `SQLite` connection.
    CloseSql,
    /// Serialize one raw connection's writable `main` database as a bounded complete image.
    SerializeSqlMain,
}

impl Operation {
    /// Stable wire tag committed by the checked-in WIT contract.
    #[must_use]
    pub const fn tag(self) -> u8 {
        match self {
            Self::Identity => 0,
            Self::HasImage => 1,
            Self::ListImages => 2,
            Self::PutImage => 3,
            Self::OpenSql => 4,
            Self::RunSql => 5,
            Self::AttachImage => 6,
            Self::CloseSql => 7,
            Self::SerializeSqlMain => 8,
        }
    }

    /// Every operation in canonical identity order.
    pub const ALL: [Self; 9] = [
        Self::Identity,
        Self::HasImage,
        Self::ListImages,
        Self::PutImage,
        Self::OpenSql,
        Self::RunSql,
        Self::AttachImage,
        Self::CloseSql,
        Self::SerializeSqlMain,
    ];
}

/// O256 identifier of the exact checked-in WIT contract bytes.
#[must_use]
pub fn contract_id() -> O256 {
    O256::from_bytes(CONTRACT_WIT.as_bytes())
}

/// Derives one operation contract identifier from the exact contract and stable operation tag.
///
/// This identifies a typed service method. It is deliberately not the semantic schema used to
/// sign a claim relating canonical input and output values; that belongs to the signed wire layer.
#[must_use]
pub fn operation_contract(operation: Operation) -> O256 {
    let contract = contract_id();
    let mut statement = Vec::with_capacity(OPERATION_CONTRACT_DOMAIN.len() + 33);
    statement.extend_from_slice(OPERATION_CONTRACT_DOMAIN);
    statement.extend_from_slice(contract.as_ref());
    statement.push(operation.tag());
    O256::from_bytes(&statement)
}

/// Derives the semantic schema for a canonical operation input/result relation.
///
/// The relation accepts the canonical request and response encodings for `operation`; value IDs
/// are direction-separated hashes beneath this schema. This is deliberately distinct from the
/// typed WIT contract identifier so signatures state both which operation ran and how its values
/// are named.
#[must_use]
pub fn operation_schema(operation: Operation) -> O256 {
    let contract = contract_id();
    let mut statement = Vec::with_capacity(OPERATION_SCHEMA_DOMAIN.len() + 33);
    statement.extend_from_slice(OPERATION_SCHEMA_DOMAIN);
    statement.extend_from_slice(contract.as_ref());
    statement.push(operation.tag());
    O256::from_bytes(&statement)
}

/// One operation and its exact typed-contract identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OperationContract {
    /// Typed operation.
    pub operation: Operation,
    /// Identifier derived from the checked-in WIT and operation tag.
    pub contract: O256,
}

/// Observed identity and advertised service surface of one kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KernelIdentity {
    /// Ephemeral Ed25519 verification key. Observation does not imply trust.
    pub public_key: [u8; 32],
    /// Canonically ordered operations supported by this endpoint.
    pub operations: Vec<OperationContract>,
}

impl KernelIdentity {
    /// Describes a kernel implementing every operation in this contract.
    #[must_use]
    pub fn complete(public_key: [u8; 32]) -> Self {
        Self {
            public_key,
            operations: Operation::ALL
                .into_iter()
                .map(|operation| OperationContract {
                    operation,
                    contract: operation_contract(operation),
                })
                .collect(),
        }
    }
}

/// Bounded complete immutable-image bytes admitted by [`KernelService::put_image`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImageBytes(Vec<u8>);

impl ImageBytes {
    /// Checks the per-call image limit without interpreting the bytes.
    ///
    /// # Errors
    ///
    /// Returns [`ServiceError::ResourceLimit`] when `bytes` exceeds [`MAX_IMAGE_BYTES`].
    pub fn new(bytes: Vec<u8>) -> Result<Self, ServiceError> {
        if bytes.len() > MAX_IMAGE_BYTES {
            return Err(ServiceError::ResourceLimit);
        }
        Ok(Self(bytes))
    }

    /// Returns the exact uninterpreted bytes.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    /// Consumes the wrapper without copying.
    #[must_use]
    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }
}

/// Bounded UTF-8 `SQLite` statement admitted by [`KernelService::run_sql`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SqlStatement(String);

impl SqlStatement {
    /// Checks the exact UTF-8 byte limit.
    ///
    /// # Errors
    ///
    /// Returns [`ServiceError::ResourceLimit`] when `statement` exceeds [`MAX_SQL_BYTES`].
    pub fn new(statement: String) -> Result<Self, ServiceError> {
        if statement.len() > MAX_SQL_BYTES {
            return Err(ServiceError::ResourceLimit);
        }
        Ok(Self(statement))
    }

    /// Returns the exact statement.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Opaque kernel-local raw `SQLite` connection handle.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SqlConnectionId(u64);

impl SqlConnectionId {
    /// Wraps a service-local integer allocated by a kernel implementation.
    #[must_use]
    pub const fn from_u64(value: u64) -> Self {
        Self(value)
    }

    /// Returns the service-local integer for transport encoding.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// Owned `SQLite` value crossing a service boundary.
#[derive(Clone, Debug, PartialEq)]
pub enum SqlValue {
    /// SQL NULL.
    Null,
    /// Signed 64-bit integer.
    Integer(i64),
    /// IEEE-754 binary64 value.
    Real(f64),
    /// UTF-8 text.
    Text(String),
    /// Arbitrary bytes.
    Blob(Vec<u8>),
}

/// Kind of owned result returned by one raw `SQLite` statement.
#[derive(Clone, Debug, PartialEq)]
pub enum SqlOutcomeKind {
    /// Number of rows changed by a non-query statement.
    Changed(u64),
    /// Column names and rows in `SQLite` result order.
    Rows {
        /// Column names, including duplicates.
        columns: Vec<String>,
        /// Values in row-major order.
        rows: Vec<Vec<SqlValue>>,
    },
}

/// Bounded owned result of one raw `SQLite` statement.
#[derive(Clone, Debug, PartialEq)]
pub struct SqlOutcome {
    kind: SqlOutcomeKind,
}

impl SqlOutcome {
    /// Constructs a fixed-width changed-row count.
    #[must_use]
    pub const fn changed(count: u64) -> Self {
        Self {
            kind: SqlOutcomeKind::Changed(count),
        }
    }

    /// Checks row widths and the documented logical output-size bound.
    ///
    /// # Errors
    ///
    /// Returns [`ServiceError::InvalidRequest`] when a row width differs from the column count,
    /// or [`ServiceError::ResourceLimit`] when the logical size exceeds
    /// [`MAX_SQL_OUTCOME_BYTES`].
    pub fn rows(columns: Vec<String>, rows: Vec<Vec<SqlValue>>) -> Result<Self, ServiceError> {
        if rows.iter().any(|row| row.len() != columns.len()) {
            return Err(ServiceError::InvalidRequest);
        }
        let kind = SqlOutcomeKind::Rows { columns, rows };
        if logical_outcome_size(&kind).is_none_or(|size| size > MAX_SQL_OUTCOME_BYTES) {
            return Err(ServiceError::ResourceLimit);
        }
        Ok(Self { kind })
    }

    /// Borrows the checked outcome kind.
    #[must_use]
    pub const fn kind(&self) -> &SqlOutcomeKind {
        &self.kind
    }

    /// Consumes the checked wrapper.
    #[must_use]
    pub fn into_kind(self) -> SqlOutcomeKind {
        self.kind
    }
}

fn logical_outcome_size(kind: &SqlOutcomeKind) -> Option<usize> {
    const LENGTH_BYTES: usize = size_of::<u64>();
    const TAG_BYTES: usize = 1;

    match kind {
        SqlOutcomeKind::Changed(_) => Some(TAG_BYTES + size_of::<u64>()),
        SqlOutcomeKind::Rows { columns, rows } => {
            let mut size = TAG_BYTES.checked_add(LENGTH_BYTES.checked_mul(2)?)?;
            for column in columns {
                size = size.checked_add(LENGTH_BYTES.checked_add(column.len())?)?;
            }
            for row in rows {
                size = size.checked_add(LENGTH_BYTES)?;
                for value in row {
                    let value_size = match value {
                        SqlValue::Null => TAG_BYTES,
                        SqlValue::Integer(_) | SqlValue::Real(_) => TAG_BYTES + size_of::<u64>(),
                        SqlValue::Text(value) => TAG_BYTES
                            .checked_add(LENGTH_BYTES)?
                            .checked_add(value.len())?,
                        SqlValue::Blob(value) => TAG_BYTES
                            .checked_add(LENGTH_BYTES)?
                            .checked_add(value.len())?,
                    };
                    size = size.checked_add(value_size)?;
                }
            }
            Some(size)
        }
    }
}

/// Transport-neutral service failure class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ServiceError {
    /// Request shape or value was invalid.
    InvalidRequest,
    /// Address or handle was unknown.
    NotFound,
    /// A documented resource bound was exceeded.
    ResourceLimit,
    /// The selected operation or live handle had the wrong protocol.
    Protocol,
    /// The implementation failed without a safe portable classification.
    Internal,
}

impl fmt::Display for ServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::InvalidRequest => "invalid kernel-service request",
            Self::NotFound => "kernel-service resource not found",
            Self::ResourceLimit => "kernel-service resource limit exceeded",
            Self::Protocol => "kernel-service protocol mismatch",
            Self::Internal => "kernel-service internal failure",
        })
    }
}

impl StdError for ServiceError {}

/// Bounded `SQLite` diagnostic preserved across a kernel-service boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SqlDiagnostic {
    primary_code: i32,
    extended_code: i32,
    message: String,
}

impl SqlDiagnostic {
    /// Creates a diagnostic while truncating its UTF-8 message to the portable bound.
    #[must_use]
    pub fn new(primary_code: i32, extended_code: i32, mut message: String) -> Self {
        if message.len() > MAX_SQL_DIAGNOSTIC_BYTES {
            let mut end = MAX_SQL_DIAGNOSTIC_BYTES;
            while !message.is_char_boundary(end) {
                end -= 1;
            }
            message.truncate(end);
        }
        Self {
            primary_code,
            extended_code,
            message,
        }
    }

    /// `SQLite` primary result code, or zero when unavailable.
    #[must_use]
    pub const fn primary_code(&self) -> i32 {
        self.primary_code
    }

    /// `SQLite` extended result code, or zero when unavailable.
    #[must_use]
    pub const fn extended_code(&self) -> i32 {
        self.extended_code
    }

    /// Bounded human-readable `SQLite` diagnostic.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for SqlDiagnostic {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.message.fmt(formatter)
    }
}

impl StdError for SqlDiagnostic {}

/// Failure specific to executing raw `SQLite` through the portable service.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SqlRunError {
    /// Portable routing, ownership, or resource failure.
    Service(ServiceError),
    /// Bounded diagnostic produced by `SQLite` itself.
    Sqlite(SqlDiagnostic),
}

impl From<ServiceError> for SqlRunError {
    fn from(error: ServiceError) -> Self {
        Self::Service(error)
    }
}

impl fmt::Display for SqlRunError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Service(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for SqlRunError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Service(error) => Some(error),
            Self::Sqlite(error) => Some(error),
        }
    }
}

/// Minimal typed service implemented by a local, Worker, HTTP, or WebSocket kernel endpoint.
///
/// This trait is a control-plane wrapper. It does not bypass `Connection<P>` and must not infer
/// protocol trust from transport authentication or from [`KernelIdentity`].
pub trait KernelService {
    /// Returns observed identity and supported operation contracts.
    ///
    /// # Errors
    ///
    /// Returns a classified service error when identity cannot be reported safely.
    fn identity(&self) -> Result<KernelIdentity, ServiceError>;

    /// Reports operational image residence without validating or trusting the bytes.
    ///
    /// # Errors
    ///
    /// Returns a classified service error for an invalid address or implementation failure.
    fn has_image(&self, image: O256) -> Result<bool, ServiceError>;

    /// Lists at most [`MAX_LISTED_IMAGES`] operational image addresses.
    ///
    /// # Errors
    ///
    /// Returns a classified service error when the bounded listing cannot be produced.
    fn list_images(&self) -> Result<Vec<O256>, ServiceError>;

    /// Admits one bounded, uninterpreted complete image.
    ///
    /// # Errors
    ///
    /// Returns a classified service error when admission or storage fails.
    fn put_image(&mut self, bytes: ImageBytes) -> Result<O256, ServiceError>;

    /// Opens one unrestricted in-memory `SQLite` connection.
    ///
    /// # Errors
    ///
    /// Returns a classified service error when the handle cannot be opened.
    fn open_sql(&mut self) -> Result<SqlConnectionId, ServiceError>;

    /// Runs one bounded `SQLite` statement on a caller-owned handle.
    ///
    /// # Errors
    ///
    /// Returns a classified service error for an unknown handle, invalid statement, bounded
    /// output failure, or implementation error.
    fn run_sql(
        &mut self,
        connection: SqlConnectionId,
        statement: SqlStatement,
    ) -> Result<SqlOutcome, SqlRunError>;

    /// Attaches one resident image immutably under `schema`.
    ///
    /// # Errors
    ///
    /// Returns a classified service error for an unknown handle/image, invalid schema, failed
    /// immutable mount, or implementation error.
    fn attach_image(
        &mut self,
        connection: SqlConnectionId,
        image: O256,
        schema: &str,
    ) -> Result<(), ServiceError>;

    /// Serializes a caller-owned raw connection's writable `main` database.
    ///
    /// # Errors
    ///
    /// Returns a classified service error for an unknown handle, serialization failure, or an
    /// image exceeding [`MAX_IMAGE_BYTES`].
    fn serialize_sql_main(
        &mut self,
        connection: SqlConnectionId,
    ) -> Result<ImageBytes, ServiceError>;

    /// Closes one caller-owned raw `SQLite` handle.
    ///
    /// # Errors
    ///
    /// Returns a classified service error for an unknown handle or implementation failure.
    fn close_sql(&mut self, connection: SqlConnectionId) -> Result<(), ServiceError>;
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn complete_identity_advertises_distinct_contract_bound_operations() {
        let identity = KernelIdentity::complete([7; 32]);
        assert_eq!(identity.operations.len(), Operation::ALL.len());
        let contracts = identity
            .operations
            .iter()
            .map(|operation| operation.contract)
            .collect::<HashSet<_>>();
        assert_eq!(contracts.len(), Operation::ALL.len());
        for (expected, advertised) in Operation::ALL.iter().zip(&identity.operations) {
            assert_eq!(advertised.operation, *expected);
            assert_eq!(advertised.contract, operation_contract(*expected));
        }
    }

    #[test]
    fn input_wrappers_enforce_exact_boundaries() {
        assert!(ImageBytes::new(vec![0; MAX_IMAGE_BYTES]).is_ok());
        assert_eq!(
            ImageBytes::new(vec![0; MAX_IMAGE_BYTES + 1]),
            Err(ServiceError::ResourceLimit)
        );
        assert!(SqlStatement::new("x".repeat(MAX_SQL_BYTES)).is_ok());
        assert_eq!(
            SqlStatement::new("x".repeat(MAX_SQL_BYTES + 1)),
            Err(ServiceError::ResourceLimit)
        );
    }

    #[test]
    fn contract_id_changes_with_exact_wit_bytes() {
        assert_eq!(
            contract_id(),
            covalence_lib_hash::o256!(
                "e9970bacb41845dd89fd317ac59438e01e79ecdef560f7f4195e1b69d075f8af"
            )
        );
        assert_ne!(contract_id(), O256::from_bytes(b"similar contract"));
    }

    #[test]
    fn sql_outcomes_are_rectangular_and_bounded() {
        let outcome =
            SqlOutcome::rows(vec!["answer".to_owned()], vec![vec![SqlValue::Integer(42)]]).unwrap();
        assert!(matches!(
            outcome.kind(),
            SqlOutcomeKind::Rows { columns, rows }
                if columns == &["answer"] && rows == &[vec![SqlValue::Integer(42)]]
        ));
        assert_eq!(
            SqlOutcome::rows(vec!["x".to_owned()], vec![Vec::new()]),
            Err(ServiceError::InvalidRequest)
        );
        assert_eq!(
            SqlOutcome::rows(
                vec!["x".to_owned()],
                vec![vec![SqlValue::Blob(vec![0; MAX_SQL_OUTCOME_BYTES])]],
            ),
            Err(ServiceError::ResourceLimit)
        );
    }

    #[test]
    fn sqlite_diagnostics_are_utf8_bounded() {
        let diagnostic = SqlDiagnostic::new(8, 8, "é".repeat(MAX_SQL_DIAGNOSTIC_BYTES));
        assert!(diagnostic.message().len() <= MAX_SQL_DIAGNOSTIC_BYTES);
        assert!(
            diagnostic
                .message()
                .is_char_boundary(diagnostic.message().len())
        );
        assert_eq!(diagnostic.primary_code(), 8);
        assert_eq!(diagnostic.extended_code(), 8);
    }
}
