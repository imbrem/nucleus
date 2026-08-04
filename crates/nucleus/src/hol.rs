//! Minimal HOL-omega protocol, beginning with canonical kinds.

use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use crate::Connection;

const SCHEMA: &str = include_str!("hol/schema.sql");
const STAR_ID: KindId = KindId(1);

/// A HOL-omega kind expression accepted by the representation-independent API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Kind {
    /// The kind of ordinary types.
    Star,
    /// A type-operator kind.
    Arrow(Box<Self>, Box<Self>),
}

impl Kind {
    /// Constructs a type-operator kind.
    #[must_use]
    pub fn arrow(domain: Self, codomain: Self) -> Self {
        Self::Arrow(Box::new(domain), Box::new(codomain))
    }
}

/// Database-local identity of an admitted kind.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KindId(i64);

impl KindId {
    /// Returns the integer stored in the HOL database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One admitted kind row, independent of its physical representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KindView {
    /// The canonical kind of ordinary types.
    Star,
    /// A canonical type-operator kind.
    Arrow {
        /// Kind accepted by the operator.
        domain: KindId,
        /// Kind returned by the operator.
        codomain: KindId,
    },
}

/// A policy-visible trusted HOL operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Operation {
    /// Read a kind constructor or its derived rank.
    ReadKind,
    /// Validate and canonically intern a kind.
    InsertKind,
}

/// Connection-local permission and operation-recording policy.
pub trait Policy {
    /// Returns whether this operation is permitted.
    ///
    /// Implementations may record the operation before returning.
    fn allows(&mut self, operation: Operation) -> bool;
}

/// A policy which permits every currently implemented HOL operation.
#[derive(Clone, Copy, Debug, Default)]
pub struct AllowAll;

impl Policy for AllowAll {
    fn allows(&mut self, _operation: Operation) -> bool {
        true
    }
}

/// HOL protocol state carried by [`Connection`].
pub struct Hol<P> {
    policy: P,
}

impl<P> Hol<P> {
    /// Returns this connection's policy state.
    #[must_use]
    pub const fn policy(&self) -> &P {
        &self.policy
    }
}

impl<P: Policy> Connection<Hol<P>> {
    /// Opens a new in-memory HOL-omega store and installs schema version zero.
    ///
    /// # Errors
    ///
    /// Returns an error if the Neutron connection or HOL schema cannot be
    /// opened.
    pub fn open_hol_in_memory(policy: P) -> Result<Self, HolOpenError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        neutron.sqlite().execute_batch(SCHEMA)?;
        Ok(Self::from_neutron(neutron, Hol { policy }))
    }

    /// Validates and canonically interns a kind.
    ///
    /// The normative rank convention is `rank(star) = 0` and
    /// `rank(K -> L) = max(rank(K) + 1, rank(L))`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies insertion or the store rejects the
    /// transaction.
    pub fn insert_kind(&mut self, kind: &Kind) -> Result<KindId, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::InsertKind)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        let id = intern_kind(&transaction, kind)?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads the constructor of an admitted kind.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is unknown, or the
    /// universal node row is corrupt.
    pub fn kind(&mut self, id: KindId) -> Result<KindView, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadKind)?;
        read_kind(neutron.sqlite(), id)
    }

    /// Derives the rank of an admitted kind from its node graph.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the ID is unknown, the node
    /// graph is malformed or cyclic, or the derived rank overflows.
    pub fn kind_rank(&mut self, id: KindId) -> Result<u32, KindError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadKind)?;
        kind_rank(
            neutron.sqlite(),
            id,
            &mut HashSet::new(),
            &mut HashMap::new(),
        )
    }
}

fn authorize(policy: &mut impl Policy, operation: Operation) -> Result<(), KindError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(KindError::Denied(operation))
    }
}

fn intern_kind(connection: &sqlite::Connection, kind: &Kind) -> Result<KindId, KindError> {
    let Kind::Arrow(domain, codomain) = kind else {
        return Ok(STAR_ID);
    };
    let domain = intern_kind(connection, domain)?;
    let codomain = intern_kind(connection, codomain)?;
    if let Some(id) = connection
        .query_row(
            "SELECT node_id FROM hol_node
             WHERE tag = 'KARR' AND lhs = ?1 AND rhs = ?2 AND ty IS NULL",
            [domain.0, codomain.0],
            |row| row.get::<_, i64>(0),
        )
        .optional()?
    {
        return Ok(KindId(id));
    }

    connection.execute(
        "INSERT INTO hol_node(tag, lhs, rhs) VALUES ('KARR', ?1, ?2)",
        [domain.0, codomain.0],
    )?;
    let id = KindId(connection.last_insert_rowid());
    Ok(id)
}

fn read_kind(connection: &sqlite::Connection, id: KindId) -> Result<KindView, KindError> {
    let row = connection
        .query_row(
            "SELECT tag, lhs, rhs, ty FROM hol_node WHERE node_id = ?1",
            [id.0],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, Option<i64>>(1)?,
                    row.get::<_, Option<i64>>(2)?,
                    row.get::<_, Option<i64>>(3)?,
                ))
            },
        )
        .optional()?
        .ok_or(KindError::UnknownKind(id))?;
    match row {
        (tag, None, None, None) if tag == "KSTAR" => Ok(KindView::Star),
        (tag, Some(domain), Some(codomain), None) if tag == "KARR" => Ok(KindView::Arrow {
            domain: KindId(domain),
            codomain: KindId(codomain),
        }),
        _ => Err(KindError::CorruptKind(id)),
    }
}

fn kind_rank(
    connection: &sqlite::Connection,
    id: KindId,
    active: &mut HashSet<KindId>,
    memo: &mut HashMap<KindId, u32>,
) -> Result<u32, KindError> {
    if let Some(rank) = memo.get(&id) {
        return Ok(*rank);
    }
    if !active.insert(id) {
        return Err(KindError::CorruptKind(id));
    }
    let result: Result<u32, KindError> = match read_kind(connection, id)? {
        KindView::Star => Ok(0),
        KindView::Arrow { domain, codomain } => {
            let domain = kind_rank(connection, domain, active, memo)?;
            let codomain = kind_rank(connection, codomain, active, memo)?;
            Ok(domain
                .checked_add(1)
                .ok_or(KindError::RankOverflow)?
                .max(codomain))
        }
    };
    active.remove(&id);
    let rank = result?;
    memo.insert(id, rank);
    Ok(rank)
}

/// Failure to open a HOL connection.
#[derive(Debug)]
pub enum HolOpenError {
    /// The raw connection could not be opened.
    Connection(covalence_neutron::ConnectionError),
    /// The schema could not be installed.
    Schema(sqlite::Error),
}

impl fmt::Display for HolOpenError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Connection(error) => write!(formatter, "could not open HOL connection: {error}"),
            Self::Schema(error) => write!(formatter, "could not install HOL schema: {error}"),
        }
    }
}

impl StdError for HolOpenError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Connection(error) => Some(error),
            Self::Schema(error) => Some(error),
        }
    }
}

impl From<covalence_neutron::ConnectionError> for HolOpenError {
    fn from(error: covalence_neutron::ConnectionError) -> Self {
        Self::Connection(error)
    }
}

impl From<sqlite::Error> for HolOpenError {
    fn from(error: sqlite::Error) -> Self {
        Self::Schema(error)
    }
}

/// Failure to insert or inspect an admitted kind.
#[derive(Debug)]
pub enum KindError {
    /// Policy denied the operation.
    Denied(Operation),
    /// No kind has the requested ID.
    UnknownKind(KindId),
    /// A universal node has an invalid kind shape or constructor.
    CorruptKind(KindId),
    /// The normative rank does not fit in `SQLite`'s integer representation.
    RankOverflow,
    /// `SQLite` rejected an operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for KindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownKind(id) => write!(formatter, "unknown kind {}", id.get()),
            Self::CorruptKind(id) => write!(formatter, "kind {} is structurally corrupt", id.get()),
            Self::RankOverflow => formatter.write_str("kind rank overflow"),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for KindError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            Self::Denied(_) | Self::UnknownKind(_) | Self::CorruptKind(_) | Self::RankOverflow => {
                None
            }
        }
    }
}

impl From<sqlite::Error> for KindError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct RecordingPolicy {
        allowed: bool,
        operations: Vec<Operation>,
    }

    impl Policy for RecordingPolicy {
        fn allows(&mut self, operation: Operation) -> bool {
            self.operations.push(operation);
            self.allowed
        }
    }

    #[test]
    fn canonically_interns_kinds_and_computes_order_rank() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let star = connection.insert_kind(&Kind::Star).unwrap();
        let unary = connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        let higher = connection
            .insert_kind(&Kind::arrow(
                Kind::arrow(Kind::Star, Kind::Star),
                Kind::Star,
            ))
            .unwrap();

        assert_eq!(star, STAR_ID);
        assert_eq!(
            unary,
            connection
                .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
                .unwrap()
        );
        assert_eq!(connection.kind(star).unwrap(), KindView::Star);
        assert_eq!(
            connection.kind(unary).unwrap(),
            KindView::Arrow {
                domain: star,
                codomain: star,
            }
        );
        assert_eq!(connection.kind_rank(star).unwrap(), 0);
        assert_eq!(connection.kind_rank(unary).unwrap(), 1);
        assert_eq!(connection.kind_rank(higher).unwrap(), 2);
    }

    #[test]
    fn policy_controls_and_records_every_public_operation() {
        let mut connection = Connection::open_hol_in_memory(RecordingPolicy::default()).unwrap();
        assert!(matches!(
            connection.insert_kind(&Kind::Star),
            Err(KindError::Denied(Operation::InsertKind))
        ));
        assert!(matches!(
            connection.kind(STAR_ID),
            Err(KindError::Denied(Operation::ReadKind))
        ));
        assert_eq!(
            connection.protocol().policy().operations,
            [Operation::InsertKind, Operation::ReadKind]
        );
    }

    #[test]
    fn detects_invalid_constructor_tags() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let arrow = connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute_batch("PRAGMA ignore_check_constraints = ON")
            .unwrap();
        connection
            .parts_mut()
            .0
            .sqlite()
            .execute(
                "UPDATE hol_node SET tag = 'NOPE' WHERE node_id = ?1",
                [arrow.0],
            )
            .unwrap();
        assert!(matches!(
            connection.kind(arrow),
            Err(KindError::CorruptKind(id)) if id == arrow
        ));
    }

    #[test]
    fn stores_every_kind_as_one_tagged_node_row() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        connection
            .insert_kind(&Kind::arrow(Kind::Star, Kind::Star))
            .unwrap();
        let rows = connection
            .parts_mut()
            .0
            .sqlite()
            .query_row(
                "SELECT count(*), count(DISTINCT node_id), count(DISTINCT tag) FROM hol_node",
                [],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, i64>(2)?,
                    ))
                },
            )
            .unwrap();
        assert_eq!(rows, (2, 2, 2));
    }
}
