use std::error::Error as StdError;
use std::fmt;
use std::ops::RangeInclusive;

use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{
    ContextError, ContextId, Hol, KindError, KindId, Operation, Policy, TermError, TermId,
    TypeError, TypeId, read_kind, read_type, require_context, validate_term,
};
use crate::Connection;

/// Database-local identity of a hierarchical export namespace.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NamespaceId(i64);

impl NamespaceId {
    /// Returns the reserved anonymous root namespace.
    #[must_use]
    pub const fn root() -> Self {
        Self(0)
    }

    /// Constructs a lookup handle from its stored non-negative integer.
    #[must_use]
    pub const fn from_i64(id: i64) -> Self {
        Self(id)
    }

    /// Returns the stored integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// Namespace-wide identity of one exported value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExportId(i64);

impl ExportId {
    /// Constructs an export handle from its stored non-negative integer.
    #[must_use]
    pub const fn from_i64(id: i64) -> Self {
        Self(id)
    }

    /// Returns the stored integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// A sort accepted by range export.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExportSort {
    /// Kinds.
    Kind,
    /// Types.
    Type,
    /// Terms, whether closed or open.
    Term,
    /// Immutable contexts.
    Context,
}

impl ExportSort {
    const fn tag(self) -> &'static str {
        match self {
            Self::Kind => "kind",
            Self::Type => "type",
            Self::Term => "term",
            Self::Context => "context",
        }
    }

    fn value(self, id: i64) -> NamespaceExport {
        match self {
            Self::Kind => NamespaceExport::Kind(KindId::from_i64(id)),
            Self::Type => NamespaceExport::Type(TypeId::from_i64(id)),
            Self::Term => NamespaceExport::Term(TermId::from_i64(id)),
            Self::Context => NamespaceExport::Context(ContextId::from_i64(id)),
        }
    }
}

/// One database-local HOL value published by a namespace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NamespaceExport {
    /// An admitted kind.
    Kind(KindId),
    /// An admitted type.
    Type(TypeId),
    /// An admitted well-typed term.
    Term(TermId),
    /// An immutable context.
    Context(ContextId),
}

impl NamespaceExport {
    const fn parts(self) -> (ExportSort, i64) {
        match self {
            Self::Kind(id) => (ExportSort::Kind, id.get()),
            Self::Type(id) => (ExportSort::Type, id.get()),
            Self::Term(id) => (ExportSort::Term, id.get()),
            Self::Context(id) => (ExportSort::Context, id.get()),
        }
    }
}

/// Read-only view of one namespace header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamespaceView {
    /// Parent namespace, or none for a top-level namespace.
    pub parent: Option<NamespaceId>,
    /// Optional local name.
    pub name: Option<String>,
}

/// Read-only view of one namespace export.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExportView {
    /// Exported local value.
    pub value: NamespaceExport,
    /// Optional namespace-local unique name.
    pub name: Option<String>,
}

impl<P: Policy> Connection<Hol<P>> {
    /// Defines a namespace. Named siblings are canonical; anonymous namespaces are fresh.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies definition, the name or parent is invalid, IDs are
    /// exhausted, or `SQLite` rejects the transaction.
    pub fn create_namespace(
        &mut self,
        parent: Option<NamespaceId>,
        name: Option<&str>,
    ) -> Result<NamespaceId, NamespaceError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::DefineNamespace)?;
        validate_name(name)?;
        let transaction = neutron.sqlite().unchecked_transaction()?;
        if let Some(parent) = parent {
            require_namespace(&transaction, parent)
                .map_err(|_| NamespaceError::UnknownParent(parent))?;
        }
        if let Some(name) = name
            && let Some(id) = transaction
                .query_row(
                    "SELECT namespace_id FROM hol_namespace
                     WHERE parent_namespace_id IS ?1 AND name = ?2",
                    sqlite::params![parent.map(NamespaceId::get), name],
                    |row| row.get::<_, i64>(0).map(NamespaceId),
                )
                .optional()?
        {
            transaction.commit()?;
            return Ok(id);
        }
        let id = NamespaceId(next_id(&transaction, "hol_namespace", "namespace_id")?);
        transaction.execute(
            "INSERT INTO hol_namespace(namespace_id, parent_namespace_id, name)
             VALUES (?1, ?2, ?3)",
            sqlite::params![id.get(), parent.map(NamespaceId::get), name],
        )?;
        transaction.commit()?;
        Ok(id)
    }

    /// Reads one namespace header.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the namespace is absent, or `SQLite` rejects
    /// the query.
    pub fn namespace(&mut self, id: NamespaceId) -> Result<NamespaceView, NamespaceError> {
        let (neutron, hol) = self.parts_mut();
        authorize(&mut hol.policy, Operation::ReadNamespace)?;
        neutron
            .sqlite()
            .query_row(
                "SELECT parent_namespace_id, name FROM hol_namespace WHERE namespace_id = ?1",
                [id.get()],
                |row| {
                    Ok(NamespaceView {
                        parent: row.get::<_, Option<i64>>(0)?.map(NamespaceId),
                        name: row.get(1)?,
                    })
                },
            )
            .optional()?
            .ok_or(NamespaceError::UnknownNamespace(id))
    }

    /// Publishes a local HOL value under one namespace-wide export ID.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies publication, an input is invalid or conflicting, or
    /// `SQLite` rejects the transaction.
    pub fn export_value(
        &mut self,
        namespace: NamespaceId,
        export: ExportId,
        value: NamespaceExport,
        name: Option<&str>,
    ) -> Result<(), ExportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_export(&mut hol.policy, Operation::ExportNamespaceValue)?;
        validate_name(name).map_err(ExportError::Namespace)?;
        if export.get() < 0 {
            return Err(ExportError::InvalidExportId(export));
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_namespace(&transaction, namespace)?;
        validate_local(&transaction, value)?;
        insert_export(&transaction, namespace, export, value, name)?;
        transaction.commit()?;
        Ok(())
    }

    /// Publishes an inclusive contiguous range atomically, shifting it to `first_export`.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies publication, any ID is invalid or conflicting, range
    /// arithmetic overflows, or `SQLite` rejects the transaction.
    pub fn export_range(
        &mut self,
        namespace: NamespaceId,
        sort: ExportSort,
        local: RangeInclusive<i64>,
        first_export: ExportId,
    ) -> Result<(), ExportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_export(&mut hol.policy, Operation::ExportNamespaceValue)?;
        if first_export.get() < 0 || local.start() < &0 {
            return Err(ExportError::InvalidExportId(first_export));
        }
        let transaction = neutron.sqlite().unchecked_transaction()?;
        require_namespace(&transaction, namespace)?;
        let values = local
            .enumerate()
            .map(|(offset, local_id)| {
                let offset = i64::try_from(offset).map_err(|_| ExportError::RangeOverflow)?;
                let export_id = first_export
                    .get()
                    .checked_add(offset)
                    .map(ExportId)
                    .ok_or(ExportError::RangeOverflow)?;
                Ok((export_id, sort.value(local_id)))
            })
            .collect::<Result<Vec<_>, ExportError>>()?;
        for (_, value) in &values {
            validate_local(&transaction, *value)?;
        }
        for (export, value) in values {
            insert_export(&transaction, namespace, export, value, None)?;
        }
        transaction.commit()?;
        Ok(())
    }

    /// Resolves an export ID without granting theorem authority.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the namespace is absent, or `SQLite` rejects
    /// the query.
    pub fn resolve_export(
        &mut self,
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<Option<ExportView>, ExportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_export(&mut hol.policy, Operation::ReadNamespaceExport)?;
        require_namespace(neutron.sqlite(), namespace)?;
        read_export(neutron.sqlite(), namespace, export)
    }

    /// Resolves a namespace-local export name without granting theorem authority.
    ///
    /// # Errors
    ///
    /// Returns an error if policy denies the read, the namespace is absent, or `SQLite` rejects
    /// the query.
    pub fn resolve_export_name(
        &mut self,
        namespace: NamespaceId,
        name: &str,
    ) -> Result<Option<(ExportId, ExportView)>, ExportError> {
        let (neutron, hol) = self.parts_mut();
        authorize_export(&mut hol.policy, Operation::ReadNamespaceExport)?;
        require_namespace(neutron.sqlite(), namespace)?;
        Ok(neutron
            .sqlite()
            .query_row(
                "SELECT export_id, sort, local_id, name FROM hol_namespace_export
                 WHERE namespace_id = ?1 AND name = ?2",
                sqlite::params![namespace.get(), name],
                |row| {
                    let export = ExportId(row.get(0)?);
                    let sort = row.get::<_, String>(1)?;
                    let view = decode_export(&sort, row.get(2)?, row.get(3)?)?;
                    Ok((export, view))
                },
            )
            .optional()?)
    }
}

fn validate_name(name: Option<&str>) -> Result<(), NamespaceError> {
    if name.is_some_and(str::is_empty) {
        Err(NamespaceError::InvalidName(String::new()))
    } else {
        Ok(())
    }
}

fn next_id(
    connection: &sqlite::Connection,
    table: &str,
    column: &str,
) -> Result<i64, NamespaceError> {
    let sql = format!("SELECT max({column}) FROM {table}");
    let maximum = connection
        .query_row(&sql, [], |row| row.get::<_, Option<i64>>(0))?
        .unwrap_or(-1);
    maximum.checked_add(1).ok_or(NamespaceError::IdOverflow)
}

fn require_namespace(
    connection: &sqlite::Connection,
    id: NamespaceId,
) -> Result<(), NamespaceError> {
    if id.get() < 0 {
        return Err(NamespaceError::UnknownNamespace(id));
    }
    let exists = connection.query_row(
        "SELECT EXISTS(SELECT 1 FROM hol_namespace WHERE namespace_id = ?1)",
        [id.get()],
        |row| row.get::<_, bool>(0),
    )?;
    if exists {
        Ok(())
    } else {
        Err(NamespaceError::UnknownNamespace(id))
    }
}

fn validate_local(
    connection: &sqlite::Connection,
    value: NamespaceExport,
) -> Result<(), ExportError> {
    match value {
        NamespaceExport::Kind(id) => read_kind(connection, id).map(|_| ()).map_err(Into::into),
        NamespaceExport::Type(id) => read_type(connection, id).map(|_| ()).map_err(Into::into),
        NamespaceExport::Term(id) => validate_term(connection, id)
            .map(|_| ())
            .map_err(Into::into),
        NamespaceExport::Context(id) => require_context(connection, id).map_err(Into::into),
    }
}

fn insert_export(
    connection: &sqlite::Connection,
    namespace: NamespaceId,
    export: ExportId,
    value: NamespaceExport,
    name: Option<&str>,
) -> Result<(), ExportError> {
    if let Some(existing) = read_export(connection, namespace, export)? {
        return if existing.value == value && existing.name.as_deref() == name {
            Ok(())
        } else {
            Err(ExportError::ExportConflict { namespace, export })
        };
    }
    if let Some(name) = name {
        let exists = connection.query_row(
            "SELECT EXISTS(SELECT 1 FROM hol_namespace_export
             WHERE namespace_id = ?1 AND name = ?2)",
            sqlite::params![namespace.get(), name],
            |row| row.get::<_, bool>(0),
        )?;
        if exists {
            return Err(ExportError::NameConflict {
                namespace,
                name: name.to_owned(),
            });
        }
    }
    let (sort, local_id) = value.parts();
    connection.execute(
        "INSERT INTO hol_namespace_export(namespace_id, export_id, sort, local_id, name)
         VALUES (?1, ?2, ?3, ?4, ?5)",
        sqlite::params![namespace.get(), export.get(), sort.tag(), local_id, name],
    )?;
    Ok(())
}

fn read_export(
    connection: &sqlite::Connection,
    namespace: NamespaceId,
    export: ExportId,
) -> Result<Option<ExportView>, ExportError> {
    Ok(connection
        .query_row(
            "SELECT sort, local_id, name FROM hol_namespace_export
             WHERE namespace_id = ?1 AND export_id = ?2",
            sqlite::params![namespace.get(), export.get()],
            |row| {
                let sort = row.get::<_, String>(0)?;
                decode_export(&sort, row.get(1)?, row.get(2)?)
            },
        )
        .optional()?)
}

fn decode_export(
    sort: &str,
    local_id: i64,
    name: Option<String>,
) -> Result<ExportView, sqlite::Error> {
    let value = match sort {
        "kind" => NamespaceExport::Kind(KindId::from_i64(local_id)),
        "type" => NamespaceExport::Type(TypeId::from_i64(local_id)),
        "term" => NamespaceExport::Term(TermId::from_i64(local_id)),
        "context" => NamespaceExport::Context(ContextId::from_i64(local_id)),
        _ => return Err(sqlite::Error::InvalidQuery),
    };
    Ok(ExportView { value, name })
}

fn authorize(policy: &mut impl Policy, operation: Operation) -> Result<(), NamespaceError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(NamespaceError::Denied(operation))
    }
}

fn authorize_export(policy: &mut impl Policy, operation: Operation) -> Result<(), ExportError> {
    if policy.allows(operation) {
        Ok(())
    } else {
        Err(ExportError::Denied(operation))
    }
}

/// Failure to define or inspect a local namespace.
#[derive(Debug)]
pub enum NamespaceError {
    /// Policy denied the operation.
    Denied(Operation),
    /// Namespace does not exist.
    UnknownNamespace(NamespaceId),
    /// Requested parent does not exist.
    UnknownParent(NamespaceId),
    /// Namespace names must be nonempty when present.
    InvalidName(String),
    /// No further non-negative namespace ID can be allocated.
    IdOverflow,
    /// `SQLite` rejected the operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for NamespaceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::UnknownNamespace(id) => write!(formatter, "unknown namespace {}", id.get()),
            Self::UnknownParent(id) => write!(formatter, "unknown parent namespace {}", id.get()),
            Self::InvalidName(name) => write!(formatter, "invalid namespace name {name:?}"),
            Self::IdOverflow => formatter.write_str("namespace ID overflow"),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for NamespaceError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<sqlite::Error> for NamespaceError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

/// Failure to publish or inspect a namespace export.
#[derive(Debug)]
pub enum ExportError {
    /// Policy denied the operation.
    Denied(Operation),
    /// Namespace validation failed.
    Namespace(NamespaceError),
    /// Export IDs must be non-negative.
    InvalidExportId(ExportId),
    /// An export ID already denotes another value or name.
    ExportConflict {
        namespace: NamespaceId,
        export: ExportId,
    },
    /// A name is already used by another export in this namespace.
    NameConflict {
        namespace: NamespaceId,
        name: String,
    },
    /// Range shifting overflowed an integer ID.
    RangeOverflow,
    /// Kind validation failed.
    Kind(KindError),
    /// Type validation failed.
    Type(TypeError),
    /// Term validation failed.
    Term(TermError),
    /// Context validation failed.
    Context(ContextError),
    /// `SQLite` rejected the operation.
    Sqlite(sqlite::Error),
}

impl fmt::Display for ExportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(operation) => write!(formatter, "HOL policy denied {operation:?}"),
            Self::Namespace(error) => error.fmt(formatter),
            Self::InvalidExportId(id) => write!(formatter, "invalid export ID {}", id.get()),
            Self::ExportConflict { namespace, export } => write!(
                formatter,
                "export {} already has another meaning in namespace {}",
                export.get(),
                namespace.get()
            ),
            Self::NameConflict { namespace, name } => write!(
                formatter,
                "export name {name:?} is already used in namespace {}",
                namespace.get()
            ),
            Self::RangeOverflow => formatter.write_str("export range overflow"),
            Self::Kind(error) => error.fmt(formatter),
            Self::Type(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::Context(error) => error.fmt(formatter),
            Self::Sqlite(error) => error.fmt(formatter),
        }
    }
}

impl StdError for ExportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Namespace(error) => Some(error),
            Self::Kind(error) => Some(error),
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Context(error) => Some(error),
            Self::Sqlite(error) => Some(error),
            _ => None,
        }
    }
}

impl From<NamespaceError> for ExportError {
    fn from(error: NamespaceError) -> Self {
        Self::Namespace(error)
    }
}
impl From<KindError> for ExportError {
    fn from(error: KindError) -> Self {
        Self::Kind(error)
    }
}
impl From<TypeError> for ExportError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}
impl From<TermError> for ExportError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}
impl From<ContextError> for ExportError {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
    }
}
impl From<sqlite::Error> for ExportError {
    fn from(error: sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::{
        AllowAll, HolImageValidationError, HolSchema, Kind, MetadataTable, MetadataTarget,
        MetadataType, MetadataValue, ValidatedHolImage,
    };

    #[test]
    fn namespaces_are_hierarchical_and_named_siblings_are_canonical() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        assert_eq!(
            connection.namespace(NamespaceId::root()).unwrap(),
            NamespaceView {
                parent: None,
                name: None
            }
        );
        let parent = connection
            .create_namespace(Some(NamespaceId::root()), Some("logic"))
            .unwrap();
        assert_eq!(
            connection
                .create_namespace(Some(NamespaceId::root()), Some("logic"))
                .unwrap(),
            parent
        );
        let first = connection.create_namespace(Some(parent), None).unwrap();
        let second = connection.create_namespace(Some(parent), None).unwrap();
        assert_ne!(first, second);
        assert!(matches!(
            connection.create_namespace(Some(NamespaceId::from_i64(999)), Some("bad")),
            Err(NamespaceError::UnknownParent(_))
        ));
    }

    #[test]
    fn one_export_space_round_trips_all_sorts_and_allows_aliases() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let namespace = connection
            .create_namespace(Some(NamespaceId::root()), Some("demo"))
            .unwrap();
        let kind = connection.insert_kind(&Kind::Star).unwrap();
        let ty = connection.insert_bool_type().unwrap();
        let term = connection.insert_bool_term(true).unwrap();
        let context = connection.define_context([term]).unwrap();
        let values = [
            NamespaceExport::Kind(kind),
            NamespaceExport::Type(ty),
            NamespaceExport::Term(term),
            NamespaceExport::Context(context),
        ];
        for (index, value) in values.into_iter().enumerate() {
            let export = ExportId::from_i64(i64::try_from(index).unwrap());
            connection
                .export_value(namespace, export, value, Some(["k", "t", "m", "c"][index]))
                .unwrap();
            assert_eq!(
                connection
                    .resolve_export(namespace, export)
                    .unwrap()
                    .unwrap()
                    .value,
                value
            );
        }
        connection
            .export_value(
                namespace,
                ExportId::from_i64(4),
                NamespaceExport::Term(term),
                None,
            )
            .unwrap();
        connection
            .export_value(
                namespace,
                ExportId::from_i64(4),
                NamespaceExport::Term(term),
                None,
            )
            .unwrap();
        assert!(matches!(
            connection.export_value(
                namespace,
                ExportId::from_i64(0),
                NamespaceExport::Term(term),
                None
            ),
            Err(ExportError::ExportConflict { .. })
        ));
        assert_eq!(
            connection
                .resolve_export_name(namespace, "m")
                .unwrap()
                .unwrap()
                .0,
            ExportId::from_i64(2)
        );
    }

    #[test]
    fn range_export_is_atomic_and_metadata_is_user_extensible() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::Namespace, "doc", MetadataType::Text)
            .unwrap();
        schema
            .add_column_to(
                MetadataTable::NamespaceExport,
                "priority",
                MetadataType::Integer,
            )
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::NamespaceExport,
                "hol_export_priority",
                ["priority"],
                false,
            )
            .unwrap();
        let mut connection = Connection::open_hol_in_memory_with_schema(AllowAll, schema).unwrap();
        let namespace = connection.create_namespace(None, Some("n")).unwrap();
        connection
            .set_metadata(
                MetadataTarget::namespace(namespace),
                &[("doc", MetadataValue::Text("docs".to_owned()))],
            )
            .unwrap();
        connection
            .export_range(namespace, ExportSort::Kind, 1..=1, ExportId::from_i64(10))
            .unwrap();
        connection
            .set_metadata(
                MetadataTarget::namespace_export(namespace, ExportId::from_i64(10)),
                &[("priority", MetadataValue::Integer(7))],
            )
            .unwrap();
        assert_eq!(
            connection
                .metadata(MetadataTarget::namespace(namespace), &["doc"])
                .unwrap(),
            [MetadataValue::Text("docs".to_owned())]
        );
        assert!(
            connection
                .export_range(namespace, ExportSort::Kind, 1..=2, ExportId::from_i64(20),)
                .is_err()
        );
        assert_eq!(
            connection
                .resolve_export(namespace, ExportId::from_i64(20))
                .unwrap(),
            None
        );
    }

    #[test]
    fn detached_validation_rechecks_namespace_graph_and_export_sort() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bytes = connection.parts_mut().0.serialize().unwrap();
        let corrupt = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt
            .sqlite()
            .execute(
                "INSERT INTO hol_namespace(namespace_id, parent_namespace_id, name)
                 VALUES (1, 2, 'a'), (2, 1, 'b')",
                [],
            )
            .unwrap();
        let cyclic = corrupt.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&cyclic),
            Err(HolImageValidationError::CyclicNamespace(_))
        ));

        let corrupt = covalence_neutron::Connection::deserialize(&bytes).unwrap();
        corrupt
            .sqlite()
            .execute(
                "INSERT INTO hol_namespace_export(namespace_id, export_id, sort, local_id)
                 VALUES (0, 0, 'term', 1)",
                [],
            )
            .unwrap();
        let wrong_sort = corrupt.serialize().unwrap();
        assert!(matches!(
            ValidatedHolImage::validate(&wrong_sort),
            Err(HolImageValidationError::InvalidNamespaceExport { .. })
        ));
    }
}
