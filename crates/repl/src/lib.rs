//! Transport-neutral REPL orchestration.
//!
//! A [`Repl`] is not a Nucleus connection protocol. It maintains an ordinary,
//! inspectable `SQLite` directory in a raw Neutron connection and associates its
//! rows with runtime connection handles owned by the current process.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;
use std::str::FromStr;

use covalence_lib_sqlite as sqlite;

pub mod hol_recipes;

pub use covalence_nucleus::sql::{
    ImageError, MAX_IMAGE_BYTES, Outcome, QueryResult, Statement, Value,
};
pub use covalence_nucleus::{AllowAll, Connection, Hol, Kernel, Sql};
use covalence_nucleus::{ContextId, ProofError, TermError, TypeError};

const SCHEMA: &str = "
PRAGMA foreign_keys = ON;
CREATE TABLE repl_kernel (
    kernel_id INTEGER PRIMARY KEY,
    transport TEXT NOT NULL,
    endpoint TEXT,
    public_key BLOB NOT NULL CHECK (length(public_key) = 32)
) STRICT;
CREATE TABLE repl_connection (
    connection_id INTEGER PRIMARY KEY,
    kernel_id INTEGER NOT NULL REFERENCES repl_kernel,
    protocol TEXT NOT NULL,
    remote_connection_id TEXT
) STRICT;
CREATE TABLE repl_state (
    singleton INTEGER PRIMARY KEY CHECK (singleton = 0),
    active_connection_id INTEGER REFERENCES repl_connection
) STRICT;
INSERT INTO repl_state(singleton) VALUES (0);
";

/// Process-local identifier for a managed connection.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConnectionId(i64);

impl ConnectionId {
    /// Creates an ID from the browser ABI's unsigned representation.
    #[must_use]
    pub const fn from_u32(id: u32) -> Self {
        Self(id as i64)
    }

    /// Returns the integer stored in the REPL state database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

impl fmt::Display for ConnectionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// A connection directory backed by its own raw `SQLite` database.
pub struct Repl<C> {
    state: covalence_neutron::Connection,
    connections: HashMap<ConnectionId, C>,
}

impl<C> Repl<C> {
    /// Opens an empty, in-memory REPL state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the raw Neutron connection or state schema cannot
    /// be opened.
    pub fn new(local_public_key: &[u8]) -> Result<Self, ReplError> {
        let state = covalence_neutron::Connection::open_in_memory()?;
        let transaction = state.sqlite().unchecked_transaction()?;
        transaction.execute_batch(SCHEMA)?;
        transaction.execute(
            "INSERT INTO repl_kernel(kernel_id, transport, public_key) VALUES (0, 'local', ?1)",
            [local_public_key],
        )?;
        transaction.commit()?;
        Ok(Self {
            state,
            connections: HashMap::new(),
        })
    }

    /// Returns the raw state connection for inspection and debugging.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        &self.state
    }

    /// Adds a runtime handle and records its protocol in the state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the directory cannot be updated.
    pub fn insert(&mut self, protocol: &str, connection: C) -> Result<ConnectionId, ReplError> {
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "INSERT INTO repl_connection(kernel_id, protocol) VALUES (0, ?1)",
            [protocol],
        )?;
        let id = ConnectionId(transaction.last_insert_rowid());
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = COALESCE(active_connection_id, ?1)
             WHERE singleton = 0",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections.insert(id, connection);
        Ok(id)
    }

    /// Returns the active connection ID, if any.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database cannot be read.
    pub fn active(&self) -> Result<Option<ConnectionId>, ReplError> {
        self.state
            .sqlite()
            .query_row(
                "SELECT active_connection_id FROM repl_state WHERE singleton = 0",
                (),
                |row| row.get::<_, Option<i64>>(0),
            )
            .map(|id| id.map(ConnectionId))
            .map_err(ReplError::from)
    }

    /// Selects an existing connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), ReplError> {
        self.require(id)?;
        self.state.sqlite().execute(
            "UPDATE repl_state SET active_connection_id = ?1 WHERE singleton = 0",
            [id.0],
        )?;
        Ok(())
    }

    /// Returns a mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or closed connection.
    pub fn get_mut(&mut self, id: ConnectionId) -> Result<&mut C, ReplError> {
        self.connections
            .get_mut(&id)
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Returns the active mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection is selected or state inspection fails.
    pub fn active_mut(&mut self) -> Result<&mut C, ReplError> {
        let id = self.active()?.ok_or(ReplError::NoActiveConnection)?;
        self.get_mut(id)
    }

    /// Closes and returns a runtime handle.
    ///
    /// If it was active, the lowest remaining ID becomes active.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn remove(&mut self, id: ConnectionId) -> Result<C, ReplError> {
        self.require(id)?;
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = (
                 SELECT min(connection_id) FROM repl_connection WHERE connection_id <> ?1
             )
             WHERE singleton = 0 AND active_connection_id = ?1",
            [id.0],
        )?;
        transaction.execute(
            "DELETE FROM repl_connection WHERE connection_id = ?1",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections
            .remove(&id)
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Runs one row-returning SQL statement against the REPL state database.
    ///
    /// The directory is ordinary `SQLite` and carries no logical trust, so
    /// front ends may expose this directly for debugging. The statement runs
    /// under `PRAGMA query_only`, so inspection cannot mutate the directory.
    ///
    /// # Errors
    ///
    /// Returns an error if the statement is invalid, returns no columns, or
    /// fails while executing.
    pub fn inspect_state(&self, sql: &str) -> Result<QueryResult, ReplError> {
        let connection = self.state.sqlite();
        connection.pragma_update(None, "query_only", true)?;
        let result = Self::query_state(connection, sql);
        connection.pragma_update(None, "query_only", false)?;
        result
    }

    fn query_state(connection: &sqlite::Connection, sql: &str) -> Result<QueryResult, ReplError> {
        let mut statement = connection.prepare(sql)?;
        let columns: Vec<String> = statement
            .column_names()
            .into_iter()
            .map(str::to_owned)
            .collect();
        if columns.is_empty() {
            return Err(ReplError::StateQueryReturnsNoRows);
        }
        let mut query = statement.query(())?;
        let mut rows = Vec::new();
        while let Some(row) = query.next()? {
            let mut values = Vec::with_capacity(columns.len());
            for index in 0..columns.len() {
                values.push(Value::from(row.get::<_, sqlite::types::Value>(index)?));
            }
            rows.push(values);
        }
        Ok(QueryResult { columns, rows })
    }

    fn require(&self, id: ConnectionId) -> Result<(), ReplError> {
        if self.connections.contains_key(&id) {
            Ok(())
        } else {
            Err(ReplError::UnknownConnection(id))
        }
    }
}

/// A process-local connection managed by the terminal or browser adapter.
///
/// This sum belongs above Nucleus's protocol boundary. It lets one REPL
/// directory select heterogeneous connections without making `Repl` itself a
/// protocol or weakening either connection's type.
pub enum LocalConnection {
    /// An unrestricted raw `SQLite` connection.
    Sql(Connection<Sql>),
    /// A rank-zero HOL connection using the demo's permissive policy.
    Hol(Connection<Hol<AllowAll>>),
}

impl LocalConnection {
    /// Returns the stable protocol name recorded in the REPL state database.
    #[must_use]
    pub const fn protocol(&self) -> &'static str {
        match self {
            Self::Sql(_) => "nucleus/sql",
            Self::Hol(_) => "nucleus/hol",
        }
    }

    /// Borrows this connection as SQL.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected connection is HOL.
    pub const fn sql_mut(&mut self) -> Result<&mut Connection<Sql>, ConnectionKindError> {
        match self {
            Self::Sql(connection) => Ok(connection),
            Self::Hol(_) => Err(ConnectionKindError::ExpectedSql),
        }
    }

    /// Borrows this connection as HOL.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected connection is SQL.
    pub const fn hol_mut(&mut self) -> Result<&mut Connection<Hol<AllowAll>>, ConnectionKindError> {
        match self {
            Self::Hol(connection) => Ok(connection),
            Self::Sql(_) => Err(ConnectionKindError::ExpectedHol),
        }
    }
}

/// A selected local connection has the wrong protocol for an operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConnectionKindError {
    /// A SQL operation selected a HOL connection.
    ExpectedSql,
    /// A HOL operation selected a SQL connection.
    ExpectedHol,
}

impl fmt::Display for ConnectionKindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedSql => formatter.write_str("selected connection is not SQL"),
            Self::ExpectedHol => formatter.write_str("selected connection is not HOL"),
        }
    }
}

impl StdError for ConnectionKindError {}

/// A deliberately tiny, transport-neutral HOL demo recipe.
///
/// Recipe interpretation is an untrusted convenience layer. Soundness comes
/// from the branded Nucleus operations called by [`HolRecipe::execute`], not
/// from parsing or from this enum.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HolRecipe {
    /// Prove primitive truth in the empty context.
    Truth,
    /// Prove reflexivity of one Boolean literal.
    Reflexivity(bool),
    /// Prove closed beta reduction of Boolean identity at one literal.
    Beta(bool),
}

impl HolRecipe {
    /// Runs the recipe and persists its syntax and resulting judgement.
    ///
    /// Proof steps remain ephemeral capabilities. The persisted judgement is
    /// canonical kernel state; recording a recipe or trace is left to an
    /// optional metadata database above this adapter.
    ///
    /// # Errors
    ///
    /// Returns an error if Nucleus rejects a syntax constructor or proof rule.
    pub fn execute<P: covalence_nucleus::Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
    ) -> Result<HolRecipeResult, HolRecipeError> {
        let context = ContextId::empty();
        let (recipe, statement, conclusion) = match self {
            Self::Truth => {
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = proof.prove_truth(context)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                ("truth", "true", conclusion)
            }
            Self::Reflexivity(value) => {
                let literal = connection.insert_bool_term(value)?;
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = hol_recipes::reflexivity(&mut proof, context, literal)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                (
                    "reflexivity",
                    if value {
                        "true = true"
                    } else {
                        "false = false"
                    },
                    conclusion,
                )
            }
            Self::Beta(value) => {
                let bool_type = connection.insert_bool_type()?;
                let variable = connection.insert_bound_term(0, bool_type)?;
                let identity = connection.insert_lambda(bool_type, variable)?;
                let literal = connection.insert_bool_term(value)?;
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = hol_recipes::beta(&mut proof, context, identity, literal)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                (
                    "beta",
                    if value {
                        "(lambda x:bool. x) true = true"
                    } else {
                        "(lambda x:bool. x) false = false"
                    },
                    conclusion,
                )
            }
        };
        Ok(HolRecipeResult {
            recipe,
            context_id: context.get(),
            conclusion_id: conclusion.get(),
            statement,
        })
    }
}

impl FromStr for HolRecipe {
    type Err = HolRecipeError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        let mut words = source.split_whitespace();
        let recipe = match (words.next(), words.next(), words.next()) {
            (Some("truth"), None, None) => Self::Truth,
            (Some("reflexivity" | "refl"), Some(value), None) => {
                Self::Reflexivity(parse_bool(value)?)
            }
            (Some("beta"), Some(value), None) => Self::Beta(parse_bool(value)?),
            _ => return Err(HolRecipeError::InvalidRecipe),
        };
        Ok(recipe)
    }
}

fn parse_bool(value: &str) -> Result<bool, HolRecipeError> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(HolRecipeError::InvalidBoolean),
    }
}

/// Common result returned by native and browser recipe adapters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolRecipeResult {
    recipe: &'static str,
    context_id: i64,
    conclusion_id: i64,
    statement: &'static str,
}

impl HolRecipeResult {
    /// Returns `hol-theorem`, the discriminant shared by every frontend.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "hol-theorem"
    }

    /// Returns the recipe constructor name.
    #[must_use]
    pub const fn recipe(&self) -> &'static str {
        self.recipe
    }

    /// Returns the database-local context ID.
    #[must_use]
    pub const fn context_id(&self) -> i64 {
        self.context_id
    }

    /// Returns the database-local conclusion term ID.
    #[must_use]
    pub const fn conclusion_id(&self) -> i64 {
        self.conclusion_id
    }

    /// Returns a human-readable statement fixed by the recipe.
    #[must_use]
    pub const fn statement(&self) -> &'static str {
        self.statement
    }
}

/// Failure to parse or execute a demo recipe.
#[derive(Debug)]
pub enum HolRecipeError {
    /// The recipe does not match the deliberately small grammar.
    InvalidRecipe,
    /// A recipe Boolean must be exactly `true` or `false`.
    InvalidBoolean,
    /// A type constructor was rejected by Nucleus.
    Type(TypeError),
    /// A term constructor was rejected by Nucleus.
    Term(TermError),
    /// A branded proof operation was rejected by Nucleus.
    Proof(ProofError),
}

impl fmt::Display for HolRecipeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRecipe => {
                formatter.write_str("expected `truth`, `reflexivity BOOL`, or `beta BOOL`")
            }
            Self::InvalidBoolean => formatter.write_str("BOOL must be `true` or `false`"),
            Self::Type(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::Proof(error) => error.fmt(formatter),
        }
    }
}

impl StdError for HolRecipeError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::InvalidRecipe | Self::InvalidBoolean => None,
        }
    }
}

impl From<TypeError> for HolRecipeError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<TermError> for HolRecipeError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ProofError> for HolRecipeError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

/// Failure to operate the REPL directory.
#[derive(Debug)]
pub enum ReplError {
    /// The raw state connection could not be opened.
    Open(covalence_neutron::ConnectionError),
    /// The state database rejected an operation.
    State(sqlite::Error),
    /// A requested runtime connection does not exist.
    UnknownConnection(ConnectionId),
    /// A state inspection statement returned no columns.
    StateQueryReturnsNoRows,
    /// No runtime connection is currently selected.
    NoActiveConnection,
}

impl fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(error) => write!(formatter, "could not open REPL state: {error}"),
            Self::State(error) => write!(formatter, "could not access REPL state: {error}"),
            Self::UnknownConnection(id) => write!(formatter, "unknown connection {id}"),
            Self::StateQueryReturnsNoRows => {
                formatter.write_str("state inspection statements must return rows")
            }
            Self::NoActiveConnection => formatter.write_str("no active connection"),
        }
    }
}

impl StdError for ReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Open(error) => Some(error),
            Self::State(error) => Some(error),
            Self::UnknownConnection(_)
            | Self::NoActiveConnection
            | Self::StateQueryReturnsNoRows => None,
        }
    }
}

impl From<covalence_neutron::ConnectionError> for ReplError {
    fn from(error: covalence_neutron::ConnectionError) -> Self {
        Self::Open(error)
    }
}

impl From<sqlite::Error> for ReplError {
    fn from(error: sqlite::Error) -> Self {
        Self::State(error)
    }
}

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
mod web;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub use web::{WebHolOutcome, WebKernel, WebOutcome};

/// Returns the cross-target `SQLite` smoke-test value.
#[must_use]
#[cfg_attr(
    all(target_arch = "wasm32", target_os = "unknown"),
    wasm_bindgen::prelude::wasm_bindgen
)]
pub fn smoke() -> u32 {
    covalence_nucleus::smoke()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orchestrates_two_simultaneous_sql_connections() {
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let first = repl
            .insert("nucleus/sql", kernel.open_sql().unwrap())
            .unwrap();
        let second = repl
            .insert("nucleus/sql", kernel.open_sql().unwrap())
            .unwrap();

        repl.get_mut(first)
            .unwrap()
            .run("CREATE TABLE only_here(x INTEGER)", &[])
            .unwrap();
        let isolated = repl
            .get_mut(second)
            .unwrap()
            .run(
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_here'",
                &[],
            )
            .unwrap();
        assert!(matches!(
            isolated,
            Outcome::Rows(result) if result.rows == [[Value::Integer(0)]]
        ));
        let present = repl
            .get_mut(first)
            .unwrap()
            .run(
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_here'",
                &[],
            )
            .unwrap();
        assert!(matches!(
            present,
            Outcome::Rows(result) if result.rows == [[Value::Integer(1)]]
        ));
    }

    #[test]
    fn inspects_state_read_only() {
        let mut repl = Repl::new(&[9; 32]).unwrap();
        let _ = repl.insert("nucleus/sql", ()).unwrap();

        let result = repl
            .inspect_state("SELECT connection_id, protocol FROM repl_connection")
            .unwrap();
        assert_eq!(result.columns, ["connection_id", "protocol"]);
        assert_eq!(
            result.rows,
            [[Value::Integer(1), Value::Text("nucleus/sql".to_owned())]]
        );

        // Inspection cannot mutate the directory, and ordinary directory
        // updates still work afterwards.
        assert!(repl.inspect_state("DELETE FROM repl_connection").is_err());
        assert!(
            repl.inspect_state("INSERT INTO repl_connection(kernel_id, protocol) VALUES (0, 'x') RETURNING connection_id")
                .is_err()
        );
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        let _ = repl.insert("nucleus/sql", ()).unwrap();
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(2)]]
        );
    }

    #[test]
    fn records_lifecycle_and_selection_in_sqlite() {
        let mut repl = Repl::new(&[7; 32]).unwrap();
        let first = repl.insert("one", String::from("first")).unwrap();
        let second = repl.insert("two", String::from("second")).unwrap();
        assert_eq!(repl.active().unwrap(), Some(first));

        repl.select(second).unwrap();
        assert_eq!(repl.active().unwrap(), Some(second));
        assert_eq!(repl.active_mut().unwrap(), "second");
        assert_eq!(repl.remove(second).unwrap(), "second");
        assert_eq!(repl.active().unwrap(), Some(first));

        let rows = repl
            .state()
            .sqlite()
            .query_row("SELECT count(*) FROM repl_connection", (), |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 1);
        let public_key = repl
            .state()
            .sqlite()
            .query_row(
                "SELECT public_key FROM repl_kernel WHERE kernel_id = 0",
                (),
                |row| row.get::<_, Vec<u8>>(0),
            )
            .unwrap();
        assert_eq!(public_key, vec![7; 32]);
    }

    #[test]
    fn manages_independent_sql_and_hol_connections() {
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let sql = LocalConnection::Sql(kernel.open_sql().unwrap());
        let hol = LocalConnection::Hol(kernel.open_hol(AllowAll).unwrap());
        let sql_id = repl.insert(sql.protocol(), sql).unwrap();
        let hol_id = repl.insert(hol.protocol(), hol).unwrap();

        repl.get_mut(sql_id)
            .unwrap()
            .sql_mut()
            .unwrap()
            .execute_batch("CREATE TABLE only_sql(value INTEGER)")
            .unwrap();
        let result = HolRecipe::Beta(true)
            .execute(repl.get_mut(hol_id).unwrap().hol_mut().unwrap())
            .unwrap();

        assert_eq!(result.kind(), "hol-theorem");
        assert_eq!(result.recipe(), "beta");
        assert_eq!(result.context_id(), 0);
        assert_eq!(result.statement(), "(lambda x:bool. x) true = true");
        assert!(result.conclusion_id() > 0);
        assert!(matches!(
            repl.get_mut(sql_id).unwrap().hol_mut(),
            Err(ConnectionKindError::ExpectedHol)
        ));
        assert!(matches!(
            repl.get_mut(hol_id).unwrap().sql_mut(),
            Err(ConnectionKindError::ExpectedSql)
        ));

        let protocols = repl
            .state()
            .sqlite()
            .prepare("SELECT protocol FROM repl_connection ORDER BY connection_id")
            .unwrap()
            .query_map((), |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(protocols, ["nucleus/sql", "nucleus/hol"]);
    }

    #[test]
    fn recipe_parser_is_intentionally_small() {
        assert_eq!("truth".parse::<HolRecipe>().unwrap(), HolRecipe::Truth);
        assert_eq!(
            "refl false".parse::<HolRecipe>().unwrap(),
            HolRecipe::Reflexivity(false)
        );
        assert_eq!(
            "beta true".parse::<HolRecipe>().unwrap(),
            HolRecipe::Beta(true)
        );
        assert!(matches!(
            "beta maybe".parse::<HolRecipe>(),
            Err(HolRecipeError::InvalidBoolean)
        ));
        assert!(matches!(
            "anything".parse::<HolRecipe>(),
            Err(HolRecipeError::InvalidRecipe)
        ));
    }
}
