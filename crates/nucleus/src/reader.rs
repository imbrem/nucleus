use covalence_lib_sqlite as sqlite;
use sqlite::hooks::{AuthAction, AuthContext, Authorization};

use crate::{Connection, Invariant};

/// A connection capability restricted to side-effect-free reads.
///
/// A reader is scoped to either one database or one table. `SQLite`'s
/// authorizer validates every statement while it is prepared; statements
/// which mutate connection state or access data outside the scope are denied.
#[derive(Debug)]
pub struct Reader<'connection> {
    connection: &'connection sqlite::Connection,
    scope: Scope,
}

impl<'connection> Reader<'connection> {
    pub(crate) fn database<I: Invariant>(
        connection: &'connection mut Connection<I>,
        database: impl Into<String>,
    ) -> Self {
        Self {
            connection: connection.sqlite(),
            scope: Scope::Database(database.into()),
        }
    }

    pub(crate) fn table<I: Invariant>(
        connection: &'connection mut Connection<I>,
        database: impl Into<String>,
        table: impl Into<String>,
    ) -> Self {
        Self {
            connection: connection.sqlite(),
            scope: Scope::Table {
                database: database.into(),
                table: table.into(),
            },
        }
    }

    /// Runs one read-only query and gives its rows to `read`.
    ///
    /// The callback cannot access the underlying connection. The statement is
    /// discarded before this reader may prepare another one.
    ///
    /// # Errors
    ///
    /// Returns an `SQLite` error if the statement is not a read, reaches outside
    /// this reader's scope, cannot be prepared, or fails while executing.
    pub fn query<P, T>(
        &mut self,
        sql: &str,
        params: P,
        read: impl FnOnce(&mut sqlite::Rows<'_>) -> sqlite::Result<T>,
    ) -> sqlite::Result<T>
    where
        P: sqlite::Params,
    {
        let authorizer = Authorizer::install(self.connection, self.scope.clone())?;
        let mut statement = authorizer.prepare(sql)?;
        let mut rows = statement.query(params)?;
        read(&mut rows)
    }

    /// Runs one read-only query which must return exactly one mapped row.
    ///
    /// # Errors
    ///
    /// Returns an `SQLite` error if the statement is not a read, reaches outside
    /// this reader's scope, cannot be prepared, or does not produce the
    /// requested row.
    pub fn query_row<P, T>(
        &mut self,
        sql: &str,
        params: P,
        map: impl FnOnce(&sqlite::Row<'_>) -> sqlite::Result<T>,
    ) -> sqlite::Result<T>
    where
        P: sqlite::Params,
    {
        let authorizer = Authorizer::install(self.connection, self.scope.clone())?;
        let mut statement = authorizer.prepare(sql)?;
        statement.query_row(params, map)
    }
}

#[derive(Clone, Debug)]
enum Scope {
    Database(String),
    Table { database: String, table: String },
}

impl Scope {
    fn authorizes(&self, context: AuthContext<'_>) -> Authorization {
        match context.action {
            AuthAction::Select | AuthAction::Recursive => Authorization::Allow,
            AuthAction::Read { table_name, .. } => {
                if self.contains(context.database_name, table_name, context.accessor) {
                    Authorization::Allow
                } else {
                    Authorization::Deny
                }
            }
            // Nucleus does not expose SQLite function registration or extension
            // loading. Built-in scalar and aggregate functions therefore cannot
            // mutate host or connection state through the safe API.
            AuthAction::Function { function_name }
                if !function_name.eq_ignore_ascii_case("load_extension") =>
            {
                Authorization::Allow
            }
            _ => Authorization::Deny,
        }
    }

    fn contains(
        &self,
        database_name: Option<&str>,
        table_name: &str,
        accessor: Option<&str>,
    ) -> bool {
        let Some(database_name) = database_name else {
            return false;
        };

        match self {
            Self::Database(database) => database.eq_ignore_ascii_case(database_name),
            Self::Table { database, table } => {
                database.eq_ignore_ascii_case(database_name)
                    && (table.eq_ignore_ascii_case(table_name)
                        || accessor.is_some_and(|accessor| table.eq_ignore_ascii_case(accessor)))
            }
        }
    }
}

struct Authorizer<'connection> {
    connection: &'connection sqlite::Connection,
}

impl<'connection> Authorizer<'connection> {
    fn install(connection: &'connection sqlite::Connection, scope: Scope) -> sqlite::Result<Self> {
        connection.authorizer(Some(move |context: AuthContext<'_>| {
            scope.authorizes(context)
        }))?;
        Ok(Self { connection })
    }

    fn prepare(&self, sql: &str) -> sqlite::Result<sqlite::Statement<'_>> {
        self.connection.prepare(sql)
    }
}

impl Drop for Authorizer<'_> {
    fn drop(&mut self) {
        let _ = self
            .connection
            .authorizer(None::<fn(AuthContext<'_>) -> Authorization>);
    }
}

impl<I: Invariant> Connection<I> {
    /// Restricts reads to one attached database.
    #[must_use]
    pub fn database_reader(&mut self, database: impl Into<String>) -> Reader<'_> {
        Reader::database(self, database)
    }

    /// Restricts reads to one table in an attached database.
    #[must_use]
    pub fn table_reader(
        &mut self,
        database: impl Into<String>,
        table: impl Into<String>,
    ) -> Reader<'_> {
        Reader::table(self, database, table)
    }
}
