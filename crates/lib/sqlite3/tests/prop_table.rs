//! A prop table as one owned prepared statement per operation.
//!
//! A prop table is a fact relation plus a deduction rule per inference, each
//! expressed as SQL. The natural Rust shape is a struct that owns the
//! connection and holds one prepared statement per rule for the life of the
//! table: prepared once, stepped many times, owned outright.
//!
//! `rusqlite` cannot express that shape. Its `Statement<'conn>` borrows the
//! `Connection`, so a struct holding both is self-referential; the alternatives
//! are re-preparing from SQL text on every call or handing the statements to
//! `rusqlite`'s own statement cache. Here the statements are plain fields.

use covalence_lib_sqlite3::{Connection, Statement, Step, ValueRef};

const SCHEMA: &str = "
    CREATE TABLE atom (id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
    CREATE TABLE below (lesser INTEGER NOT NULL, greater INTEGER NOT NULL,
                        PRIMARY KEY (lesser, greater)) WITHOUT ROWID;
    CREATE TABLE clause (id INTEGER PRIMARY KEY, width INTEGER NOT NULL);
    CREATE TABLE literal (clause INTEGER NOT NULL, atom INTEGER NOT NULL,
                          sign INTEGER NOT NULL, PRIMARY KEY (clause, atom))
                          WITHOUT ROWID;
    CREATE TABLE assigned (atom INTEGER PRIMARY KEY, sign INTEGER NOT NULL);
";

/// A prop table: the facts, and one prepared statement per rule.
///
/// No lifetime parameter, no self-reference, no statement cache.
struct PropTable {
    connection: Connection,
    /// `INSERT` a new atom, returning its id.
    intern_atom: Statement,
    /// `INSERT` a base fact into the order relation.
    assert_below: Statement,
    /// Transitivity: close `below` under composition, once.
    close_transitively: Statement,
    /// Unit propagation: assign the last unassigned literal of a clause.
    propagate_units: Statement,
    /// Read back the assignment of one atom.
    assignment_of: Statement,
}

impl PropTable {
    fn new() -> Self {
        let connection = Connection::open_in_memory().expect("open");
        connection.execute_batch(SCHEMA).expect("install schema");
        Self {
            intern_atom: connection
                .prepare("INSERT INTO atom (name) VALUES (?1) RETURNING id")
                .expect("prepare intern_atom"),
            assert_below: connection
                .prepare("INSERT OR IGNORE INTO below (lesser, greater) VALUES (?1, ?2)")
                .expect("prepare assert_below"),
            close_transitively: connection
                .prepare(
                    "INSERT OR IGNORE INTO below (lesser, greater)
                     SELECT left.lesser, right.greater
                     FROM below AS left JOIN below AS right
                       ON left.greater = right.lesser",
                )
                .expect("prepare close_transitively"),
            propagate_units: connection
                .prepare(
                    "INSERT OR IGNORE INTO assigned (atom, sign)
                     SELECT open.atom, open.sign
                     FROM literal AS open
                     JOIN clause ON clause.id = open.clause
                     WHERE open.atom NOT IN (SELECT atom FROM assigned)
                       AND clause.width - 1 = (
                             SELECT count(*) FROM literal AS other
                             JOIN assigned ON assigned.atom = other.atom
                                          AND assigned.sign <> other.sign
                             WHERE other.clause = clause.id)",
                )
                .expect("prepare propagate_units"),
            assignment_of: connection
                .prepare("SELECT sign FROM assigned WHERE atom = ?1")
                .expect("prepare assignment_of"),
            connection,
        }
    }

    /// Runs a statement to completion and reports how many rows it changed.
    fn run(connection: &Connection, statement: &mut Statement) -> i64 {
        while statement.step().expect("step") == Step::Row {}
        let changed = connection.changes();
        statement.reset().expect("reset");
        changed
    }

    fn intern(&mut self, name: &str) -> i64 {
        self.intern_atom.bind_text(1, name).expect("bind name");
        assert_eq!(self.intern_atom.step().expect("step"), Step::Row);
        let id = self.intern_atom.column(0).as_integer().expect("id column");
        assert_eq!(self.intern_atom.step().expect("step"), Step::Done);
        self.intern_atom.reset().expect("reset");
        id
    }

    fn assert_below(&mut self, lesser: i64, greater: i64) {
        self.assert_below.bind_integer(1, lesser).expect("bind");
        self.assert_below.bind_integer(2, greater).expect("bind");
        Self::run(&self.connection, &mut self.assert_below);
    }

    /// Applies transitivity until it stops producing new facts.
    fn saturate(&mut self) -> usize {
        let mut rounds = 0;
        while Self::run(&self.connection, &mut self.close_transitively) > 0 {
            rounds += 1;
            assert!(rounds < 64, "transitive closure did not converge");
        }
        rounds
    }

    fn propagate(&mut self) -> usize {
        let mut rounds = 0;
        while Self::run(&self.connection, &mut self.propagate_units) > 0 {
            rounds += 1;
            assert!(rounds < 64, "unit propagation did not converge");
        }
        rounds
    }

    fn assignment(&mut self, atom: i64) -> Option<i64> {
        self.assignment_of.bind_integer(1, atom).expect("bind");
        let value = match self.assignment_of.step().expect("step") {
            Step::Row => self.assignment_of.column(0).as_integer(),
            Step::Done => None,
        };
        self.assignment_of.reset().expect("reset");
        value
    }

    fn below_count(&self) -> i64 {
        let mut count = self
            .connection
            .prepare("SELECT count(*) FROM below")
            .expect("prepare count");
        assert_eq!(count.step().expect("step"), Step::Row);
        count.column(0).as_integer().expect("count")
    }
}

#[test]
fn transitivity_saturates_a_chain() {
    let mut table = PropTable::new();
    let atoms: Vec<_> = ["a", "b", "c", "d"]
        .into_iter()
        .map(|name| table.intern(name))
        .collect();
    for pair in atoms.windows(2) {
        table.assert_below(pair[0], pair[1]);
    }

    assert_eq!(table.below_count(), 3);
    assert!(table.saturate() > 0);
    // The transitive closure of a 4-chain has 3 + 2 + 1 = 6 edges.
    assert_eq!(table.below_count(), 6);
    // Saturation is idempotent.
    assert_eq!(table.saturate(), 0);
    assert_eq!(table.below_count(), 6);
}

#[test]
fn unit_propagation_runs_to_fixpoint() {
    let mut table = PropTable::new();
    let p = table.intern("p");
    let q = table.intern("q");
    let r = table.intern("r");

    // (p), (~p | q), (~q | r)
    table
        .connection
        .execute_batch(
            "INSERT INTO clause (id, width) VALUES (1, 1), (2, 2), (3, 2);
             INSERT INTO literal (clause, atom, sign) VALUES
               (1, 1, 1), (2, 1, 0), (2, 2, 1), (3, 2, 0), (3, 3, 1);",
        )
        .expect("seed clauses");

    assert!(table.propagate() >= 3);
    assert_eq!(table.assignment(p), Some(1));
    assert_eq!(table.assignment(q), Some(1));
    assert_eq!(table.assignment(r), Some(1));
}

#[test]
fn the_rules_outlive_the_connection_value() {
    let mut table = PropTable::new();
    let a = table.intern("a");
    let b = table.intern("b");
    table.assert_below(a, b);

    // Drop the connection field while every rule statement is still live.
    let PropTable {
        connection,
        mut assert_below,
        ..
    } = table;
    drop(connection);

    // The statement still owns the handle, so the rule still runs.
    assert_below.bind_integer(1, b).expect("bind");
    assert_below.bind_integer(2, a).expect("bind");
    assert_eq!(assert_below.step().expect("step"), Step::Done);
    assert_eq!(assert_below.connection().changes(), 1);
}

#[test]
fn every_storage_class_round_trips() {
    let connection = Connection::open_in_memory().expect("open");
    connection
        .execute_batch("CREATE TABLE cell (slot INTEGER PRIMARY KEY, value)")
        .expect("schema");

    let mut insert = connection
        .prepare("INSERT INTO cell (slot, value) VALUES (?1, ?2)")
        .expect("prepare insert");
    for (slot, value) in [
        ValueRef::Null,
        ValueRef::Integer(-7),
        ValueRef::Real(0.5),
        ValueRef::Text(b"nucleus"),
        ValueRef::Blob(&[0x00, 0xff, 0x7f]),
    ]
    .into_iter()
    .enumerate()
    {
        insert
            .bind_integer(1, i64::try_from(slot).expect("slot fits"))
            .expect("bind slot");
        insert.bind(2, value).expect("bind value");
        assert_eq!(insert.step().expect("step"), Step::Done);
        insert.reset().expect("reset");
    }

    let mut select = connection
        .prepare("SELECT value FROM cell ORDER BY slot")
        .expect("prepare select");
    let mut read = Vec::new();
    while select.step().expect("step") == Step::Row {
        read.push(match select.column(0) {
            ValueRef::Text(bytes) => ValueRef::Text(bytes).as_str().map(str::to_owned),
            other => Some(format!("{other:?}")),
        });
    }
    assert_eq!(
        read,
        vec![
            Some("Null".to_owned()),
            Some("Integer(-7)".to_owned()),
            Some("Real(0.5)".to_owned()),
            Some("nucleus".to_owned()),
            Some("Blob([0, 255, 127])".to_owned()),
        ]
    );
}

#[test]
fn a_failed_step_leaves_the_transaction_for_the_caller_to_settle() {
    let connection = Connection::open_in_memory().expect("open");
    connection
        .execute_batch("CREATE TABLE unique_fact (value INTEGER PRIMARY KEY)")
        .expect("schema");

    let mut insert = connection
        .prepare("INSERT INTO unique_fact (value) VALUES (?1)")
        .expect("prepare");

    connection.execute_batch("BEGIN").expect("begin");
    insert.bind_integer(1, 1).expect("bind");
    assert_eq!(insert.step().expect("step"), Step::Done);
    insert.reset().expect("reset");

    // The same key again: SQLite reports the constraint violation and the
    // transaction is still open, so atomicity is the caller's to decide.
    insert.bind_integer(1, 1).expect("bind");
    let error = insert.step().expect_err("duplicate key");
    assert!(error.message().is_some_and(|text| text.contains("UNIQUE")));
    insert.reset().expect_err("reset reports the same failure");
    connection.execute_batch("ROLLBACK").expect("rollback");

    let mut count = connection
        .prepare("SELECT count(*) FROM unique_fact")
        .expect("prepare count");
    assert_eq!(count.step().expect("step"), Step::Row);
    assert_eq!(count.column(0).as_integer(), Some(0));
}
