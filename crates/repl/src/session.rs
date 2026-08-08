//! The REPL, as a pure function from input to what should happen.
//!
//! This is the whole command surface, and it is shared: every front end runs
//! *this*, not an implementation that resembles it. That is the only way "the
//! browser behaves like the terminal" stays true after the second change to
//! either.
//!
//! # It performs no I/O
//!
//! [`Session::eval`] returns a [`Response`], and a response may be a request:
//! *read this file*. The host does it and hands the result
//! back. That is not ceremony — a browser cannot read a path and cannot block
//! on a socket, and a session that tried to do either itself could not run
//! there. Keeping I/O at the edge is what makes one dispatch serve every
//! front end.
//!
//! # Why an evaluator rather than a dispatcher
//!
//! Commands are [`sexpr::Value`]s in and values out. The store's contents are
//! a list of addresses, not a block of text that happens to have one address
//! per line. See [`sexpr`] for why that is worth the reader it costs.

use covalence_data_cas::MemoryCas;
use covalence_lib_hash::{O256, o256};

use crate::sexpr::{ReadError, Value, read};
use crate::{ConnectionId, Repl, ReplError};

/// What the host should do with a form.
#[derive(Clone, Debug, PartialEq)]
pub enum Response {
    /// Show this value. [`Value::Nil`] means show nothing.
    Value(Value),
    /// Read this file and pass its bytes to [`Session::admit`].
    ///
    /// The session cannot read files: it does not know whether it is running
    /// somewhere that has any.
    ReadFile(String),
    /// Leave.
    Quit,
}

impl Response {
    /// A response carrying a value.
    fn value(value: impl Into<Value>) -> Self {
        Self::Value(value.into())
    }
}

impl From<String> for Value {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<O256> for Value {
    fn from(address: O256) -> Self {
        Self::Address(address)
    }
}

/// Failure to evaluate a form.
#[derive(Debug)]
pub enum SessionError {
    /// The input is not an s-expression.
    Read(ReadError),
    /// No procedure by this name.
    Unbound(String),
    /// A form was applied to the wrong arguments.
    Usage(&'static str),
    /// The argument is not a content address.
    NotAnAddress(Value),
    /// Building a sample database failed.
    Sqlite(covalence_lib_sqlite::Error),
    /// The store or a connection failed.
    Repl(ReplError),
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read(error) => write!(formatter, "{error}"),
            Self::Unbound(name) => write!(formatter, "unbound: {name}; try (help)"),
            Self::Usage(usage) => write!(formatter, "usage: {usage}"),
            Self::NotAnAddress(value) => write!(formatter, "{value} is not an address"),
            Self::Sqlite(error) => write!(formatter, "{error}"),
            Self::Repl(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for SessionError {}

impl From<ReplError> for SessionError {
    fn from(error: ReplError) -> Self {
        Self::Repl(error)
    }
}

impl From<covalence_lib_sqlite::Error> for SessionError {
    fn from(error: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite(error)
    }
}

impl From<ReadError> for SessionError {
    fn from(error: ReadError) -> Self {
        Self::Read(error)
    }
}

/// What `(help)` returns.
pub const HELP: &str = "\
(put \"PATH\")        admit a file into the store; returns its address
(forget ADDRESS)    drop an address from the store
(stats)             how much the store holds
(objects [N])       up to N resident addresses (default 64)
(samples)           admit the sample databases; returns name/address pairs

(open)              open a private in-memory connection
(open ADDRESS)      open a resident object read-only through the mount
(open \"URI\")        open any SQLite URI; ?vfs=cas reaches the store
(connections)       every open connection, as a list
(select N)          select a connection
(close N)           close a connection

(help)              this
(quit)              leave

Every resident object is reachable from inside SQLite:
  ATTACH 'file:<address>?vfs=cas' AS obj;
";

/// How many addresses `(objects)` lists when not told otherwise.
const DEFAULT_OBJECTS: usize = 64;

/// A shipped database, baked into this binary.
pub struct Sample {
    /// What to call it.
    pub name: &'static str,
    /// Where it lives, which is also what it hashes to.
    pub address: O256,
    /// The file, byte for byte.
    pub bytes: &'static [u8],
}

/// Small databases that make an empty store worth typing at.
///
/// Two of them, related, so a join has something to join.
///
/// # Why files rather than SQL run at startup
///
/// Because the address has to be the same everywhere. Building these from SQL
/// would make their addresses depend on whichever `SQLite` did the building --
/// page size, encoding, the version's idea of a freelist -- so the terminal
/// and the page could disagree about what `planets` *is*, which is precisely
/// the thing a content address is supposed to settle.
///
/// The files live in `crates/repl/samples/`, each named by its own address.
/// That is not decoration: a directory of hash-named files is a read-only CAS
/// already, so serving that directory over HTTP is a serviceable minimal
/// kernel with no server code in it at all. `samples_are_named_by_their_own_address`
/// checks the names really are the hashes.
pub const SAMPLES: &[Sample] = &[
    Sample {
        name: "planets",
        address: o256!("63ab97eb43d45274034d43663e5af8a2c15e1fc1008a66cf9dd17640881d9a84"),
        bytes: include_bytes!(
            "../samples/63ab97eb43d45274034d43663e5af8a2c15e1fc1008a66cf9dd17640881d9a84"
        ),
    },
    Sample {
        name: "moons",
        address: o256!("51ac6802cd2c89da48591fefe806d652584fc5af8d127c637634a3a0384b9ea4"),
        bytes: include_bytes!(
            "../samples/51ac6802cd2c89da48591fefe806d652584fc5af8d127c637634a3a0384b9ea4"
        ),
    },
];

/// Narrows a count to the integer type the REPL speaks.
///
/// Saturating rather than failing: these are object and byte counts, and a
/// REPL that refused to answer because a store held more than `i64::MAX`
/// bytes would be solving a problem no one has.
fn count(value: impl TryInto<i64>) -> i64 {
    value.try_into().unwrap_or(i64::MAX)
}

/// A two-element list, which is how this REPL says "name: value".
fn pair(name: &str, value: i64) -> Value {
    Value::List(vec![Value::Symbol(name.to_owned()), Value::Integer(value)])
}

/// One REPL, independent of how its input arrives.
pub struct Session {
    repl: Repl,
}

impl Session {
    /// Creates a session whose store is mounted under the conventional name.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    pub fn new() -> Result<Self, ReplError> {
        Ok(Self { repl: Repl::new()? })
    }

    /// Creates a session whose store is mounted under `name`.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    pub fn with_mount_name(name: &str) -> Result<Self, ReplError> {
        Ok(Self {
            repl: Repl::with_mount_name(name, false)?,
        })
    }

    /// Borrows the underlying REPL.
    #[must_use]
    pub const fn repl(&self) -> &Repl {
        &self.repl
    }

    /// Borrows the underlying REPL mutably, for what the command surface does
    /// not cover.
    pub const fn repl_mut(&mut self) -> &mut Repl {
        &mut self.repl
    }

    /// Borrows the store.
    #[must_use]
    pub fn store(&self) -> &std::sync::Arc<MemoryCas> {
        self.repl.cas()
    }

    /// Admits bytes the host read for a `(put …)`.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes exceed the store's admission limit.
    pub fn admit(&self, bytes: Vec<u8>) -> Result<Value, SessionError> {
        Ok(Value::Address(self.repl.put(bytes)?))
    }

    /// Reads and evaluates every form in `input`, returning the last response.
    ///
    /// A form which asks the host to do something ends the line: the host
    /// must act before the rest can mean anything.
    ///
    /// # Errors
    ///
    /// Returns an error if the input does not read, names nothing, or fails.
    pub fn eval(&mut self, input: &str) -> Result<Response, SessionError> {
        let mut last = Response::Value(Value::Nil);
        for form in read(input)? {
            last = self.eval_form(&form)?;
            if !matches!(last, Response::Value(_)) {
                return Ok(last);
            }
        }
        Ok(last)
    }

    /// Evaluates one form.
    fn eval_form(&mut self, form: &Value) -> Result<Response, SessionError> {
        let Value::List(items) = form else {
            // Everything else is self-evaluating. A bare symbol has nothing to
            // resolve to yet -- there are no variables -- so it stands for
            // itself, which makes `(forget ADDRESS)` and a pasted address
            // behave the same way.
            return Ok(Response::Value(form.clone()));
        };
        let (operator, arguments) = items.split_first().unwrap_or_else(|| {
            unreachable!("Value::list collapses the empty list to Nil, so List is never empty")
        });
        let Some(name) = operator.as_text() else {
            return Err(SessionError::Unbound(operator.to_string()));
        };
        if name == "quote" {
            return match arguments {
                [quoted] => Ok(Response::Value(quoted.clone())),
                _ => Err(SessionError::Usage("(quote FORM)")),
            };
        }
        // Arguments evaluate before application, as in any applicative-order
        // Lisp. Only `Value` responses can be arguments: a nested form that
        // wanted the host would have nothing to hand back here.
        let mut evaluated = Vec::with_capacity(arguments.len());
        for argument in arguments {
            match self.eval_form(argument)? {
                Response::Value(value) => evaluated.push(value),
                other => return Ok(other),
            }
        }
        self.apply(name, &evaluated)
    }

    /// Applies the procedure `name` to already-evaluated arguments.
    ///
    /// A `match` rather than an environment: there is nothing to shadow yet,
    /// and a table of one binding kind would be structure without content.
    /// Growing this into a Scheme means replacing this function, not
    /// unpicking it.
    fn apply(&mut self, name: &str, arguments: &[Value]) -> Result<Response, SessionError> {
        match (name, arguments) {
            ("quit" | "exit", []) => Ok(Response::Quit),
            ("help", []) => Ok(Response::value(HELP.to_owned())),

            ("put", [path]) => path
                .as_text()
                .map(|path| Response::ReadFile(path.to_owned()))
                .ok_or(SessionError::Usage("(put \"PATH\")")),
            ("forget", [value]) => {
                let address = Self::address(value)?;
                Ok(Response::value(Value::Bool(self.repl.forget(address))))
            }
            ("stats", []) => {
                let stats = self.repl.stats();
                Ok(Response::value(Value::List(vec![
                    pair("objects", count(stats.objects)),
                    pair("bytes", count(stats.bytes)),
                    pair("largest", count(stats.largest)),
                ])))
            }
            ("objects", []) => Ok(Response::value(self.objects(DEFAULT_OBJECTS))),
            ("objects", [limit]) => {
                let limit = limit
                    .as_integer()
                    .and_then(|limit| usize::try_from(limit).ok())
                    .ok_or(SessionError::Usage("(objects [N])"))?;
                Ok(Response::value(self.objects(limit)))
            }
            ("samples", []) => self.samples().map(Response::Value),

            ("open", []) => Ok(Response::value(Value::Integer(
                self.repl
                    .open_memory()?
                    .get()
                    .try_into()
                    .unwrap_or(i64::MAX),
            ))),
            ("open", [value]) => {
                let id = match value.as_address() {
                    Some(address) => self.repl.open_address(address)?,
                    None => self.repl.open_uri(
                        value
                            .as_text()
                            .ok_or(SessionError::Usage("(open ADDRESS)"))?,
                    )?,
                };
                Ok(Response::value(Value::Integer(
                    id.get().try_into().unwrap_or(i64::MAX),
                )))
            }
            ("connections", []) => Ok(Response::value(Value::list(
                self.repl
                    .connections()
                    .into_iter()
                    .map(|info| {
                        Value::List(vec![
                            Value::Integer(info.id.get().try_into().unwrap_or(i64::MAX)),
                            Value::Text(info.origin),
                            Value::Bool(info.selected),
                        ])
                    })
                    .collect(),
            ))),
            ("select", [value]) => {
                self.repl.select(Self::connection(value)?)?;
                Ok(Response::value(Value::Nil))
            }
            ("close", [value]) => {
                self.repl.close(Self::connection(value)?)?;
                Ok(Response::value(Value::Nil))
            }

            _ => Err(SessionError::Unbound(name.to_owned())),
        }
    }

    /// Lists at most `limit` resident addresses.
    ///
    /// Bounded because `(stats)` is the question this usually answers, and
    /// because listing is not something a store necessarily *can* do: the
    /// `Cas` contract is `open`, `len`, `read`, and nothing about
    /// enumeration. This works because the store in this process happens to
    /// be an in-memory one that keeps a map. A store backed by S3, or one
    /// composing several sources, has no such list to give -- so nothing
    /// should be built on the assumption that it does.
    fn objects(&self, limit: usize) -> Value {
        Value::list(
            self.repl
                .addresses()
                .into_iter()
                .take(limit)
                .map(Value::Address)
                .collect(),
        )
    }

    /// Admits the shipped sample databases.
    ///
    /// A fresh store is empty, and an empty store gives you nothing to type.
    /// These are real `SQLite` files carried in the binary, so this needs no
    /// filesystem and no network -- which is what lets the page do it too.
    /// Admitting the same bytes twice is the same address, so calling this
    /// again is harmless.
    fn samples(&self) -> Result<Value, SessionError> {
        let mut admitted = Vec::with_capacity(SAMPLES.len());
        for sample in SAMPLES {
            let address = self.repl.put(sample.bytes.to_vec())?;
            admitted.push(Value::List(vec![
                Value::Symbol(sample.name.to_owned()),
                Value::Address(address),
            ]));
        }
        Ok(Value::list(admitted))
    }

    fn address(value: &Value) -> Result<O256, SessionError> {
        value
            .as_address()
            .ok_or_else(|| SessionError::NotAnAddress(value.clone()))
    }

    fn connection(value: &Value) -> Result<ConnectionId, SessionError> {
        value
            .as_integer()
            .and_then(|id| u64::try_from(id).ok())
            .map(ConnectionId::from_raw)
            .ok_or(SessionError::Usage("(select N)"))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use covalence_data_cas::Cas;

    use super::*;

    static NEXT: AtomicU64 = AtomicU64::new(0);

    /// Each session needs a distinct mount name: registration is
    /// process-global and permanent.
    fn session() -> Session {
        let name = format!(
            "covalence-test-session-{}",
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        Session::with_mount_name(&name).expect("mount")
    }

    /// Evaluates and renders, the way a front end would.
    fn say(session: &mut Session, input: &str) -> String {
        match session.eval(input) {
            Ok(Response::Value(value)) => value.to_string(),
            Ok(other) => format!("{other:?}"),
            Err(error) => format!("error: {error}"),
        }
    }

    #[test]
    fn an_empty_store_reports_nothing() {
        let mut session = session();
        assert_eq!(
            say(&mut session, "(stats)"),
            "((objects 0) (bytes 0) (largest 0))"
        );
        assert_eq!(say(&mut session, "(objects)"), "()");
    }

    #[test]
    fn admitting_bytes_returns_an_address_which_then_lists() {
        let mut session = session();
        let address = session.admit(b"hello".to_vec()).expect("admit");
        assert_eq!(say(&mut session, "(objects)"), format!("({address})"));
        assert_eq!(
            say(&mut session, "(stats)"),
            "((objects 1) (bytes 5) (largest 5))"
        );
    }

    #[test]
    fn results_are_data_rather_than_text() {
        let mut session = session();
        session.admit(b"a".to_vec()).expect("admit");
        session.admit(b"bb".to_vec()).expect("admit");
        // Two addresses in one list, which is what a caller can consume.
        let rendered = say(&mut session, "(objects)");
        assert!(
            rendered.starts_with('(') && rendered.ends_with(')'),
            "{rendered}"
        );
        assert_eq!(rendered.split_whitespace().count(), 2, "{rendered}");
    }

    #[test]
    fn an_unbound_name_is_reported_without_stopping() {
        let mut session = session();
        assert!(say(&mut session, "(nope)").contains("unbound: nope"));
        assert_eq!(say(&mut session, "(objects)"), "()");
    }

    #[test]
    fn a_bad_address_is_rejected() {
        let mut session = session();
        assert!(say(&mut session, "(forget not-an-address)").contains("is not an address"));
    }

    #[test]
    fn unreadable_input_is_reported_without_stopping() {
        let mut session = session();
        assert!(say(&mut session, "(stats").contains("unterminated"));
        assert!(say(&mut session, "(stats)").contains("objects"));
    }

    #[test]
    fn connections_open_select_and_close() {
        let mut session = session();
        assert_eq!(say(&mut session, "(open)"), "1");
        assert_eq!(say(&mut session, "(open)"), "2");
        assert_eq!(
            say(&mut session, "(connections)"),
            "((1 \":memory:\" #f) (2 \":memory:\" #t))"
        );
        say(&mut session, "(select 1)");
        assert!(say(&mut session, "(connections)").contains("(1 \":memory:\" #t)"));
        say(&mut session, "(close 1)");
        assert_eq!(say(&mut session, "(connections)"), "((2 \":memory:\" #t))");
    }

    #[test]
    fn put_asks_the_host_to_read_the_file() {
        let mut session = session();
        assert_eq!(
            session.eval(r#"(put "db.sqlite")"#).expect("eval"),
            Response::ReadFile("db.sqlite".to_owned())
        );
    }

    #[test]
    fn samples_are_stored_under_their_own_address() {
        // The filename in `crates/repl/samples/` is the file's own address.
        // That is what makes the directory a CAS rather than a folder of
        // databases -- and therefore what makes serving it over HTTP a
        // kernel. Nothing but a test keeps it true once someone edits a
        // fixture, so this is that test.
        for sample in SAMPLES {
            assert_eq!(
                O256::from_bytes(sample.bytes),
                sample.address,
                "{} is not stored under its own address",
                sample.name
            );
        }
    }

    #[test]
    fn samples_are_real_sqlite_files() {
        for sample in SAMPLES {
            assert_eq!(&sample.bytes[..15], b"SQLite format 3", "{}", sample.name);
        }
    }

    #[test]
    fn samples_admit_real_databases_and_name_them() {
        let mut session = session();
        let rendered = say(&mut session, "(samples)");
        // A list of (name address) pairs, one per sample.
        assert!(rendered.starts_with("((planets "), "{rendered}");
        assert!(rendered.contains("(moons "), "{rendered}");
        assert_eq!(session.repl().stats().objects, 2);

        // Real SQLite images, not placeholder bytes.
        for address in session.repl().addresses() {
            let bytes = session.repl().cas().read(address, 0..16).expect("read");
            assert_eq!(&bytes.expect("resident")[..15], b"SQLite format 3");
        }

        // Admitting them again is the same two addresses: content, not events.
        say(&mut session, "(samples)");
        assert_eq!(session.repl().stats().objects, 2);
    }

    #[test]
    fn objects_is_bounded_and_stats_says_how_much_was_left_out() {
        let mut session = session();
        for byte in 0..5_u8 {
            session.admit(vec![byte]).expect("admit");
        }
        assert_eq!(
            say(&mut session, "(objects 2)").split_whitespace().count(),
            2
        );
        assert_eq!(say(&mut session, "(objects)").split_whitespace().count(), 5);
        // Which is how you find out whether you saw everything.
        assert!(say(&mut session, "(stats)").contains("(objects 5)"));
    }

    #[test]
    fn quote_returns_its_argument_unevaluated() {
        let mut session = session();
        assert_eq!(say(&mut session, "'(cas)"), "(cas)");
    }

    #[test]
    fn several_forms_on_one_line_all_run() {
        let mut session = session();
        assert_eq!(
            say(&mut session, "(open) (open) (connections)")
                .matches('(')
                .count(),
            3
        );
    }

    #[test]
    fn quitting_is_a_response_rather_than_a_value() {
        let mut session = session();
        assert_eq!(session.eval("(quit)").expect("eval"), Response::Quit);
    }
}
