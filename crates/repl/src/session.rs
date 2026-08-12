//! Host-independent REPL evaluation.
//!
//! I/O is returned as a [`Response`] for the terminal or browser to perform.

use covalence_data_cas::MemoryCas;
use covalence_lib_hash::{O256, o256};

use crate::sat::{self, State as SatState};
use crate::sexpr::{ReadError, Value, read};
use crate::{ConnectionId, Repl, ReplError};

/// Where a kernel is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Endpoint {
    /// The store inside this process.
    Local,
    /// A kernel reachable over HTTP, by base URL.
    Http(String),
}

impl std::fmt::Display for Endpoint {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Local => formatter.write_str("local"),
            Self::Http(url) => formatter.write_str(url),
        }
    }
}

/// What the host should do with a form.
#[derive(Clone, Debug, PartialEq)]
pub enum Response {
    /// Show this value. [`Value::Unspecified`] means show nothing.
    Value(Value),
    /// Ask the host to read a file for [`Session::admit`].
    ReadFile(String),
    /// Fetch this URL and pass its bytes to [`Session::admit_verified`].
    Fetch {
        /// Where the bytes might be.
        url: String,
        /// What they must hash to.
        address: O256,
    },
    /// Ask the host to run the `SQLite` shell.
    Shell(Vec<String>),
    /// Ask the host's completely untrusted SAT provider to solve a problem.
    Solve(covalence_logic_sat::continuation::SolveRequest),
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
    /// No kernel carries this handle.
    UnknownKernel(i64),
    /// The command needs a kernel of a different kind.
    WrongKernel(&'static str),
    /// Bytes did not hash to the address they were asked for.
    NotWhatWasAskedFor {
        /// The address requested.
        expected: O256,
        /// What arrived instead.
        actual: O256,
    },
    /// The store or a connection failed.
    Repl(ReplError),
    /// A SAT demo, checker, or continuation operation failed.
    Sat(sat::Error),
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read(error) => write!(formatter, "{error}"),
            Self::Unbound(name) => write!(formatter, "unbound: {name}; try (help)"),
            Self::Usage(usage) => write!(formatter, "usage: {usage}"),
            Self::NotAnAddress(value) => write!(formatter, "{value} is not an address"),
            Self::Sqlite(error) => write!(formatter, "{error}"),
            Self::UnknownKernel(id) => write!(formatter, "no kernel {id}"),
            Self::WrongKernel(message) => formatter.write_str(message),
            Self::NotWhatWasAskedFor { expected, actual } => write!(
                formatter,
                "content does not match its address: asked for {}, received {}",
                expected.hex(),
                actual.hex()
            ),
            Self::Repl(error) => write!(formatter, "{error}"),
            Self::Sat(error) => write!(formatter, "{error}"),
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

impl From<sat::Error> for SessionError {
    fn from(error: sat::Error) -> Self {
        Self::Sat(error)
    }
}

/// What `(help)` returns.
pub const HELP: &str = "\
(put \"PATH\")        admit a file into the store; returns its address
(forget ADDRESS)    drop an address from the store
(stats)             how much the store holds
(objects [N])       up to N resident addresses (default 64)
(samples)           admit the sample databases; returns name/address pairs

(kernels)           every known kernel, as a list
(connect \"URL\")     add an HTTP kernel and select it
(kernel N)          select a kernel; (kernel) reports the current one
(local)             select the kernel inside this process
(fetch ADDRESS)     pull an object from the selected kernel and verify it

(open)              open a private in-memory connection
(open ADDRESS)      open a resident object read-only through the mount
(open \"URI\")        open any SQLite URI; ?vfs=cas reaches the store
(connections)       every open connection, as a list
(select N)          select a connection
(close N)           close a connection

(sqlite)            hand the terminal to the real SQLite shell
(sqlite ADDRESS)    ... with that object already open
(sqlite ADDRESS \"SELECT 1\")
                    ... and run that instead of prompting

(sat-demos)         list reusable circuit problems
(sat-get NAME)      describe a named problem
(sat-show NAME)     show its canonical DIMACS
(sat-select NAME)   select a named problem
(sat-set \"DIMACS\")  select a custom DIMACS problem
(sat-problem)       inspect the active problem and identity
(sat-dimacs)        show the exact solver input
(sat-solve)         ask the host's untrusted solver
(sat-verify)        inspect the locally checked result
(sat-model)         show the checked model
(sat-proof)         inspect binary LRAT and admitted judgement metadata
(sat-proof-text)    explicitly render binary LRAT as diagnostic ASCII

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
    /// Kernel 0 is always the one this session is running inside.
    endpoints: Vec<Endpoint>,
    selected: usize,
    sat: SatState,
}

impl Session {
    /// Creates a session whose store is mounted under the conventional name.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    pub fn new() -> Result<Self, ReplError> {
        Ok(Self::over(Repl::new()?))
    }

    /// Creates a session whose store is mounted under `name`.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    pub fn with_mount_name(name: &str) -> Result<Self, ReplError> {
        Ok(Self::over(Repl::with_mount_name(name, false)?))
    }

    fn over(repl: Repl) -> Self {
        Self {
            repl,
            endpoints: vec![Endpoint::Local],
            selected: 0,
            sat: SatState::new(),
        }
    }

    /// Returns the selected kernel.
    #[must_use]
    pub fn endpoint(&self) -> &Endpoint {
        &self.endpoints[self.selected]
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

    /// Admits bytes the host fetched, refusing any that do not match.
    ///
    /// This is what makes a remote kernel usable without trusting it. The URL
    /// says where bytes might be; the address says whether they are the right
    /// ones.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes hash to something else, or exceed the
    /// admission limit.
    pub fn admit_verified(&self, expected: O256, bytes: Vec<u8>) -> Result<Value, SessionError> {
        let actual = O256::from_bytes(&bytes);
        if actual != expected {
            return Err(SessionError::NotWhatWasAskedFor { expected, actual });
        }
        self.admit(bytes)
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
        let mut last = Response::Value(Value::Unspecified);
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
        // Grouped by what they act on, because that is how they are learned.
        // Each group answers `None` for a name it does not have, so "unbound"
        // is decided in exactly one place.
        if let Some(response) = self.store_form(name, arguments)? {
            return Ok(response);
        }
        if let Some(response) = self.connection_form(name, arguments)? {
            return Ok(response);
        }
        if let Some(response) = self.kernel_form(name, arguments)? {
            return Ok(response);
        }
        if let Some(response) = self.sat_form(name, arguments)? {
            return Ok(response);
        }
        match (name, arguments) {
            ("quit" | "exit", []) => Ok(Response::Quit),
            ("help", []) => Ok(Response::value(HELP.to_owned())),
            ("sqlite", _) => Ok(Response::Shell(self.shell_arguments(arguments)?)),
            _ => Err(SessionError::Unbound(name.to_owned())),
        }
    }

    fn sat_form(
        &mut self,
        name: &str,
        arguments: &[Value],
    ) -> Result<Option<Response>, SessionError> {
        Ok(Some(match (name, arguments) {
            ("sat-demos", []) => Response::value(Value::list(
                sat::DEMOS
                    .iter()
                    .map(|demo| {
                        Value::List(vec![
                            Value::Symbol(demo.name.to_owned()),
                            Value::Text(demo.description.to_owned()),
                        ])
                    })
                    .collect(),
            )),
            ("sat-get", [name]) => {
                let name = name
                    .as_text()
                    .ok_or(SessionError::Usage("(sat-get NAME)"))?;
                let demo = sat::DEMOS
                    .iter()
                    .find(|demo| demo.name == name)
                    .ok_or_else(|| sat::Error::UnknownDemo(name.to_owned()))?;
                Response::value(format!("{} — {}", demo.name, demo.description))
            }
            ("sat-show", [name]) => {
                let name = name
                    .as_text()
                    .ok_or(SessionError::Usage("(sat-show NAME)"))?;
                let cnf = SatState::demo_cnf(name)?;
                Response::value(String::from_utf8_lossy(cnf.dimacs()).into_owned())
            }
            ("sat-select", [name]) => {
                self.sat.select_demo(
                    name.as_text()
                        .ok_or(SessionError::Usage("(sat-select NAME)"))?,
                )?;
                Response::value(self.sat.active_summary()?)
            }
            ("sat-set", [text]) => {
                self.sat.set_dimacs(
                    text.as_text()
                        .ok_or(SessionError::Usage("(sat-set \"DIMACS\")"))?,
                )?;
                Response::value(self.sat.active_summary()?)
            }
            ("sat-problem", []) => Response::value(self.sat.active_summary()?),
            ("sat-id", []) => Response::value(self.sat.problem_id()?),
            ("sat-dimacs", []) => Response::value(self.sat.dimacs()?),
            ("sat-solve", []) => Response::Solve(self.sat.begin()?),
            ("sat-verify" | "sat-result" | "sat-checked", []) => {
                Response::value(self.sat.result_summary()?)
            }
            ("sat-model", []) => Response::value(self.sat.model()?),
            ("sat-proof", []) => Response::value(self.sat.proof_metadata()?),
            ("sat-proof-text", []) => Response::value(self.sat.proof_text()?),
            _ if name.starts_with("sat-") => {
                return Err(SessionError::Usage(
                    "(sat-demos), (sat-get NAME), (sat-show NAME), (sat-select NAME), (sat-set \"DIMACS\"), (sat-problem), (sat-dimacs), (sat-solve), or (sat-verify)",
                ));
            }
            _ => return Ok(None),
        }))
    }

    /// Completes the current SAT provider continuation and checks its claim.
    ///
    /// # Errors
    ///
    /// Rejects stale jobs, wrong problems, malformed models, invalid LRAT, or
    /// obsolete proposition snapshots.
    pub fn complete_sat(
        &mut self,
        job: covalence_logic_sat::continuation::JobId,
        result: covalence_logic_sat::continuation::SolveResult,
    ) -> Result<Value, SessionError> {
        self.sat.complete(job, result)?;
        Ok(Value::Text(self.sat.result_summary()?))
    }

    /// Forms acting on the content-addressed store.
    fn store_form(
        &self,
        name: &str,
        arguments: &[Value],
    ) -> Result<Option<Response>, SessionError> {
        Ok(Some(match (name, arguments) {
            ("put", [path]) => Response::ReadFile(
                path.as_text()
                    .ok_or(SessionError::Usage("(put \"PATH\")"))?
                    .to_owned(),
            ),
            ("forget", [value]) => {
                Response::value(Value::Bool(self.repl.forget(Self::address(value)?)))
            }
            ("stats", []) => {
                let stats = self.repl.stats();
                Response::value(Value::List(vec![
                    pair("objects", count(stats.objects)),
                    pair("bytes", count(stats.bytes)),
                    pair("largest", count(stats.largest)),
                ]))
            }
            ("objects", []) => Response::value(self.objects(DEFAULT_OBJECTS)),
            ("objects", [limit]) => Response::value(
                self.objects(
                    limit
                        .as_integer()
                        .and_then(|limit| usize::try_from(limit).ok())
                        .ok_or(SessionError::Usage("(objects [N])"))?,
                ),
            ),
            ("samples", []) => Response::Value(self.samples()?),
            _ => return Ok(None),
        }))
    }

    /// Forms acting on open connections.
    fn connection_form(
        &mut self,
        name: &str,
        arguments: &[Value],
    ) -> Result<Option<Response>, SessionError> {
        Ok(Some(match (name, arguments) {
            ("open", []) => Response::value(Value::Integer(count(self.repl.open_memory()?.get()))),
            ("open", [value]) => {
                let id = match value.as_address() {
                    Some(address) => self.repl.open_address(address)?,
                    None => self.repl.open_uri(
                        value
                            .as_text()
                            .ok_or(SessionError::Usage("(open ADDRESS)"))?,
                    )?,
                };
                Response::value(Value::Integer(count(id.get())))
            }
            ("connections", []) => Response::value(Value::list(
                self.repl
                    .connections()
                    .into_iter()
                    .map(|info| {
                        Value::List(vec![
                            Value::Integer(count(info.id.get())),
                            Value::Text(info.origin),
                            Value::Bool(info.selected),
                        ])
                    })
                    .collect(),
            )),
            ("select", [value]) => {
                self.repl.select(Self::connection(value)?)?;
                Response::value(Value::Unspecified)
            }
            ("close", [value]) => {
                self.repl.close(Self::connection(value)?)?;
                Response::value(Value::Unspecified)
            }
            _ => return Ok(None),
        }))
    }

    /// Forms acting on kernels.
    fn kernel_form(
        &mut self,
        name: &str,
        arguments: &[Value],
    ) -> Result<Option<Response>, SessionError> {
        Ok(Some(match (name, arguments) {
            ("kernels", []) => Response::value(Value::list(
                self.endpoints
                    .iter()
                    .enumerate()
                    .map(|(id, endpoint)| {
                        Value::List(vec![
                            Value::Integer(count(id)),
                            Value::Text(endpoint.to_string()),
                            Value::Bool(id == self.selected),
                        ])
                    })
                    .collect(),
            )),
            ("connect", [url]) => self.connect(url)?,
            ("local", []) => {
                self.selected = 0;
                Response::value(Value::Integer(0))
            }
            ("kernel", []) => Response::value(Value::Integer(count(self.selected))),
            ("kernel", [value]) => {
                let id = value
                    .as_integer()
                    .ok_or(SessionError::Usage("(kernel N)"))?;
                let index = usize::try_from(id).map_err(|_| SessionError::UnknownKernel(id))?;
                if index >= self.endpoints.len() {
                    return Err(SessionError::UnknownKernel(id));
                }
                self.selected = index;
                Response::value(Value::Integer(id))
            }
            ("fetch", [value]) => {
                let address = Self::address(value)?;
                match self.endpoint() {
                    // Fetching from the store you are already inside is not a
                    // fetch; saying so is more use than silently succeeding.
                    Endpoint::Local => {
                        return Err(SessionError::WrongKernel(
                            "the local kernel is already here; (connect \"URL\") to a remote one first",
                        ));
                    }
                    Endpoint::Http(base) => Response::Fetch {
                        url: format!("{}/cas/{}", base.trim_end_matches('/'), address.hex()),
                        address,
                    },
                }
            }
            _ => return Ok(None),
        }))
    }

    /// Records a kernel and selects it.
    ///
    /// Nothing is contacted here. A URL that does not answer is discovered by
    /// the first `(fetch …)`, which is where the error belongs: connecting is
    /// not a claim that anything is listening.
    fn connect(&mut self, url: &Value) -> Result<Response, SessionError> {
        let url = url
            .as_text()
            .filter(|url| url.starts_with("http://") || url.starts_with("https://"))
            .ok_or(SessionError::Usage("(connect \"http://…\")"))?;
        let endpoint = Endpoint::Http(url.to_owned());
        let id = self
            .endpoints
            .iter()
            .position(|known| *known == endpoint)
            .unwrap_or_else(|| {
                self.endpoints.push(endpoint);
                self.endpoints.len() - 1
            });
        self.selected = id;
        Ok(Response::value(Value::Integer(
            i64::try_from(id).unwrap_or(i64::MAX),
        )))
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

    /// Turns arguments into a shell command line.
    ///
    /// A bare address becomes the URI which opens it, because typing the full
    /// `file:…?vfs=cas` form every time is friction with no upside.
    fn shell_arguments(&self, arguments: &[Value]) -> Result<Vec<String>, SessionError> {
        arguments
            .iter()
            .map(|argument| match argument.as_address() {
                Some(address) => Ok(self.repl.uri(address)),
                None => argument
                    .as_text()
                    .map(str::to_owned)
                    .ok_or(SessionError::Usage("(sqlite [ADDRESS | \"ARG\"]...)")),
            })
            .collect()
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
    fn a_bare_sqlite_form_asks_for_an_interactive_shell() {
        let mut session = session();
        assert_eq!(
            session.eval("(sqlite)").expect("eval"),
            Response::Shell(Vec::new())
        );
    }

    #[test]
    fn sqlite_expands_an_address_and_passes_strings_through() {
        let mut session = session();
        let Value::Address(address) = session.admit(b"x".to_vec()).expect("admit") else {
            unreachable!("admit returns an address")
        };
        let Response::Shell(arguments) = session
            .eval(&format!(r#"(sqlite {address} "SELECT * FROM t")"#))
            .expect("eval")
        else {
            panic!("expected a shell response")
        };
        assert_eq!(arguments.len(), 2);
        assert!(
            arguments[0].contains(&address.hex().to_string()),
            "{arguments:?}"
        );
        assert!(arguments[0].contains("vfs="), "{arguments:?}");
        // A string with spaces arrives as one argument, with no splitter.
        assert_eq!(arguments[1], "SELECT * FROM t");
    }

    #[test]
    fn the_local_kernel_is_always_kernel_zero() {
        let mut session = session();
        assert_eq!(say(&mut session, "(kernels)"), "((0 \"local\" #t))");
        assert_eq!(say(&mut session, "(kernel)"), "0");
    }

    #[test]
    fn connecting_adds_a_kernel_and_selects_it() {
        let mut session = session();
        assert_eq!(
            say(&mut session, "(connect \"http://127.0.0.1:8080\")"),
            "1"
        );
        assert!(say(&mut session, "(kernels)").contains("(1 \"http://127.0.0.1:8080\" #t)"));
        // Connecting twice to the same place selects it rather than listing it
        // twice.
        assert_eq!(
            say(&mut session, "(connect \"http://127.0.0.1:8080\")"),
            "1"
        );
        assert_eq!(say(&mut session, "(kernels)").matches("http").count(), 1);
        assert_eq!(say(&mut session, "(local)"), "0");
    }

    #[test]
    fn a_url_that_is_not_a_url_is_refused() {
        let mut session = session();
        assert!(say(&mut session, "(connect \"ftp://nope\")").contains("usage"));
        assert!(say(&mut session, "(kernel 7)").contains("no kernel 7"));
    }

    #[test]
    fn fetching_asks_the_host_for_the_selected_kernels_url() {
        let mut session = session();
        // Nothing to fetch from the store you are standing in.
        assert!(
            say(
                &mut session,
                "(fetch 0000000000000000000000000000000000000000000000000000000000000000)"
            )
            .contains("already here")
        );
        say(&mut session, "(connect \"http://example.invalid/\")");
        let Response::Fetch { url, address } = session
            .eval("(fetch 0000000000000000000000000000000000000000000000000000000000000000)")
            .expect("eval")
        else {
            panic!("expected a fetch")
        };
        assert_eq!(url, format!("http://example.invalid/cas/{}", address.hex()));
    }

    #[test]
    fn fetched_bytes_are_checked_against_the_address_that_was_asked_for() {
        let session = session();
        let expected = O256::from_bytes(b"the real thing");
        let error = session
            .admit_verified(expected, b"something else".to_vec())
            .expect_err("mismatch");
        assert!(error.to_string().contains("does not match its address"));
        // And the impostor is not in the store.
        assert_eq!(session.repl().stats().objects, 0);
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
    fn sat_catalog_and_custom_problem_are_inspectable_and_checked() {
        use covalence_logic_sat::continuation::SolveResult;

        let mut session = session();
        let demos = say(&mut session, "(sat-demos)");
        assert!(demos.contains("and-sat"));
        assert!(demos.contains("half-adder-unsat"));
        assert!(demos.contains("full-adder-sat"));
        assert!(say(&mut session, "(sat-show and-sat)").contains("p cnf 3 6"));

        let selected = say(&mut session, "(sat-set \"p cnf 1 1\\n1 0\\n\")");
        assert!(selected.contains("custom"), "{selected}");
        assert!(say(&mut session, "(sat-problem)").contains("problem="));
        assert!(say(&mut session, "(sat-dimacs)").contains("p cnf 3"));

        let Response::Solve(request) = session.eval("(sat-solve)").expect("solve request") else {
            panic!("expected solve request");
        };
        let status = session
            .complete_sat(
                request.job(),
                SolveResult::Sat {
                    problem: request.problem(),
                    model: vec![1, -2, 3].into_boxed_slice(),
                },
            )
            .expect("checked model")
            .display();
        assert!(status.contains("checked-model"), "{status}");
        assert_eq!(say(&mut session, "(sat-model)"), "\"1 -2 3\"");
    }

    #[test]
    fn invalid_solver_claim_is_consumed_without_authority() {
        use covalence_logic_sat::continuation::SolveResult;

        let mut session = session();
        say(&mut session, "(sat-select and-sat)");
        let Response::Solve(request) = session.eval("(sat-solve)").expect("request") else {
            panic!("expected solve request");
        };
        let error = session
            .complete_sat(
                request.job(),
                SolveResult::Sat {
                    problem: request.problem(),
                    model: Box::new([]),
                },
            )
            .expect_err("lying solver rejected");
        assert!(error.to_string().contains("model rejected"));
        assert!(say(&mut session, "(sat-verify)").contains("no checked SAT result"));

        let Response::Solve(_) = session.eval("(sat-solve)").expect("retry request") else {
            panic!("matching rejection must consume the failed job")
        };
    }

    #[test]
    fn quitting_is_a_response_rather_than_a_value() {
        let mut session = session();
        assert_eq!(session.eval("(quit)").expect("eval"), Response::Quit);
    }
}
