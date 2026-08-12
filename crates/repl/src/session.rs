//! Host-independent REPL evaluation.
//!
//! I/O is returned as a [`Response`] for the terminal or browser to perform.

use covalence_data_cas::MemoryCas;
use covalence_lib_hash::{O256, o256};
use covalence_nucleus::prop::{AllowAll, Lit, PreparedSat, WorldId};

use crate::sat::{SAT_DEMOS, SatProblem};
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
    /// Ask the host to read a DIMACS file for [`Session::load_sat`].
    ReadSatFile(String),
    /// Fetch this URL and pass its bytes to [`Session::admit_verified`].
    Fetch {
        /// Where the bytes might be.
        url: String,
        /// What they must hash to.
        address: O256,
    },
    /// Ask the host to run the `SQLite` shell.
    Shell(Vec<String>),
    /// Ask an untrusted host capability to solve canonical DIMACS.
    Solve {
        /// Opaque correlation token for the retained trusted continuation.
        job: SatJobId,
        /// Canonical problem bytes. The retained continuation owns identity.
        dimacs: Vec<u8>,
        /// Largest model response the trusted checker accepts.
        max_model_literals: usize,
        /// Largest proof response the trusted checker accepts.
        max_proof_bytes: usize,
    },
    /// Leave.
    Quit,
}

/// Opaque identity of one pending SAT request.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SatJobId(u64);

impl std::fmt::Display for SatJobId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

impl std::str::FromStr for SatJobId {
    type Err = ();

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let value: u64 = text.parse().map_err(|_| ())?;
        if value == 0 || value.to_string() != text {
            return Err(());
        }
        Ok(Self(value))
    }
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
    /// A solve is already waiting for its one completion.
    SatPending,
    /// The session has issued every representable job identity.
    SatJobExhausted,
    /// A completion did not name the retained solve job.
    UnknownSatJob(String),
    /// An untrusted model contained an invalid literal.
    InvalidSatLiteral(i64),
    /// A DIMACS problem is malformed or unavailable.
    SatProblem(String),
    /// No SAT problem is selected.
    NoSatProblem,
    /// No checked SAT result is available.
    NoSatResult,
    /// The checked propositional kernel rejected preparation or completion.
    Prop(covalence_nucleus::prop::PropError),
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
            Self::UnknownKernel(id) => write!(formatter, "no kernel {id}"),
            Self::WrongKernel(message) => formatter.write_str(message),
            Self::NotWhatWasAskedFor { expected, actual } => write!(
                formatter,
                "content does not match its address: asked for {}, received {}",
                expected.hex(),
                actual.hex()
            ),
            Self::SatPending => formatter.write_str("a SAT solve is already pending"),
            Self::SatJobExhausted => formatter.write_str("SAT job identities are exhausted"),
            Self::UnknownSatJob(job) => write!(formatter, "no pending SAT job {job}"),
            Self::InvalidSatLiteral(literal) => {
                write!(formatter, "invalid SAT model literal {literal}")
            }
            Self::SatProblem(message) => formatter.write_str(message),
            Self::NoSatProblem => {
                formatter.write_str("no SAT problem is selected; try (sat-demos)")
            }
            Self::NoSatResult => formatter.write_str("no checked SAT result is available"),
            Self::Prop(error) => write!(formatter, "{error}"),
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

impl From<covalence_nucleus::prop::PropError> for SessionError {
    fn from(error: covalence_nucleus::prop::PropError) -> Self {
        Self::Prop(error)
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

(sat-demos)         list built-in gate and adder problems
(sat-demo NAME)     select a built-in problem
(sat-set \"DIMACS\")  select an inline problem
(sat-load \"PATH\")   select a DIMACS file
(sat-problem)       describe the selected problem
(sat-dimacs)        show its canonical DIMACS
(sat-solve)         ask the configured untrusted solver
(sat-status)        show selected, pending, operational, or checked state
(sat-result)        show the last checked result
(sat-model)         show the checked model
(sat-proof)         show checked proof metadata
(sat-proof-text)    render the retained LRAT proof for inspection
(sat-checked)       query the locally admitted judgement
(sat-database)      snapshot the selected kernel into the local store

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
    next_sat_job: u64,
    pending_sat: Option<PendingSat>,
    sat_problem: Option<SatProblem>,
    sat_result: Option<CheckedSat>,
    sat_status: Option<SatStatus>,
}

struct PendingSat {
    job: SatJobId,
    problem: O256,
    prepared: PreparedSat<AllowAll>,
}

enum CheckedSat {
    Sat {
        problem: O256,
        world: WorldId,
        model: Vec<i64>,
    },
    Unsat {
        problem: O256,
        proof: O256,
        bytes: usize,
        binary: bool,
    },
}

enum SatStatus {
    Ready,
    Pending(SatJobId),
    Checked(&'static str),
    Operational(&'static str, Option<String>),
    Rejected(String),
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
            next_sat_job: 1,
            pending_sat: None,
            sat_problem: None,
            sat_result: None,
            sat_status: None,
        }
    }

    /// Retains a checked problem description and asks the host to solve it.
    ///
    /// # Errors
    ///
    /// Returns an error while another solve is pending or job ids are
    /// exhausted. Textual propositional forms are deliberately left to #584.
    pub fn begin_sat(&mut self, prepared: PreparedSat<AllowAll>) -> Result<Response, SessionError> {
        if self.pending_sat.is_some() {
            return Err(SessionError::SatPending);
        }
        let raw = self.next_sat_job;
        self.next_sat_job = self
            .next_sat_job
            .checked_add(1)
            .ok_or(SessionError::SatJobExhausted)?;
        let job = SatJobId(raw);
        let response = Response::Solve {
            job,
            dimacs: prepared.dimacs().to_vec(),
            max_model_literals: prepared.max_model_literals(),
            max_proof_bytes: prepared.max_proof_bytes(),
        };
        self.pending_sat = Some(PendingSat {
            job,
            problem: prepared.id(),
            prepared,
        });
        self.sat_status = Some(SatStatus::Pending(job));
        Ok(response)
    }

    /// Consumes a matching job and checks an untrusted SAT assignment.
    ///
    /// # Errors
    ///
    /// Returns an error for a stale job, malformed model, failed check, or
    /// atomic commit failure. A matching job is consumed on every outcome.
    pub fn complete_sat(&mut self, job: SatJobId, model: &[i64]) -> Result<Value, SessionError> {
        let pending = self.take_sat(job)?;
        let model = match model
            .iter()
            .copied()
            .map(|literal| Lit::new(literal).ok_or(SessionError::InvalidSatLiteral(literal)))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(model) => model,
            Err(error) => {
                self.sat_status = Some(SatStatus::Rejected(error.to_string()));
                return Err(error);
            }
        };
        let world = match pending.prepared.certify_model(&model) {
            Ok(world) => world,
            Err(error) => {
                self.sat_status = Some(SatStatus::Rejected(error.to_string()));
                return Err(error.into());
            }
        };
        if self
            .sat_problem
            .as_ref()
            .is_some_and(|problem| problem.identity == pending.problem)
        {
            self.sat_result = Some(CheckedSat::Sat {
                problem: pending.problem,
                world,
                model: model.iter().map(|literal| literal.get()).collect(),
            });
        }
        self.sat_status = Some(SatStatus::Checked("sat"));
        Ok(Value::List(vec![
            Value::Symbol("sat".to_owned()),
            Value::Integer(world.get()),
        ]))
    }

    /// Consumes a matching job and checks ASCII or binary LRAT.
    ///
    /// # Errors
    ///
    /// Returns an error for a stale job, malformed or invalid proof, exhausted
    /// bound, or commit failure.
    pub fn complete_unsat(&mut self, job: SatJobId, proof: &[u8]) -> Result<Value, SessionError> {
        let pending = self.take_sat(job)?;
        if let Err(error) = pending.prepared.certify_lrat(proof, -1) {
            self.sat_status = Some(SatStatus::Rejected(error.to_string()));
            return Err(error.into());
        }
        if self
            .sat_problem
            .as_ref()
            .is_some_and(|problem| problem.identity == pending.problem)
        {
            let address = self.repl.put(proof.to_vec())?;
            self.sat_result = Some(CheckedSat::Unsat {
                problem: pending.problem,
                proof: address,
                bytes: proof.len(),
                binary: proof
                    .first()
                    .is_some_and(|byte| matches!(byte, b'a' | b'd')),
            });
        }
        self.sat_status = Some(SatStatus::Checked("unsat"));
        Ok(Value::Symbol("unsat".to_owned()))
    }

    /// Consumes a matching job without admitting a logical result.
    ///
    /// # Errors
    ///
    /// Returns an error if `job` is not the retained pending job.
    pub fn abandon_sat(&mut self, job: SatJobId) -> Result<(), SessionError> {
        self.finish_sat_operational(job, "abandoned", None)
    }

    /// Consumes a job with a non-authoritative operational outcome.
    ///
    /// # Errors
    ///
    /// Returns an error when `job` is not the retained pending job.
    pub fn finish_sat_operational(
        &mut self,
        job: SatJobId,
        state: &'static str,
        detail: Option<&str>,
    ) -> Result<(), SessionError> {
        self.take_sat(job)?;
        let detail = detail.map(|text| text.chars().take(512).collect());
        self.sat_status = Some(SatStatus::Operational(state, detail));
        Ok(())
    }

    fn take_sat(&mut self, job: SatJobId) -> Result<PendingSat, SessionError> {
        let Some(pending) = self.pending_sat.as_ref() else {
            return Err(SessionError::UnknownSatJob(job.to_string()));
        };
        if pending.job != job {
            return Err(SessionError::UnknownSatJob(job.to_string()));
        }
        Ok(self.pending_sat.take().expect("checked above"))
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

    /// Selects DIMACS bytes read by the host.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed input or while a solve is pending.
    pub fn load_sat(
        &mut self,
        bytes: &[u8],
        source: impl Into<String>,
    ) -> Result<Value, SessionError> {
        self.select_sat(bytes, source.into(), None)
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

    /// Forms for selecting and checking a DIMACS problem.
    fn sat_form(
        &mut self,
        name: &str,
        arguments: &[Value],
    ) -> Result<Option<Response>, SessionError> {
        Ok(Some(match (name, arguments) {
            ("sat-demos", []) => Response::value(Value::list(
                SAT_DEMOS
                    .iter()
                    .map(|demo| {
                        Value::List(vec![
                            Value::Symbol(demo.name.to_owned()),
                            Value::Symbol(demo.expected.to_owned()),
                            Value::Text(demo.description.to_owned()),
                        ])
                    })
                    .collect(),
            )),
            ("sat-demo", [name]) => {
                let name = name
                    .as_text()
                    .ok_or(SessionError::Usage("(sat-demo NAME)"))?;
                let demo = SAT_DEMOS
                    .iter()
                    .find(|demo| demo.name == name)
                    .ok_or_else(|| SessionError::SatProblem(format!("no SAT demo {name}")))?;
                Response::value(self.select_sat(
                    demo.dimacs.as_bytes(),
                    demo.name.to_owned(),
                    Some(demo.expected),
                )?)
            }
            ("sat-set", [text]) => {
                let text = text
                    .as_text()
                    .ok_or(SessionError::Usage("(sat-set \"DIMACS\")"))?;
                Response::value(self.select_sat(text.as_bytes(), "inline".to_owned(), None)?)
            }
            ("sat-load", [path]) => {
                if self.pending_sat.is_some() {
                    return Err(SessionError::SatPending);
                }
                Response::ReadSatFile(
                    path.as_text()
                        .ok_or(SessionError::Usage("(sat-load \"PATH\")"))?
                        .to_owned(),
                )
            }
            ("sat-problem", []) => Response::value(self.sat_problem_value()?),
            ("sat-dimacs", []) => Response::value(Value::Text(
                String::from_utf8(self.problem()?.dimacs.clone())
                    .expect("canonical DIMACS is ASCII"),
            )),
            ("sat-solve", []) => {
                let prepared = self
                    .problem()?
                    .prepare()
                    .map_err(SessionError::SatProblem)?;
                let response = self.begin_sat(prepared)?;
                self.sat_result = None;
                response
            }
            ("sat-status", []) => Response::value(self.sat_status_value()),
            ("sat-result", []) => Response::value(self.sat_result_value()?),
            ("sat-model", []) => Response::value(self.sat_model_value()?),
            ("sat-proof", []) => Response::value(self.sat_proof_value()?),
            ("sat-proof-text", []) => Response::value(self.sat_proof_text_value()?),
            ("sat-checked", []) => Response::value(self.sat_checked_value()?),
            ("sat-database", []) => {
                let image = self
                    .problem()?
                    .snapshot()
                    .map_err(SessionError::SatProblem)?;
                Response::value(Value::Address(self.repl.put(image)?))
            }
            _ if name.starts_with("sat-") => {
                return Err(SessionError::Usage("a documented sat-* command"));
            }
            _ => return Ok(None),
        }))
    }

    fn select_sat(
        &mut self,
        bytes: &[u8],
        source: String,
        expected: Option<&'static str>,
    ) -> Result<Value, SessionError> {
        if self.pending_sat.is_some() {
            return Err(SessionError::SatPending);
        }
        let problem =
            SatProblem::parse(bytes, source, expected).map_err(SessionError::SatProblem)?;
        self.sat_problem = Some(problem);
        self.sat_result = None;
        self.sat_status = Some(SatStatus::Ready);
        self.sat_problem_value()
    }

    fn problem(&self) -> Result<&SatProblem, SessionError> {
        self.sat_problem.as_ref().ok_or(SessionError::NoSatProblem)
    }

    fn sat_problem_value(&self) -> Result<Value, SessionError> {
        let problem = self.problem()?;
        let mut fields = vec![
            Value::List(vec![
                Value::Symbol("source".to_owned()),
                Value::Text(problem.source.clone()),
            ]),
            Value::List(vec![
                Value::Symbol("id".to_owned()),
                Value::Address(problem.identity),
            ]),
            pair("variables", count(problem.variables)),
            pair("clauses", count(problem.clauses)),
        ];
        if let Some(expected) = problem.expected {
            fields.push(Value::List(vec![
                Value::Symbol("expected".to_owned()),
                Value::Symbol(expected.to_owned()),
            ]));
        }
        Ok(Value::List(fields))
    }

    fn current_result(&self) -> Result<(&SatProblem, &CheckedSat), SessionError> {
        let problem = self.problem()?;
        let result = self.sat_result.as_ref().ok_or(SessionError::NoSatResult)?;
        let identity = match result {
            CheckedSat::Sat { problem, .. } | CheckedSat::Unsat { problem, .. } => *problem,
        };
        if identity != problem.identity {
            return Err(SessionError::NoSatResult);
        }
        Ok((problem, result))
    }

    fn sat_result_value(&self) -> Result<Value, SessionError> {
        let (_, result) = self.current_result()?;
        Ok(match result {
            CheckedSat::Sat { world, model, .. } => Value::List(vec![
                Value::Symbol("sat".to_owned()),
                pair("world", world.get()),
                pair("model-literals", count(model.len())),
            ]),
            CheckedSat::Unsat {
                proof,
                bytes,
                binary,
                ..
            } => Value::List(vec![
                Value::Symbol("unsat".to_owned()),
                Value::List(vec![
                    Value::Symbol("proof".to_owned()),
                    Value::Address(*proof),
                ]),
                pair("bytes", count(*bytes)),
                Value::List(vec![
                    Value::Symbol("encoding".to_owned()),
                    Value::Symbol(if *binary { "binary" } else { "ascii" }.to_owned()),
                ]),
            ]),
        })
    }

    fn sat_status_value(&self) -> Value {
        if self.sat_problem.is_none() {
            return Value::Symbol("idle".to_owned());
        }
        match self.sat_status.as_ref().unwrap_or(&SatStatus::Ready) {
            SatStatus::Ready => Value::Symbol("selected".to_owned()),
            SatStatus::Pending(job) => Value::List(vec![
                Value::Symbol("pending".to_owned()),
                Value::Text(job.to_string()),
            ]),
            SatStatus::Checked(state) | SatStatus::Operational(state, None) => {
                Value::Symbol((*state).to_owned())
            }
            SatStatus::Operational(state, Some(detail)) => Value::List(vec![
                Value::Symbol((*state).to_owned()),
                Value::Text(detail.clone()),
            ]),
            SatStatus::Rejected(detail) => Value::List(vec![
                Value::Symbol("rejected".to_owned()),
                Value::Text(detail.clone()),
            ]),
        }
    }

    fn sat_model_value(&self) -> Result<Value, SessionError> {
        let (_, CheckedSat::Sat { model, .. }) = self.current_result()? else {
            return Err(SessionError::NoSatResult);
        };
        Ok(Value::list(
            model.iter().copied().map(Value::Integer).collect(),
        ))
    }

    fn sat_proof_value(&self) -> Result<Value, SessionError> {
        let (
            _,
            CheckedSat::Unsat {
                proof,
                bytes,
                binary,
                ..
            },
        ) = self.current_result()?
        else {
            return Err(SessionError::NoSatResult);
        };
        Ok(Value::List(vec![
            Value::Address(*proof),
            Value::Symbol(if *binary { "binary" } else { "ascii" }.to_owned()),
            Value::Integer(count(*bytes)),
        ]))
    }

    fn sat_proof_text_value(&self) -> Result<Value, SessionError> {
        let (_, CheckedSat::Unsat { proof, .. }) = self.current_result()? else {
            return Err(SessionError::NoSatResult);
        };
        let bytes = self
            .repl
            .cas()
            .get(*proof)
            .ok_or(SessionError::NoSatResult)?;
        let text = covalence_nucleus::prop::lrat::to_text_bounded(
            &bytes,
            covalence_nucleus::prop::lrat::Limits::default(),
            8 * 1024 * 1024,
        )
        .map_err(|error| SessionError::SatProblem(format!("LRAT display rejected: {error:?}")))?;
        Ok(Value::Text(text))
    }

    fn sat_checked_value(&self) -> Result<Value, SessionError> {
        let (problem, result) = self.current_result()?;
        match result {
            CheckedSat::Sat { world, .. }
                if problem
                    .sat_holds(*world)
                    .map_err(SessionError::SatProblem)? =>
            {
                Ok(Value::List(vec![
                    Value::Symbol("sat".to_owned()),
                    pair("world", world.get()),
                ]))
            }
            CheckedSat::Unsat { .. }
                if problem.unsat_holds().map_err(SessionError::SatProblem)? =>
            {
                Ok(Value::Symbol("unsat".to_owned()))
            }
            _ => Err(SessionError::NoSatResult),
        }
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
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    use covalence_data_cas::Cas;
    use covalence_nucleus::Connection as NucleusConnection;
    use covalence_nucleus::prop::{CnfLimits, Prop, PropId, lrat};

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

    fn contradiction() -> PreparedSat<AllowAll> {
        let connection = Arc::new(
            NucleusConnection::<Prop<AllowAll>>::open_prop_in_memory(AllowAll)
                .expect("prop connection"),
        );
        let view = connection.view();
        let id = |value| PropId::new(value).expect("positive id");
        view.declare_free(id(1)).expect("variable");
        view.define(id(2), &[Lit::new(-1).expect("literal")])
            .expect("positive unit clause");
        view.define(id(3), &[Lit::new(1).expect("literal")])
            .expect("negative unit clause");
        view.define(
            id(4),
            &[
                Lit::new(-2).expect("literal"),
                Lit::new(-3).expect("literal"),
            ],
        )
        .expect("formula");
        connection
            .prepare_sat(
                id(4),
                &[id(2), id(3)],
                CnfLimits::default(),
                16,
                lrat::Limits::default(),
            )
            .expect("prepare")
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
    fn quitting_is_a_response_rather_than_a_value() {
        let mut session = session();
        assert_eq!(session.eval("(quit)").expect("eval"), Response::Quit);
    }

    #[test]
    fn sat_jobs_are_exactly_once_and_wrong_tokens_do_not_consume() {
        let mut session = session();
        let Response::Solve { job, dimacs, .. } =
            session.begin_sat(contradiction()).expect("begin first job")
        else {
            panic!("expected solve response");
        };
        assert_eq!(dimacs, b"p cnf 1 2\n1 0\n-1 0\n");
        assert!(matches!(
            session.begin_sat(contradiction()),
            Err(SessionError::SatPending)
        ));

        let wrong = (job.0 + 1).to_string().parse().expect("job");
        assert!(matches!(
            session.complete_unsat(wrong, &[b'a', 6, 0, 2, 4, 0]),
            Err(SessionError::UnknownSatJob(_))
        ));
        assert_eq!(
            session
                .complete_unsat(job, &[b'a', 6, 0, 2, 4, 0])
                .expect("checked LRAT")
                .display(),
            "unsat"
        );
        assert!(matches!(
            session.complete_unsat(job, &[b'a', 6, 0, 2, 4, 0]),
            Err(SessionError::UnknownSatJob(_))
        ));
    }

    #[test]
    fn rejected_and_abandoned_jobs_are_consumed() {
        let mut session = session();
        let Response::Solve { job, .. } = session.begin_sat(contradiction()).expect("begin") else {
            panic!("expected solve response");
        };
        assert!(session.complete_unsat(job, b"not LRAT").is_err());
        assert!(matches!(
            session.abandon_sat(job),
            Err(SessionError::UnknownSatJob(_))
        ));

        let Response::Solve { job, .. } = session.begin_sat(contradiction()).expect("begin") else {
            panic!("expected solve response");
        };
        session.abandon_sat(job).expect("abandon");
        assert!(matches!(
            session.abandon_sat(job),
            Err(SessionError::UnknownSatJob(_))
        ));
    }

    #[test]
    fn both_lrat_encodings_complete_the_same_kind_of_job() {
        let mut session = session();
        let Response::Solve { job, .. } = session.begin_sat(contradiction()).expect("binary job")
        else {
            panic!("expected solve response");
        };
        session
            .complete_unsat(job, &[b'a', 6, 0, 2, 4, 0])
            .expect("binary LRAT");

        let Response::Solve { job, .. } = session.begin_sat(contradiction()).expect("ASCII job")
        else {
            panic!("expected solve response");
        };
        session
            .complete_unsat(job, b"3 0 1 2 0\n")
            .expect("ASCII LRAT");
    }

    #[test]
    fn sat_demos_are_small_canonical_gate_problems() {
        let mut session = session();
        let demos = say(&mut session, "(sat-demos)");
        assert!(demos.contains("and-sat"), "{demos}");
        assert!(demos.contains("half-adder-unsat"), "{demos}");

        let first = say(&mut session, "(sat-demo and-sat)");
        assert!(first.contains("(variables 3)"), "{first}");
        assert!(first.contains("(expected sat)"), "{first}");
        let identity = session.problem().expect("selected").identity;
        assert_eq!(
            say(&mut session, "(sat-dimacs)"),
            r#""p cnf 3 4\n3 -1 -2 0\n1 -3 0\n2 -3 0\n3 0\n""#
        );
        say(&mut session, "(sat-demo and-sat)");
        assert_eq!(
            session.problem().expect("selected again").identity,
            identity
        );
    }

    #[test]
    fn sat_demo_checks_a_model_and_queries_the_admitted_world() {
        let mut session = session();
        say(&mut session, "(sat-demo and-sat)");
        let Response::Solve { job, dimacs, .. } = session.eval("(sat-solve)").expect("solve")
        else {
            panic!("expected solve request");
        };
        assert_eq!(dimacs, b"p cnf 3 4\n3 -1 -2 0\n1 -3 0\n2 -3 0\n3 0\n");
        session
            .complete_sat(job, &[1, 2, 3])
            .expect("checked model");
        assert_eq!(say(&mut session, "(sat-model)"), "(1 2 3)");
        assert!(say(&mut session, "(sat-result)").starts_with("(sat "));
        assert!(say(&mut session, "(sat-checked)").starts_with("(sat "));
    }

    #[test]
    fn sat_demo_keeps_a_checked_binary_proof_as_an_artifact() {
        let mut session = session();
        say(&mut session, "(sat-demo and-unsat)");
        let Response::Solve { job, .. } = session.eval("(sat-solve)").expect("solve") else {
            panic!("expected solve request");
        };
        let proof = [
            97, 12, 2, 0, 8, 4, 0, 97, 14, 4, 0, 8, 6, 0, 97, 16, 0, 12, 10, 0,
        ];
        session.complete_unsat(job, &proof).expect("checked proof");
        assert_eq!(say(&mut session, "(sat-checked)"), "unsat");
        let rendered = say(&mut session, "(sat-proof)");
        assert!(rendered.contains("binary"), "{rendered}");
        assert!(rendered.ends_with(" 20)"), "{rendered}");
        assert_eq!(session.repl().stats().objects, 1);
    }

    #[test]
    fn malformed_dimacs_does_not_replace_the_selected_problem() {
        let mut session = session();
        say(&mut session, "(sat-demo and-sat)");
        let identity = session.problem().expect("selected").identity;
        let error = say(&mut session, r#"(sat-set "p cnf 1 2\n1 0\n")"#);
        assert!(error.contains("declares 2 clauses"), "{error}");
        assert_eq!(
            session.problem().expect("still selected").identity,
            identity
        );

        for bad in [
            "1 0\np cnf 1 1\n",
            "p cnf 1 1\n2 0\n",
            "p cnf 1 1\n1\n",
            "p cnf 1 1\n1 0\n0\n",
        ] {
            assert!(
                SatProblem::parse(bad.as_bytes(), "bad".to_owned(), None).is_err(),
                "{bad:?}"
            );
        }
    }

    #[test]
    fn loading_uses_the_host_file_pattern_and_pending_jobs_pin_selection() {
        let mut session = session();
        assert_eq!(
            session.eval(r#"(sat-load "problem.cnf")"#).expect("load"),
            Response::ReadSatFile("problem.cnf".to_owned())
        );
        session
            .load_sat(b"p cnf 1 1\n1 0\n", "problem.cnf")
            .expect("loaded");
        let Response::Solve { job, .. } = session.eval("(sat-solve)").expect("solve") else {
            panic!("expected solve request");
        };
        assert!(matches!(
            session.eval(r#"(sat-load "replacement.cnf")"#),
            Err(SessionError::SatPending)
        ));
        assert!(matches!(
            session.load_sat(b"p cnf 1 1\n-1 0\n", "replacement.cnf"),
            Err(SessionError::SatPending)
        ));
        session.abandon_sat(job).expect("abandon");
        session
            .load_sat(b"p cnf 1 1\n-1 0\n", "replacement.cnf")
            .expect("replace after completion");
    }

    #[test]
    fn sat_status_records_non_authoritative_terminal_outcomes() {
        let mut session = session();
        say(&mut session, "(sat-demo and-sat)");
        assert_eq!(say(&mut session, "(sat-status)"), "selected");
        let Response::Solve { job, .. } = session.eval("(sat-solve)").expect("solve") else {
            panic!("expected solve request");
        };
        assert!(say(&mut session, "(sat-status)").starts_with("(pending "));
        session
            .finish_sat_operational(job, "unknown", Some("solver declined"))
            .expect("unknown");
        assert_eq!(
            say(&mut session, "(sat-status)"),
            "(unknown \"solver declined\")"
        );
        assert!(say(&mut session, "(sat-checked)").starts_with("error:"));
        assert!(matches!(
            session.finish_sat_operational(job, "failed", None),
            Err(SessionError::UnknownSatJob(_))
        ));
    }
}
