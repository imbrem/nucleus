//! Runs untrusted WASM proof modules against the HOL kernel.
//!
//! A proof module is a core-Wasm guest that drives the kernel
//! dynamically through a flat FFI import namespace (`nucleus-logic`):
//! it resolves init-database exports, builds terms, invokes the
//! out-of-TCB derived rules of `covalence-hol-logic` on integer
//! handles, reads back what it has proved, and records finished
//! theorems with the host. The dynamic host-import shape is deliberate:
//! the kernel state is a whole `SQLite` database, and proof modules are
//! meant to *query* it mid-proof (resolve names, inspect theorems,
//! check whether something is already proved) to decide what to do
//! next. Reads can never mint authority, so the whole query surface is
//! trust-free; `thm_concl` is its seed, and the trajectory includes a
//! read-only SQL surface over the kernel database (the `PRAGMA
//! query_only` inspection pattern of the REPL is the precedent).
//!
//! # Trust
//!
//! The guest is completely untrusted. Host functions only wrap the
//! out-of-TCB logic API, which itself only calls the kernel's sealed
//! primitive rules through `proof_step`; theorem handles are minted
//! exclusively by the kernel, and every raw handle re-entering from the
//! guest is revalidated in-store. Those are the only checks with
//! soundness weight. Everything else - shape checks, the entry-point
//! contract, memory limits - exists to report failures early, and a
//! failed, trapped, out-of-memory, wrong-ABI, or unsupported-feature
//! guest run is just a failure: correctness never depends on a proof
//! module, and proof support being incomplete or even different across
//! runners is never an error. There is deliberately no gas or fuel
//! metering; resource exhaustion is an ordinary failure like any
//! other. The only error mode the host guards against is a guest
//! successfully proving something false, which is impossible while
//! theorem handles come only from the sealed rules.
//!
//! Re-executing a guest against the same inputs is expected to
//! reproduce the artifact (and hence its content hash); a mismatch
//! means a different artifact was produced - detection, not error -
//! and the produced database is not otherwise canonicalized.
//!
//! # Guest ABIs
//!
//! Nothing in the runner assumes exactly one guest ABI: each module
//! declares its flavor as per-module data ([`GuestAbi`]). Today that is
//! plain core Wasm (`wasm32-unknown-unknown`, empty ambient imports)
//! or, opt-in, core Wasm plus a native WASI preview 1 context so
//! ordinary Rust binaries can be proof modules. A guest importing WASI
//! when its module was not declared as WASI is a clean reported
//! failure. Longer term, WASI becomes the default with its functions
//! shimmed by *untrusted* code rather than host-native trust,
//! component-model guests join, and modules targeting different ABIs
//! link and call each other - all untrusted, all just driving the
//! trusted kernel. Trusted Wasm arrives later, only for kernel
//! acceleration, and is a completely separate and far more restricted
//! regime.

use covalence_lib_error::snafu::Snafu;
use covalence_neutron::Bytes;
use covalence_nucleus::Connection;
use covalence_nucleus::hol::{AllowAll, Hol, HolImageError, HolView, Tm, Ty};
use wasmtime::{
    Caller, Config, Engine, Extern, Linker, Module, Store, StoreLimits, StoreLimitsBuilder,
};

use covalence_hol_logic::Logic;

/// The import namespace proof modules link against.
pub const IMPORT_MODULE: &str = "nucleus-logic";

/// The exported entry point of a proof module.
pub const ENTRY: &str = "prove";

/// The value host functions return when an operation fails.
///
/// `0` is a valid handle (the empty variable context), so failures are
/// negative. The host records a human-readable reason for the last
/// failure and reports it in the [`RunOutcome`].
pub const FAILURE: i64 = -1;

/// How a guest module expects to be instantiated.
///
/// The flavor is per-module data, never a global runner mode: a future
/// module registry stores it next to the bytes, and modules of
/// different flavors are meant to link and call each other.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GuestAbi {
    /// Plain core Wasm: the `nucleus-logic` imports and nothing else.
    Core,
    /// Core Wasm plus a native WASI preview 1 context (stdout/stderr
    /// inherited, no filesystem or network), so ordinary Rust binaries
    /// compiled to `wasm32-wasip1` can be proof modules.
    WasiP1,
}

/// One guest module: raw bytes plus its declared ABI flavor.
#[derive(Clone, Copy, Debug)]
pub struct GuestModule<'a> {
    /// The core-Wasm module bytes.
    pub bytes: &'a [u8],
    /// The declared instantiation flavor.
    pub abi: GuestAbi,
}

/// The result of one completed (non-trapping) guest run.
pub struct RunOutcome {
    /// The kernel-state connection the guest drove.
    pub connection: Connection<Hol<AllowAll>>,
    /// The status value returned by the guest's entry point.
    pub status: i64,
    /// Raw theorem handles the guest recorded with `finish`, in order.
    ///
    /// Handles were revalidated when recorded; re-enter them through
    /// the view's `theorem_from_raw` to read the judgements.
    pub proved: Vec<i64>,
    /// The reason for the most recent failed host call, if any.
    pub guest_error: Option<String>,
}

/// Failure to run a proof module.
///
/// Every variant is an ordinary failure report (issue #384): an
/// unsupported construct, a broken module, or an exhausted resource is
/// a clean failure, never a soundness event.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunError {
    /// The kernel-state image could not be opened.
    #[snafu(display("cannot open the kernel-state image"), context(false))]
    Image {
        /// Underlying image failure.
        source: HolImageError,
    },
    /// The image does not carry a resolvable init database.
    #[snafu(display("cannot resolve the init database: {message}"))]
    Resolve {
        /// Human-readable resolution failure.
        message: String,
    },
    /// The engine or linker could not be configured.
    #[snafu(display("cannot configure the WASM engine: {message}"))]
    Engine {
        /// Human-readable engine failure.
        message: String,
    },
    /// The guest bytes are not a compilable core-Wasm module.
    #[snafu(display("cannot compile the guest module: {message}"))]
    Compile {
        /// Human-readable compilation failure.
        message: String,
    },
    /// The guest imports something this run does not provide.
    #[snafu(display("cannot instantiate the guest module: {message}"))]
    Instantiate {
        /// Human-readable instantiation failure.
        message: String,
    },
    /// The guest does not export the `prove` entry point.
    #[snafu(display("guest does not export `prove: () -> i64`: {message}"))]
    MissingEntry {
        /// Human-readable lookup failure.
        message: String,
    },
    /// The guest trapped or exhausted a resource limit while running.
    #[snafu(display("guest failed while running: {message}"))]
    Guest {
        /// Human-readable trap or exhaustion report.
        message: String,
    },
}

/// Host state carried by one guest run.
struct Session {
    connection: Connection<Hol<AllowAll>>,
    proved: Vec<i64>,
    last_error: Option<String>,
    limits: StoreLimits,
    wasi: wasmtime_wasi::p1::WasiP1Ctx,
}

impl Session {
    /// Runs one host operation over a fresh view, recording failures.
    ///
    /// Handle revalidation happens inside `operation` through the
    /// view's checked `*_from_raw` re-entry; this wrapper only converts
    /// the failure into the ABI's sentinel plus a recorded reason.
    fn host_call(
        &mut self,
        operation: impl for<'l, 'v> FnOnce(
            &Logic<'l, 'v, AllowAll>,
            &'l HolView<'v, AllowAll>,
        ) -> Result<i64, String>,
    ) -> i64 {
        let view = self.connection.view();
        let result = match Logic::new(&view) {
            Ok(logic) => operation(&logic, &view),
            Err(error) => Err(error.to_string()),
        };
        match result {
            Ok(value) => value,
            Err(message) => {
                self.last_error = Some(message);
                FAILURE
            }
        }
    }
}

/// A reusable proof-module runner over one engine.
pub struct Runner {
    engine: Engine,
}

impl Runner {
    /// Creates a runner with the default engine configuration.
    ///
    /// There is deliberately no fuel metering; the store carries a
    /// memory limit as quality of service, not soundness.
    ///
    /// # Errors
    ///
    /// Returns an error if the engine cannot be configured.
    pub fn new() -> Result<Self, RunError> {
        let engine = Engine::new(&Config::new()).map_err(|error| RunError::Engine {
            message: error.to_string(),
        })?;
        Ok(Self { engine })
    }

    /// Runs one proof module against a kernel-state image.
    ///
    /// The image is opened as a private writable copy; the guest is
    /// instantiated with only the `nucleus-logic` imports (plus a WASI
    /// preview 1 context when the module declares [`GuestAbi::WasiP1`])
    /// and its `prove` entry point is invoked once.
    ///
    /// # Errors
    ///
    /// Returns an error if the image cannot be opened or resolved, the
    /// module cannot be compiled or instantiated, the entry point is
    /// missing, or the guest traps. All of these are clean failures.
    pub fn run(&self, image: &Bytes, guest: GuestModule<'_>) -> Result<RunOutcome, RunError> {
        let connection = Connection::open_hol_image(image, AllowAll)?;
        {
            let view = connection.view();
            Logic::new(&view).map_err(|error| RunError::Resolve {
                message: error.to_string(),
            })?;
        }

        let module = Module::new(&self.engine, guest.bytes).map_err(|error| RunError::Compile {
            message: error.to_string(),
        })?;
        let mut linker: Linker<Session> = Linker::new(&self.engine);
        add_logic_imports(&mut linker).map_err(|error| RunError::Engine {
            message: error.to_string(),
        })?;
        // The context is built unconditionally (it is inert without the
        // imports); only a declared WASI module gets the imports linked.
        if guest.abi == GuestAbi::WasiP1 {
            wasmtime_wasi::p1::add_to_linker_sync(&mut linker, |session: &mut Session| {
                &mut session.wasi
            })
            .map_err(|error| RunError::Engine {
                message: error.to_string(),
            })?;
        }
        let wasi = wasmtime_wasi::WasiCtxBuilder::new()
            .inherit_stdout()
            .inherit_stderr()
            .build_p1();

        let session = Session {
            connection,
            proved: Vec::new(),
            last_error: None,
            limits: StoreLimitsBuilder::new()
                .memory_size(256 << 20)
                .instances(16)
                .build(),
            wasi,
        };
        let mut store = Store::new(&self.engine, session);
        store.limiter(|session| &mut session.limits);

        let instance =
            linker
                .instantiate(&mut store, &module)
                .map_err(|error| RunError::Instantiate {
                    message: error.to_string(),
                })?;
        if let Ok(initialize) = instance.get_typed_func::<(), ()>(&mut store, "_initialize") {
            initialize
                .call(&mut store, ())
                .map_err(|error| RunError::Guest {
                    message: error.to_string(),
                })?;
        }
        let entry = instance
            .get_typed_func::<(), i64>(&mut store, ENTRY)
            .map_err(|error| RunError::MissingEntry {
                message: error.to_string(),
            })?;
        let status = entry
            .call(&mut store, ())
            .map_err(|error| RunError::Guest {
                message: error.to_string(),
            })?;

        let session = store.into_data();
        Ok(RunOutcome {
            connection: session.connection,
            status,
            proved: session.proved,
            guest_error: session.last_error,
        })
    }
}

/// Reads a guest-memory string for name-resolving host functions.
fn read_guest_name(
    caller: &mut Caller<'_, Session>,
    pointer: i32,
    length: i32,
) -> Result<String, String> {
    let Some(Extern::Memory(memory)) = caller.get_export("memory") else {
        return Err("guest does not export its linear memory".to_owned());
    };
    let start = usize::try_from(u32::from_ne_bytes(pointer.to_ne_bytes()))
        .map_err(|_| "name pointer is out of range".to_owned())?;
    let length = usize::try_from(u32::from_ne_bytes(length.to_ne_bytes()))
        .map_err(|_| "name length is out of range".to_owned())?;
    let mut bytes = vec![0_u8; length];
    memory
        .read(&mut *caller, start, &mut bytes)
        .map_err(|_| "name is outside the guest memory".to_owned())?;
    String::from_utf8(bytes).map_err(|_| "name is not valid UTF-8".to_owned())
}

/// Installs the `nucleus-logic` host imports.
///
/// Each function revalidates its raw handles in-store, runs one
/// out-of-TCB operation, and returns [`FAILURE`] with a recorded
/// reason when anything goes wrong.
#[expect(clippy::too_many_lines, reason = "one flat ABI, one table of imports")]
fn add_logic_imports(linker: &mut Linker<Session>) -> wasmtime::Result<()> {
    linker.func_wrap(
        IMPORT_MODULE,
        "resolve",
        |mut caller: Caller<'_, Session>, pointer: i32, length: i32| {
            let name = match read_guest_name(&mut caller, pointer, length) {
                Ok(name) => name,
                Err(message) => {
                    caller.data_mut().last_error = Some(message);
                    return FAILURE;
                }
            };
            caller.data_mut().host_call(|_, view| {
                let namespace = view
                    .find_namespace(covalence_hol_init::NAMESPACE)
                    .map_err(|error| error.to_string())?
                    .ok_or_else(|| "init namespace is missing".to_owned())?;
                let export = view
                    .resolve_export(namespace, &name)
                    .map_err(|error| error.to_string())?;
                export
                    .as_term()
                    .map(covalence_nucleus::hol::TermId::raw)
                    .ok_or_else(|| format!("export {name:?} is not a term"))
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "vars_bool",
        |mut caller: Caller<'_, Session>, count: i64| {
            caller.data_mut().host_call(|_, view| {
                let count = usize::try_from(count)
                    .ok()
                    .filter(|count| *count <= 1024)
                    .ok_or_else(|| "variable count is out of range".to_owned())?;
                let bool_ty = view.ty(Ty::Bool).map_err(|error| error.to_string())?;
                view.vars(&vec![bool_ty; count])
                    .map(covalence_nucleus::hol::VarsId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "tm_var",
        |mut caller: Caller<'_, Session>, index: i64| {
            caller.data_mut().host_call(|_, view| {
                let index = u32::try_from(index)
                    .map_err(|_| "variable index is out of range".to_owned())?;
                view.tm(Tm::Bv(index))
                    .map(covalence_nucleus::hol::TermId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "tm_app",
        |mut caller: Caller<'_, Session>, function: i64, argument: i64| {
            caller.data_mut().host_call(|_, view| {
                let function = view
                    .tm_from_raw(function)
                    .map_err(|error| error.to_string())?;
                let argument = view
                    .tm_from_raw(argument)
                    .map_err(|error| error.to_string())?;
                view.tm(Tm::App(function, argument))
                    .map(covalence_nucleus::hol::TermId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "truth",
        |mut caller: Caller<'_, Session>, vars: i64| {
            caller.data_mut().host_call(|logic, view| {
                let vars = view
                    .vars_from_raw(vars)
                    .map_err(|error| error.to_string())?;
                logic
                    .truth(view.empty_kinds(), vars)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "assume",
        |mut caller: Caller<'_, Session>, vars: i64, prop: i64| {
            caller.data_mut().host_call(|logic, view| {
                let vars = view
                    .vars_from_raw(vars)
                    .map_err(|error| error.to_string())?;
                let prop = view.tm_from_raw(prop).map_err(|error| error.to_string())?;
                logic
                    .assume(view.empty_kinds(), vars, prop)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "conj",
        |mut caller: Caller<'_, Session>, left: i64, right: i64| {
            caller.data_mut().host_call(|logic, view| {
                let left = view
                    .theorem_from_raw(left)
                    .map_err(|error| error.to_string())?;
                let right = view
                    .theorem_from_raw(right)
                    .map_err(|error| error.to_string())?;
                logic
                    .conj(left, right)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "conjunct1",
        |mut caller: Caller<'_, Session>, theorem: i64| {
            caller.data_mut().host_call(|logic, view| {
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                logic
                    .conjunct1(theorem)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "conjunct2",
        |mut caller: Caller<'_, Session>, theorem: i64| {
            caller.data_mut().host_call(|logic, view| {
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                logic
                    .conjunct2(theorem)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "disj1",
        |mut caller: Caller<'_, Session>, theorem: i64, right: i64| {
            caller.data_mut().host_call(|logic, view| {
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                let right = view.tm_from_raw(right).map_err(|error| error.to_string())?;
                logic
                    .disj1(theorem, right)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "disj2",
        |mut caller: Caller<'_, Session>, left: i64, theorem: i64| {
            caller.data_mut().host_call(|logic, view| {
                let left = view.tm_from_raw(left).map_err(|error| error.to_string())?;
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                logic
                    .disj2(left, theorem)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "mp",
        |mut caller: Caller<'_, Session>, implication: i64, premise: i64| {
            caller.data_mut().host_call(|logic, view| {
                let implication = view
                    .theorem_from_raw(implication)
                    .map_err(|error| error.to_string())?;
                let premise = view
                    .theorem_from_raw(premise)
                    .map_err(|error| error.to_string())?;
                logic
                    .mp(implication, premise)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "disch",
        |mut caller: Caller<'_, Session>, prop: i64, theorem: i64| {
            caller.data_mut().host_call(|logic, view| {
                let prop = view.tm_from_raw(prop).map_err(|error| error.to_string())?;
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                logic
                    .disch(prop, theorem)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            })
        },
    )?;
    // A mid-proof read: guests inspect what a theorem handle actually
    // established (for example one returned by another module) before
    // deciding how to continue. Reads never mint authority.
    linker.func_wrap(
        IMPORT_MODULE,
        "thm_concl",
        |mut caller: Caller<'_, Session>, theorem: i64| {
            caller.data_mut().host_call(|_, view| {
                let theorem = view
                    .theorem_from_raw(theorem)
                    .map_err(|error| error.to_string())?;
                let (.., concl) = view.theorem(theorem).map_err(|error| error.to_string())?;
                Ok(concl.raw())
            })
        },
    )?;
    linker.func_wrap(
        IMPORT_MODULE,
        "finish",
        |mut caller: Caller<'_, Session>, theorem: i64| {
            let session = caller.data_mut();
            let recorded = session.host_call(|_, view| {
                view.theorem_from_raw(theorem)
                    .map(covalence_nucleus::hol::syntax::TheoremId::raw)
                    .map_err(|error| error.to_string())
            });
            if recorded == FAILURE {
                return FAILURE;
            }
            session.proved.push(recorded);
            1
        },
    )?;
    Ok(())
}
