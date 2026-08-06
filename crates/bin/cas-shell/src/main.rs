//! The upstream `SQLite` shell, run against a content-addressed store held by
//! another process.
//!
//! This binary is the whole point of the arrangement. It links its own
//! `SQLite`, mounts a VFS which resolves addresses by asking a server over a
//! socket, and then hands control to the real `sqlite3` shell. It shares no
//! memory with whoever owns the store.
//!
//! What that buys is not convenience — the in-process alternative is smaller —
//! but the removal of an argument. An embedded `shell.c` is 37,000 lines of C
//! in the kernel's address space, and saying "no correctness claim depends on
//! it" is weaker than saying it cannot reach the kernel at all. Here everything
//! this process can do is bounded by the CAS protocol: read objects the server
//! chose to serve, and nothing else. No writes, no enumeration, no SQL executed
//! anywhere but here.
//!
//! It is also why the browser is not a special case. The transport changes; the
//! design does not.
//!
//! # Usage
//!
//! ```text
//! covalence-cas-shell --cas <SOCKET> [SHELL ARGUMENT...]
//! ```
//!
//! Arguments after `--cas <SOCKET>` are the ordinary `sqlite3` command line. A
//! resident object opens as `file:<address>?vfs=cas`.

use std::process::ExitCode;
use std::sync::Arc;

use covalence_neutron::{CAS_VFS_NAME, register_cas};

#[cfg(unix)]
use std::os::unix::net::UnixStream;
#[cfg(unix)]
use std::sync::OnceLock;

#[cfg(unix)]
use covalence_data_cas_wire::{RemoteCas, Transport};

/// The store, parked between connecting to it and the shell asking for it.
///
/// The handoff goes through a static because the shell calls back into us from
/// C, with no argument to carry it.
#[cfg(unix)]
static STORE: OnceLock<Arc<RemoteCas<UnixStream, UnixStream>>> = OnceLock::new();

/// Called by `shell.c` at the point it initializes `SQLite`.
///
/// Mounting here rather than before entering the shell is what keeps `SQLite`
/// uninitialized until the shell is ready: registering a VFS initializes it,
/// and doing that early makes the shell's own `sqlite3_config` calls fail with
/// a warning printed to stdout, which would corrupt any script reading its
/// output.
#[allow(unsafe_code, reason = "the shell calls this from C by name")]
#[unsafe(no_mangle)]
extern "C" fn covalence_shell_init() {
    #[cfg(unix)]
    let store = match STORE.get() {
        Some(store) => Arc::clone(store),
        // Nothing to mount. The shell still runs; only `?vfs=cas` is missing.
        None => return,
    };
    // Under WASI the store is the host, which is always there: no connection
    // to establish and nothing to park.
    #[cfg(target_os = "wasi")]
    let store = Arc::new(covalence_bin_cas_shell::wasi::HostCas);

    if let Err(error) = register_cas(store, CAS_VFS_NAME, false) {
        eprintln!("cas-shell: could not mount the store: {error}");
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(status) => u8::try_from(status).map_or(ExitCode::FAILURE, ExitCode::from),
        Err(error) => {
            eprintln!("cas-shell: {error}");
            ExitCode::FAILURE
        }
    }
}

/// Under WASI the store arrives through imports, so every argument is the
/// shell's.
#[cfg(target_os = "wasi")]
fn run() -> Result<i32, Box<dyn std::error::Error>> {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    Ok(covalence_bin_cas_shell::run(&arguments)?)
}

#[cfg(unix)]
fn run() -> Result<i32, Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let socket = match arguments.next().as_deref() {
        Some("--cas") => arguments.next().ok_or("--cas requires a socket path")?,
        _ => return Err("usage: cas-shell --cas <SOCKET> [SHELL ARGUMENT...]".into()),
    };

    // One connection for the life of the process. The server holds every
    // object opened through it, so a database stays readable even if its
    // address is dropped from the store while the shell is using it.
    let stream = UnixStream::connect(&socket)?;
    let cas = Arc::new(RemoteCas::new(Transport::new(stream.try_clone()?, stream)));

    // Parked for `covalence_shell_init`, which the shell calls once it is
    // ready for SQLite to exist.
    STORE
        .set(cas)
        .map_err(|_| "the store was already connected")?;

    let shell_arguments: Vec<String> = arguments.collect();
    Ok(covalence_bin_cas_shell::run(&shell_arguments)?)
}
