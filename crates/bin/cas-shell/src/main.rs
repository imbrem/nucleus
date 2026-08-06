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

use std::os::unix::net::UnixStream;
use std::process::ExitCode;
use std::sync::Arc;

use covalence_data_cas_wire::{RemoteCas, Transport};
use covalence_neutron::{CAS_VFS_NAME, register_cas};

fn main() -> ExitCode {
    match run() {
        Ok(status) => u8::try_from(status).map_or(ExitCode::FAILURE, ExitCode::from),
        Err(error) => {
            eprintln!("cas-shell: {error}");
            ExitCode::FAILURE
        }
    }
}

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

    // The mount is process-global, but this process is the shell, so there is
    // nothing here to protect it from.
    register_cas(cas, CAS_VFS_NAME, false)?;

    let shell_arguments: Vec<String> = arguments.collect();
    Ok(covalence_bin_cas_shell::run(&shell_arguments)?)
}
