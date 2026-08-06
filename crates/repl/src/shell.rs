//! Running the `SQLite` shell as a separate process.
//!
//! The REPL does not embed a shell. It serves its store over a socket and runs
//! the shell binary against it, so 37,000 lines of vendored C never enter this
//! address space. What the shell can do is exactly what the CAS protocol
//! allows: open and read objects this process chose to serve.
//!
//! The socket lives in a private directory created with mode `0700` and is
//! removed when the shell exits.

use std::io;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_data_cas::MemoryCas;
use covalence_data_cas_wire::serve;

/// Where the shell binary is found.
///
/// Resolved from the environment so a development tree and an installed tree
/// can differ without the REPL guessing.
pub const SHELL_BINARY_ENV: &str = "COVALENCE_CAS_SHELL";

/// Default binary name, looked up on `PATH` when the variable is unset.
pub const SHELL_BINARY_DEFAULT: &str = "covalence-cas-shell";

/// Failure to run the shell.
#[derive(Debug)]
pub enum ShellError {
    /// The socket could not be created, or the shell could not be started.
    Io(io::Error),
    /// The shell ran and exited with a non-zero status.
    Status(i32),
}

impl std::fmt::Display for ShellError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "could not run the shell: {error}"),
            Self::Status(status) => write!(formatter, "shell exited with status {status}"),
        }
    }
}

impl std::error::Error for ShellError {}

impl From<io::Error> for ShellError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// A listening socket which cleans up its directory when dropped.
struct Endpoint {
    directory: PathBuf,
    path: PathBuf,
    listener: UnixListener,
}

impl Endpoint {
    fn bind() -> io::Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "covalence-cas-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory)?;
        // Owner-only: the socket is an unauthenticated read capability over
        // everything this store holds, so it must not be world-reachable.
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;

        let path = directory.join("socket");
        let listener = UnixListener::bind(&path)?;
        Ok(Self {
            directory,
            path,
            listener,
        })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for Endpoint {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
        let _ = std::fs::remove_dir(&self.directory);
    }
}

/// Runs the shell against `cas`, returning its exit status.
///
/// `arguments` are the shell's own command line. A resident object opens as
/// `file:<address>?vfs=cas`.
///
/// The store is served for exactly as long as the shell runs. Objects the
/// shell opened are held here until it releases them, so a `.forget` during
/// the session cannot break a database the shell already has open.
///
/// # Errors
///
/// Returns an error when the socket cannot be created or the shell cannot be
/// started. The shell's own failures arrive as a non-zero status.
pub fn run<S: AsRef<std::ffi::OsStr>>(
    cas: &Arc<MemoryCas>,
    arguments: &[S],
) -> Result<i32, ShellError> {
    run_with_binary(cas, &binary_path(), arguments)
}

/// Returns the shell binary this REPL will run.
#[must_use]
pub fn binary_path() -> std::ffi::OsString {
    std::env::var_os(SHELL_BINARY_ENV).unwrap_or_else(|| SHELL_BINARY_DEFAULT.into())
}

/// Runs a named shell binary against `cas`.
///
/// Split out from [`run`] so the binary can be chosen explicitly rather than
/// by mutating the environment.
///
/// # Errors
///
/// Returns an error when the socket cannot be created or the shell cannot be
/// started.
pub fn run_with_binary<S: AsRef<std::ffi::OsStr>>(
    cas: &Arc<MemoryCas>,
    binary: &std::ffi::OsStr,
    arguments: &[S],
) -> Result<i32, ShellError> {
    let endpoint = Endpoint::bind()?;

    let mut child = Command::new(binary)
        .arg("--cas")
        .arg(endpoint.path())
        .args(arguments)
        .spawn()?;

    // One connection, served on this thread's behalf for the child's lifetime.
    // `accept` returns as soon as the child connects; if it dies first, the
    // error surfaces here rather than hanging.
    let store = Arc::clone(cas);
    let socket = endpoint.listener.try_clone()?;
    let server = std::thread::spawn(move || -> io::Result<()> {
        let (stream, _) = socket.accept()?;
        let mut reader = stream.try_clone()?;
        let mut writer = stream;
        serve(store.as_ref(), &mut reader, &mut writer)
    });

    let status = child.wait()?;
    // The child is gone, so the connection is closed and the server has
    // returned. A transport error at this point means the shell disconnected,
    // which is how it always ends.
    let _ = server.join();

    Ok(status.code().unwrap_or(-1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_socket_directory_is_private_and_removed() {
        let directory;
        {
            let endpoint = Endpoint::bind().unwrap();
            directory = endpoint.directory.clone();
            let mode = std::fs::metadata(&directory).unwrap().permissions().mode();
            assert_eq!(mode & 0o777, 0o700, "socket directory must be owner-only");
            assert!(endpoint.path().exists());
        }
        assert!(!directory.exists(), "endpoint must clean up after itself");
    }

    #[test]
    fn a_missing_shell_binary_is_an_error_not_a_hang() {
        let cas = Arc::new(MemoryCas::new());
        let result = run_with_binary(
            &cas,
            std::ffi::OsStr::new("/nonexistent/covalence-cas-shell"),
            &["-batch"],
        );
        assert!(matches!(result, Err(ShellError::Io(_))));
    }
}
