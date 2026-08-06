//! The vendored upstream `SQLite` command-line shell, as a library.
//!
//! This crate does not implement a shell. It vendors `shell.c` from the
//! `SQLite` amalgamation, renames its entry point, and links it against the
//! same `SQLite` this binary uses — which is *this process's* `SQLite`, not the
//! kernel's. That is the difference from embedding it in the host: the shell
//! and everything it can reach live here.
//!
//! Two compile-time redirects do all the adaptation, so the vendored source
//! stays unmodified:
//!
//! - `-Dmain=covalence_sqlite_shell_main` turns the program into a library.
//! - `-Dexit=covalence_shell_exit` turns termination into a return, via the
//!   `setjmp` landing pad in `vendor/trampoline.c`. `shell.c` is a program and
//!   programs call `exit()`; argument parsing and several fatal paths call it
//!   directly rather than through `cli_exit`, so a whole-translation-unit
//!   redirect is what catches them all.
//!
//! It is compiled without extension loading and without `system()`, so it
//! cannot acquire capabilities this process was not already given — and this
//! process was given only a CAS socket.

use std::ffi::{CString, NulError, c_char, c_int};

// The shell's `sqlite3_*` symbols resolve to this library. Naming it here is
// load-bearing: an unreferenced dependency is not linked, and its native
// library directives would not reach this crate's link.
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use libsqlite3_sys as _;

#[allow(unsafe_code, reason = "declares the vendored shell's trampoline")]
unsafe extern "C" {
    /// The trampoline around `shell.c`'s renamed `main`. Returns the shell's
    /// exit status whether the shell returned or tried to terminate the
    /// process. See `vendor/trampoline.c`.
    fn covalence_sqlite_shell_run(argc: c_int, argv: *mut *mut c_char) -> c_int;
}

/// Failure to enter the shell.
///
/// This covers only arguments the shell can never see. Once the shell runs,
/// its own failures are reported through its exit status.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShellError {
    /// An argument contains an interior NUL byte.
    InteriorNul {
        /// Index of the offending argument, counting `argv[0]`.
        argument: usize,
    },
    /// More arguments were supplied than `argc` can express.
    TooManyArguments {
        /// Number of arguments supplied.
        count: usize,
    },
}

impl std::fmt::Display for ShellError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InteriorNul { argument } => {
                write!(
                    formatter,
                    "argument {argument} contains an interior NUL byte"
                )
            }
            Self::TooManyArguments { count } => {
                write!(formatter, "{count} arguments exceed the C argument limit")
            }
        }
    }
}

impl std::error::Error for ShellError {}

/// Runs the embedded `SQLite` shell and returns its exit status.
///
/// `arguments` are the shell's own arguments, *excluding* `argv[0]`, and use
/// the ordinary `sqlite3` command line: a database argument, `-readonly`,
/// `-cmd`, `.dump`, and so on. A URI naming a registered VFS works here
/// exactly as it does at a `sqlite3` prompt.
///
/// This call takes over the process's standard input and output for as long
/// as the shell runs, and returns when the shell exits.
///
/// # Errors
///
/// Returns [`ShellError`] when an argument cannot be passed to C at all. Every
/// other failure — an unopenable database, a SQL error — is the shell's, and
/// arrives as a non-zero exit status.
pub fn run<S: AsRef<str>>(arguments: &[S]) -> Result<i32, ShellError> {
    let mut owned = Vec::with_capacity(arguments.len() + 1);
    owned.push(argv0());
    for (index, argument) in arguments.iter().enumerate() {
        owned.push(CString::new(argument.as_ref()).map_err(|_: NulError| {
            ShellError::InteriorNul {
                // `argv[0]` occupies index 0, so caller arguments start at 1.
                argument: index + 1,
            }
        })?);
    }

    let argc = c_int::try_from(owned.len()).map_err(|_| ShellError::TooManyArguments {
        count: arguments.len(),
    })?;

    // `main` takes `char **`. The shell may permute or rewrite these slots, so
    // they must be genuinely writable pointers into memory we own for the
    // whole call. A trailing null keeps the array conventional.
    let mut pointers: Vec<*mut c_char> = owned
        .iter()
        .map(|argument| argument.as_ptr().cast_mut())
        .collect();
    pointers.push(std::ptr::null_mut());

    // SAFETY: `pointers` holds `argc` valid, NUL-terminated pointers followed
    // by a null terminator, and `owned` keeps every one of them alive for the
    // duration of the call.
    #[allow(
        unsafe_code,
        reason = "calls the vendored shell through its trampoline"
    )]
    let status = unsafe { covalence_sqlite_shell_run(argc, pointers.as_mut_ptr()) };
    Ok(status)
}

/// The program name the shell reports in its own messages.
fn argv0() -> CString {
    CString::new("sqlite3").unwrap_or_else(|_| unreachable!("literal contains no NUL"))
}

#[cfg(test)]
mod tests {
    use std::sync::{Mutex, MutexGuard};

    use super::*;

    /// `shell.c` keeps its state in file-scope variables, and the trampoline's
    /// landing pad is a single `jmp_buf`. One invocation at a time.
    static SHELL: Mutex<()> = Mutex::new(());

    fn exclusive() -> MutexGuard<'static, ()> {
        SHELL
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Runs the shell with output discarded. `-batch` keeps it off the
    /// terminal.
    fn quiet(arguments: &[&str]) -> i32 {
        let mut argv = vec!["-batch", "-cmd", ".output /dev/null"];
        argv.extend_from_slice(arguments);
        run(&argv).unwrap()
    }

    #[test]
    fn runs_a_statement_against_an_in_memory_database() {
        let _guard = exclusive();
        assert_eq!(quiet(&[":memory:", "SELECT 1;"]), 0);
    }

    #[test]
    fn reports_a_failing_statement() {
        let _guard = exclusive();
        assert_ne!(quiet(&[":memory:", "SELECT * FROM missing;"]), 0);
    }

    #[test]
    fn a_terminating_shell_path_returns_instead_of_exiting() {
        let _guard = exclusive();

        // An unrecognised option is one of `shell.c`'s direct `exit()` calls,
        // reached during argument parsing before `cli_exit` exists to help.
        assert_ne!(quiet(&[":memory:", "--no-such-option"]), 0);

        // The assertion is that this line runs at all: without the trampoline
        // the test binary would already have exited. Running the shell again
        // afterwards shows the landing pad was left reusable.
        assert_eq!(quiet(&[":memory:", "SELECT 1;"]), 0);
    }

    #[test]
    fn rejects_arguments_with_interior_nul() {
        assert_eq!(
            run(&[":memory:", "-batch", "SELECT\u{0}1;"]).unwrap_err(),
            ShellError::InteriorNul { argument: 3 }
        );
    }
}
