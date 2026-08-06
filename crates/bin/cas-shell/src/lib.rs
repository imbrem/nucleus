//! The vendored upstream `SQLite` command-line shell, as a library.
//!
//! This crate does not implement a shell. It vendors `shell.c` from the
//! `SQLite` amalgamation, renames its entry point, and links it against this
//! process's `SQLite` — which is *this* process's, not the kernel's. That is
//! the difference from embedding it in the host: the shell and everything it
//! can reach live here.
//!
//! One compile-time redirect does all the adaptation, so the vendored source
//! stays unmodified: `-Dmain=covalence_sqlite_shell_main` turns the program
//! into something callable.
//!
//! # `exit` is left alone
//!
//! `shell.c` is a program, and programs terminate by calling `exit()` —
//! `cli_exit` does, and so do several paths in argument parsing. That is
//! correct here. This process exists to be the shell, so a fatal shell path
//! ending it is the right outcome, upstream's exit codes reach the parent
//! unchanged, and `atexit` handlers run.
//!
//! Redirecting `exit` would only be necessary if the shell shared an address
//! space with something that had to outlive it. Running it separately removes
//! that requirement rather than working around it, which also removes the
//! `setjmp` landing pad, the allocations it leaked on every fatal path, and
//! the question of what `shell.c`'s file-scope state looks like on a second
//! entry.
//!
//! [`run`] therefore **may not return**. That is a property of the shell, not
//! a defect, and it is why this is a private library of one binary rather than
//! something general.
//!
//! # Trust
//!
//! The shell is outside the trusted computing base and nothing may depend on
//! it for a correctness claim. It is compiled without extension loading and
//! without `system()`, so it cannot acquire capabilities this process was not
//! given — and this process was given a CAS socket and nothing else.

/// A [`covalence_data_cas::Cas`] provided by a WASI host.
#[cfg(target_os = "wasi")]
pub mod wasi;

use std::ffi::{CString, NulError, c_char, c_int};

// The shell's `sqlite3_*` symbols resolve to this library. Naming it here is
// load-bearing: an unreferenced dependency is not linked, and its native
// library directives would not reach this crate's link.
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use libsqlite3_sys as _;

#[allow(
    unsafe_code,
    reason = "declares the vendored shell's renamed entry point"
)]
unsafe extern "C" {
    /// `shell.c`'s `main`, renamed at compile time by the build script.
    ///
    /// May terminate the process rather than returning.
    fn covalence_sqlite_shell_main(argc: c_int, argv: *mut *mut c_char) -> c_int;
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

/// Runs the vendored `SQLite` shell.
///
/// `arguments` are the shell's own arguments, *excluding* `argv[0]`, and use
/// the ordinary `sqlite3` command line: a database argument, `-readonly`,
/// `-cmd`, `.dump`, and so on. A URI naming a registered VFS works here
/// exactly as it does at a `sqlite3` prompt.
///
/// This call takes over the process's standard input and output. It returns
/// the shell's status when the shell returns, and **terminates the process**
/// on the shell's fatal paths — see the module documentation.
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
    #[allow(unsafe_code, reason = "calls the vendored shell's renamed entry point")]
    let status = unsafe { covalence_sqlite_shell_main(argc, pointers.as_mut_ptr()) };
    Ok(status)
}

/// The program name the shell reports in its own messages.
fn argv0() -> CString {
    CString::new("sqlite3").unwrap_or_else(|_| unreachable!("literal contains no NUL"))
}
