//! The upstream `SQLite` shell, linked as a private subprocess library.

use std::ffi::{CString, NulError, c_char, c_int};

// Ensure the shell's SQLite symbols resolve to this library.
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use libsqlite3_sys as _;

#[allow(
    unsafe_code,
    reason = "declares the vendored shell's renamed entry point"
)]
unsafe extern "C" {
    /// `shell.c`'s renamed `main`; it may terminate the process.
    fn covalence_sqlite_shell_main(argc: c_int, argv: *mut *mut c_char) -> c_int;
}

/// Failure to encode shell arguments.
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

/// Runs the shell with arguments excluding `argv[0]`.
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

    // `main` may mutate argv pointers, so keep owned writable slots.
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
