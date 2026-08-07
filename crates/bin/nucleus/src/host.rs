//! The capabilities a WASI guest cannot supply for itself.
//!
//! Compiled for `wasm32-wasip1` this binary *is* the REPL — the same
//! [`covalence_repl::Session`], the same commands, the same output — but two
//! of the things a session asks for cannot be done from inside a sandbox with
//! no sockets and no way to instantiate a module. So they become imports, and
//! whoever runs this wasm supplies them.
//!
//! That is the same arrangement the session already has with its host; this
//! just moves the boundary from a Rust function call to a wasm import.
//!
//! # Why two calls per operation
//!
//! A wasm import returns one number. Returning bytes therefore takes two
//! steps: ask for the operation and get back a length, then hand over a buffer
//! of that length to be filled. The alternative — having the host allocate
//! inside the guest — needs the guest to export an allocator, which is more
//! coupling for no benefit at this size.
//!
//! # Trust
//!
//! The host is not trusted. Fetched bytes are verified against the address
//! that was asked for before being admitted, exactly as in the native binary,
//! so a host that returns the wrong thing is caught rather than believed.

use std::ffi::c_int;

#[allow(unsafe_code, reason = "declares the host's imports")]
#[link(wasm_import_module = "covalence:host")]
unsafe extern "C" {
    /// Fetches a URL.
    ///
    /// Returns the length of the result, or a negative value on failure.
    fn host_fetch(url: *const u8, len: usize) -> i64;

    /// Runs the `SQLite` shell with NUL-separated arguments.
    ///
    /// Returns the length of its combined output, or a negative value if the
    /// shell could not be run at all. The shell's own exit status arrives
    /// through [`host_status`].
    fn host_shell(arguments: *const u8, len: usize) -> i64;

    /// Copies the bytes produced by the last [`host_fetch`] or [`host_shell`].
    ///
    /// `out` must have room for exactly the length that call returned.
    fn host_take(out: *mut u8);

    /// The exit status of the last [`host_shell`].
    fn host_status() -> c_int;
}

/// Failure of a host-provided operation.
#[derive(Debug)]
pub enum HostError {
    /// The host could not fetch the URL.
    Fetch,
    /// The host could not run the shell.
    Shell,
}

impl std::fmt::Display for HostError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fetch => formatter.write_str("the host could not fetch that URL"),
            Self::Shell => formatter.write_str("the host could not run the shell"),
        }
    }
}

impl std::error::Error for HostError {}

/// Reads back whatever the last host call produced.
fn take(length: i64) -> Vec<u8> {
    let Ok(length) = usize::try_from(length) else {
        return Vec::new();
    };
    let mut bytes = vec![0u8; length];
    if length > 0 {
        // SAFETY: `bytes` has exactly `length` writable bytes, which is what
        // the preceding call reported it would write.
        #[allow(unsafe_code, reason = "calls the host's import")]
        unsafe {
            host_take(bytes.as_mut_ptr());
        }
    }
    bytes
}

/// Fetches a URL through the host.
///
/// # Errors
///
/// Returns an error if the host declines.
pub fn fetch(url: &str) -> Result<Vec<u8>, HostError> {
    // SAFETY: `url` is a live byte range of exactly this length.
    #[allow(unsafe_code, reason = "calls the host's import")]
    let length = unsafe { host_fetch(url.as_ptr(), url.len()) };
    if length < 0 {
        return Err(HostError::Fetch);
    }
    Ok(take(length))
}

/// Runs the shell through the host, returning its output and status.
///
/// # Errors
///
/// Returns an error if the host declines to run it at all. A shell which ran
/// and failed reports through its status.
pub fn shell(arguments: &[String]) -> Result<(String, c_int), HostError> {
    // NUL-separated, because argv is a list and a wasm import takes a pointer.
    // Arguments cannot contain NUL: they came from a Rust `String`, and the
    // session's splitter never produces one.
    let packed = arguments.join("\0");
    // SAFETY: `packed` is a live byte range of exactly this length.
    #[allow(unsafe_code, reason = "calls the host's import")]
    let length = unsafe { host_shell(packed.as_ptr(), packed.len()) };
    if length < 0 {
        return Err(HostError::Shell);
    }
    let output = String::from_utf8_lossy(&take(length)).into_owned();
    // SAFETY: reads a value the host set during the call above.
    #[allow(unsafe_code, reason = "calls the host's import")]
    let status = unsafe { host_status() };
    Ok((output, status))
}
