//! A content-addressed `SQLite` kernel, in the browser.
//!
//! This is a whole kernel compiled to wasm: a store, a mounted VFS, and
//! `SQLite` itself. A page can put bytes in, get an address back, and open that
//! address as a database — with no server involved at all.
//!
//! It is also a client. Objects can be admitted from a *remote* kernel over
//! HTTP, which is the other half of the demo: one design, two places it runs.
//!
//! # Verification is the whole point of the remote path
//!
//! [`Kernel::admit`] takes the address the caller expected and refuses bytes
//! that do not hash to it. That is what makes an untrusted HTTP source usable:
//! the URL is a hint about where bytes might be, and the address is what says
//! whether they are the right ones. A server that returns something else — or
//! a cache, or a proxy, or an attacker — is caught here rather than believed.
//!
//! Whole objects are fetched and hashed. Verifying a *range* without fetching
//! the whole object needs BLAKE3 range proofs, tracked in #442; until those
//! exist, whole-object verification is the honest option and is what this does.
//!
//! # Trust
//!
//! Nothing here is trusted. [`Kernel::query`] runs arbitrary SQL, which is the
//! browser's stand-in for the shell until the shell itself runs here. It sits
//! outside the trusted core for exactly the reason the shell does.

use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, Step, ValueType};
use covalence_repl::Repl;
use wasm_bindgen::prelude::*;

/// Names handed to successive kernels in one wasm instance.
///
/// `SQLite`'s VFS registry is process-global and permanent, so a second kernel
/// cannot reuse the first's mount name. The first kernel gets the conventional
/// `cas`, because that is what a page will have in its URLs; later ones get a
/// distinct name, which [`Kernel::uri`] reports.
static NEXT_MOUNT: AtomicU64 = AtomicU64::new(0);

/// A kernel running in this page.
#[wasm_bindgen]
pub struct Kernel {
    repl: Repl,
    mount: String,
}

#[wasm_bindgen]
impl Kernel {
    /// Creates a kernel with an empty store, mounted as `vfs=cas`.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<Self, JsError> {
        let index = NEXT_MOUNT.fetch_add(1, Ordering::Relaxed);
        let mount = if index == 0 {
            covalence_lib_sqlite::vfs::CAS_VFS_NAME.to_owned()
        } else {
            format!("{}-{index}", covalence_lib_sqlite::vfs::CAS_VFS_NAME)
        };
        Ok(Self {
            repl: Repl::with_mount_name(&mount, false).map_err(to_js)?,
            mount,
        })
    }

    /// The `SQLite` VFS name this kernel's store is mounted under.
    #[wasm_bindgen(js_name = mountName)]
    #[must_use]
    pub fn mount_name(&self) -> String {
        self.mount.clone()
    }

    /// Admits bytes and returns their address.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes exceed the store's admission limit.
    pub fn put(&self, bytes: &[u8]) -> Result<String, JsError> {
        let address = self.repl.put(bytes.to_vec()).map_err(to_js)?;
        Ok(address.hex().to_string())
    }

    /// Admits bytes only if they hash to `expected`.
    ///
    /// This is the check that makes a remote source usable without trusting
    /// it. Bytes which do not match are refused and not stored.
    ///
    /// # Errors
    ///
    /// Returns an error if `expected` is not an address, if the bytes hash to
    /// something else, or if they exceed the admission limit.
    pub fn admit(&self, expected: &str, bytes: &[u8]) -> Result<String, JsError> {
        let expected = address(expected)?;
        let actual = O256::from_bytes(bytes);
        if actual != expected {
            return Err(JsError::new(&format!(
                "content does not match its address: expected {}, received {}",
                expected.hex(),
                actual.hex()
            )));
        }
        let stored = self.repl.put(bytes.to_vec()).map_err(to_js)?;
        Ok(stored.hex().to_string())
    }

    /// Drops an address, reporting whether it resolved.
    ///
    /// Databases already open through it keep working.
    ///
    /// # Errors
    ///
    /// Returns an error if `address` is not an address.
    pub fn forget(&self, address: &str) -> Result<bool, JsError> {
        Ok(self.repl.forget(self::address(address)?))
    }

    /// Returns every resident address.
    #[wasm_bindgen(js_name = addresses)]
    #[must_use]
    pub fn addresses(&self) -> Vec<String> {
        self.repl
            .addresses()
            .into_iter()
            .map(|address| address.hex().to_string())
            .collect()
    }

    /// Returns `{objects, bytes, largest}` as JSON.
    #[must_use]
    pub fn stats(&self) -> String {
        let stats = self.repl.stats();
        format!(
            r#"{{"objects":{},"bytes":{},"largest":{}}}"#,
            stats.objects, stats.bytes, stats.largest
        )
    }

    /// Returns the `SQLite` URI which opens `address` through the mount.
    ///
    /// # Errors
    ///
    /// Returns an error if `address` is not an address.
    pub fn uri(&self, address: &str) -> Result<String, JsError> {
        Ok(self.repl.uri(self::address(address)?))
    }

    /// Runs a query against a resident object and returns JSON.
    ///
    /// The result is `{"columns": [...], "rows": [[...]]}`. This is the
    /// browser's stand-in for the shell and is outside the trusted core.
    ///
    /// # Errors
    ///
    /// Returns an error if the address does not resolve, if it was not opened
    /// through the mount, or if the SQL fails.
    pub fn query(&mut self, address: &str, sql: &str) -> Result<String, JsError> {
        let id = self
            .repl
            .open_address(self::address(address)?)
            .map_err(to_js)?;
        let result = {
            let connection = self.repl.connection(id).map_err(to_js)?;
            run(connection, sql)
        };
        // The connection was opened for this query; do not accumulate them.
        let _ = self.repl.close(id);
        result
    }
}

/// Runs `sql` and renders the result as JSON.
fn run(connection: &Connection, sql: &str) -> Result<String, JsError> {
    let mut statement = connection.prepare(sql).map_err(to_js)?;

    let column_count = statement.column_count();
    let columns: Vec<String> = (0..column_count)
        .map(|index| statement.column_name(index).unwrap_or_default().to_owned())
        .collect();

    let mut rows: Vec<Vec<String>> = Vec::new();
    while statement.step().map_err(to_js)? == Step::Row {
        rows.push(
            (0..column_count)
                .map(|index| encode(&statement, index))
                .collect(),
        );
    }

    let columns = columns.iter().map(|name| quote(name)).collect::<Vec<_>>();
    let rows = rows
        .iter()
        .map(|row| format!("[{}]", row.join(",")))
        .collect::<Vec<_>>();
    Ok(format!(
        r#"{{"columns":[{}],"rows":[{}]}}"#,
        columns.join(","),
        rows.join(",")
    ))
}

/// Renders one column value as a JSON scalar.
fn encode(statement: &covalence_lib_sqlite::Statement, index: i32) -> String {
    let value = statement.column(index);
    match value.value_type() {
        ValueType::Null => "null".to_owned(),
        ValueType::Integer => value.as_integer().unwrap_or_default().to_string(),
        ValueType::Real => {
            let number = value.as_real().unwrap_or_default();
            // JSON has no infinity or NaN.
            if number.is_finite() {
                number.to_string()
            } else {
                "null".to_owned()
            }
        }
        ValueType::Text => quote(value.as_str().unwrap_or_default()),
        // A blob is not text; render its length rather than mangling bytes.
        ValueType::Blob => quote(&format!(
            "<{} byte blob>",
            value.as_bytes().unwrap_or_default().len()
        )),
    }
}

/// Escapes a string as a JSON string literal.
fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            // Control characters must be escaped; everything else is UTF-8.
            character if (character as u32) < 0x20 => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\u{:04x}", character as u32);
            }
            character => out.push(character),
        }
    }
    out.push('"');
    out
}

fn address(text: &str) -> Result<O256, JsError> {
    O256::from_str(text.trim())
        .map_err(|error| JsError::new(&format!("{text:?} is not an address: {error}")))
}

fn to_js(error: impl std::fmt::Display) -> JsError {
    JsError::new(&error.to_string())
}
