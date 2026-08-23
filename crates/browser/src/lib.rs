//! Browser host for the content-addressed `SQLite` REPL and shell.

use std::collections::HashMap;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_data_cas::{CasObject, ObjectCas, ResidentObject};
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, Step as SqliteStep, ValueType};
use covalence_repl::{Response, Session};
use wasm_bindgen::prelude::*;

mod hol;

pub use hol::HolProver;

/// Generates unique VFS names within one wasm instance.
static NEXT_MOUNT: AtomicU64 = AtomicU64::new(0);

/// A wasm-friendly form of `covalence_repl::Response`.
#[wasm_bindgen]
pub struct Step {
    kind: String,
    text: String,
    address: String,
    arguments: Vec<String>,
}

#[wasm_bindgen]
impl Step {
    /// One of `output`, `fetch`, `shell`, or `quit`.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn kind(&self) -> String {
        self.kind.clone()
    }

    /// Text to show, or the URL to fetch.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn text(&self) -> String {
        self.text.clone()
    }

    /// For `fetch`, the address the bytes must hash to.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn address(&self) -> String {
        self.address.clone()
    }

    /// For `shell`, the arguments to run it with.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn arguments(&self) -> Vec<String> {
        self.arguments.clone()
    }
}

impl Step {
    fn output(text: impl Into<String>) -> Self {
        Self {
            kind: "output".to_owned(),
            text: text.into(),
            address: String::new(),
            arguments: Vec::new(),
        }
    }

    fn bare(kind: &str) -> Self {
        Self {
            kind: kind.to_owned(),
            text: String::new(),
            address: String::new(),
            arguments: Vec::new(),
        }
    }
}

/// The REPL this page runs.
#[wasm_bindgen]
pub struct Repl {
    session: Session,
    /// Objects pinned for a guest such as the WASI shell.
    open: HashMap<u64, ResidentObject>,
    next_handle: u64,
}

#[wasm_bindgen]
impl Repl {
    /// Creates a REPL with an empty local store.
    ///
    /// # Errors
    ///
    /// Returns an error if the mount cannot be registered.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<Self, JsError> {
        let index = NEXT_MOUNT.fetch_add(1, Ordering::Relaxed);
        let mount = if index == 0 {
            covalence_neutron::CAS_VFS_NAME.to_owned()
        } else {
            format!("{}-{index}", covalence_neutron::CAS_VFS_NAME)
        };
        Ok(Self {
            session: Session::with_mount_name(&mount).map_err(to_js)?,
            open: HashMap::new(),
            next_handle: 1,
        })
    }

    /// The banner a terminal prints on startup.
    #[must_use]
    pub fn banner(&self) -> String {
        format!(
            "nucleus: content-addressed SQLite. Store mounted as vfs={}. `.help` for commands.",
            self.session.repl().mount().name()
        )
    }

    /// The `SQLite` VFS name this REPL's store is mounted under.
    #[wasm_bindgen(js_name = mountName)]
    #[must_use]
    pub fn mount_name(&self) -> String {
        self.session.repl().mount().name().as_str().to_owned()
    }

    /// Reads and evaluates one line of input.
    ///
    /// # Errors
    ///
    /// Returns an error if the input does not read, names nothing, or fails. A
    /// failed form is ordinary: show it and keep the prompt.
    pub fn eval(&mut self, line: &str) -> Result<Step, JsError> {
        Ok(match self.session.eval(line).map_err(to_js)? {
            Response::Value(value) => Step::output(value.display()),
            Response::Quit => Step::bare("quit"),
            Response::ReadFile(path) => Step::output(format!(
                "no filesystem here: use the file picker to admit {path:?}"
            )),
            Response::Fetch { url, address } => Step {
                kind: "fetch".to_owned(),
                text: url,
                address: address.hex().to_string(),
                arguments: Vec::new(),
            },
            Response::Shell(arguments) => Step {
                kind: "shell".to_owned(),
                text: String::new(),
                address: String::new(),
                arguments,
            },
        })
    }

    /// Admits bytes the page read from a file picker.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes exceed the admission limit.
    pub fn admit(&self, bytes: &[u8]) -> Result<String, JsError> {
        self.session
            .admit(bytes.to_vec())
            .map(|value| value.display())
            .map_err(to_js)
    }

    /// Admits bytes the page fetched, refusing any that do not match.
    ///
    /// # Errors
    ///
    /// Returns an error if `expected` is not an address, or the bytes hash to
    /// something else.
    #[wasm_bindgen(js_name = admitVerified)]
    pub fn admit_verified(&self, expected: &str, bytes: &[u8]) -> Result<String, JsError> {
        self.session
            .admit_verified(address(expected)?, bytes.to_vec())
            .map(|value| value.display())
            .map_err(to_js)
    }

    /// Returns every resident address.
    #[must_use]
    pub fn addresses(&self) -> Vec<String> {
        self.session
            .repl()
            .addresses()
            .into_iter()
            .map(|address| address.hex().to_string())
            .collect()
    }

    /// Returns `{objects, bytes, largest}` as JSON.
    #[must_use]
    pub fn stats(&self) -> String {
        let stats = self.session.repl().stats();
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
        Ok(self.session.repl().uri(self::address(address)?))
    }

    /// Runs a query against a resident object and returns JSON.
    ///
    /// A convenience for a page. The shell is the real answer.
    ///
    /// # Errors
    ///
    /// Returns an error if the address does not resolve, if it was not opened
    /// through the mount, or if the SQL fails.
    pub fn query(&mut self, address: &str, sql: &str) -> Result<String, JsError> {
        let repl = self.session.repl_mut();
        let id = repl.open_address(self::address(address)?).map_err(to_js)?;
        let result = {
            let connection = repl.connection(id).map_err(to_js)?;
            run(connection, sql)
        };
        // The connection was opened for this query; do not accumulate them.
        let _ = repl.close(id);
        result
    }

    /// Opens an address for a wasm guest, returning `-1` when absent.
    ///
    /// # Errors
    ///
    /// Returns an error if `address` is not an address, or the store fails.
    #[wasm_bindgen(js_name = openObject)]
    pub fn open_object(&mut self, address: &str) -> Result<f64, JsError> {
        let address = self::address(address)?;
        let Some(object) = self.session.store().open(address).map_err(to_js)? else {
            return Ok(-1.0);
        };
        let handle = self.next_handle;
        self.next_handle += 1;
        self.open.insert(handle, object);
        Ok(handle_to_js(handle))
    }

    /// Returns an open object's length, or `-1` for an unknown handle.
    #[wasm_bindgen(js_name = objectLength)]
    #[must_use]
    pub fn object_length(&self, handle: f64) -> f64 {
        self.open
            .get(&handle_from_js(handle))
            .map_or(-1.0, |object| handle_to_js(object.len()))
    }

    /// Reads exactly `len` bytes from `offset` of an open object.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown handle or a range outside the object.
    /// A short read is never returned as success: `SQLite` would read the
    /// difference as zeroes and see a corrupt database.
    #[wasm_bindgen(js_name = readObject)]
    pub fn read_object(&self, handle: f64, offset: f64, len: f64) -> Result<Vec<u8>, JsError> {
        let object = self
            .open
            .get(&handle_from_js(handle))
            .ok_or_else(|| JsError::new("unknown object handle"))?;
        let start = handle_from_js(offset);
        let end = start.saturating_add(handle_from_js(len));
        Ok(object.read(start..end).map_err(to_js)?.to_vec())
    }

    /// Releases an open object.
    #[wasm_bindgen(js_name = closeObject)]
    pub fn close_object(&mut self, handle: f64) {
        self.open.remove(&handle_from_js(handle));
    }
}

/// Converts a handle or length for `JavaScript`.
///
/// Saturates rather than wrapping: a value past `f64`'s exact range would be a
/// silently wrong handle, and there is no honest number to return.
#[allow(
    clippy::cast_precision_loss,
    reason = "saturated below the exact range"
)]
fn handle_to_js(value: u64) -> f64 {
    const EXACT: u64 = 1 << 53;
    if value >= EXACT { -1.0 } else { value as f64 }
}

/// Converts a handle, offset or length back from `JavaScript`.
///
/// A negative or non-finite input becomes 0, which no handle uses and which
/// every range check rejects.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "non-finite and negative inputs are mapped to 0"
)]
fn handle_from_js(value: f64) -> u64 {
    if value.is_finite() && value >= 0.0 {
        value as u64
    } else {
        0
    }
}

fn address(text: &str) -> Result<O256, JsError> {
    O256::from_str(text.trim())
        .map_err(|error| JsError::new(&format!("{text:?} is not an address: {error}")))
}

fn to_js(error: impl std::fmt::Display) -> JsError {
    JsError::new(&error.to_string())
}

/// Runs `sql` and renders the result as JSON.
fn run(connection: &Connection, sql: &str) -> Result<String, JsError> {
    let mut statement = covalence_lib_sqlite::Statement::prepare(connection, sql).map_err(to_js)?;

    let column_count = statement.column_count();
    let columns: Vec<String> = (0..column_count)
        .map(|index| statement.column_name(index).unwrap_or_default().to_owned())
        .collect();

    let mut rows: Vec<Vec<String>> = Vec::new();
    while statement.step().map_err(to_js)? == SqliteStep::Row {
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
