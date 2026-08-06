//! A small SQL shell over [`covalence_lib_sqlite`].
//!
//! This is **not** the upstream `sqlite3` command-line program and does not
//! try to be. It is the subset a content-addressed REPL actually needs — open
//! a database by URI, type SQL at it, look at the answer — written in Rust so
//! that it links no C of its own, needs no build script, and builds for
//! `wasm32-unknown-unknown`.
//!
//! # Trust
//!
//! The shell is outside the trusted computing base. It runs arbitrary SQL
//! against whatever connection it is pointed at, and nothing may depend on it
//! for a correctness claim. Unlike an embedded `shell.c`, it also cannot
//! corrupt the host: the crate is `#![deny(unsafe_code)]` apart from a single
//! documented FFI call to `sqlite3_complete`, which reads one NUL-terminated
//! string and returns an `int`.
//!
//! # What it is not
//!
//! Upstream has 81 dot commands, 23 output modes, an archive tool, a query
//! planner advisor, a database recovery engine and a corruption-tolerant
//! `.dump`. This has 13 dot commands and 5 output modes. See the crate's
//! issue for the measured comparison; the short version is that anything
//! diagnostic, anything that writes, and anything that reaches the filesystem
//! beyond `.read` and `.output` is deliberately absent.
//!
//! # Example
//!
//! ```
//! use covalence_lib_sql_shell::Shell;
//! use covalence_lib_sqlite::Connection;
//!
//! let output = covalence_lib_sql_shell::SharedBuffer::new();
//! let mut shell = Shell::new(
//!     Connection::open_in_memory().unwrap(),
//!     Box::new(output.clone()),
//!     Box::new(covalence_lib_sql_shell::SharedBuffer::new()),
//! );
//! shell.run(&mut "SELECT 1+1;".as_bytes()).unwrap();
//! assert_eq!(output.take_string(), "2\n");
//! ```
//!
//! Wiring it to a terminal is the same call with real handles:
//!
//! ```no_run
//! # use covalence_lib_sql_shell::Shell;
//! # use covalence_lib_sqlite::Connection;
//! let mut shell = Shell::new(
//!     Connection::open_in_memory().unwrap(),
//!     Box::new(std::io::stdout()),
//!     Box::new(std::io::stderr()),
//! );
//! shell.set_interactive(true);
//! shell.run(&mut std::io::stdin().lock()).unwrap();
//! ```

mod buffer;
mod command;
mod complete;
mod mode;
mod render;
mod shell;
mod value;

pub use buffer::SharedBuffer;
pub use command::{Command, ParseError, split_arguments};
pub use complete::is_complete;
pub use mode::{Mode, UnknownMode};
pub use shell::Shell;
pub use value::Cell;
