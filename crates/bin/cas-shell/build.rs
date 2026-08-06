//! Compiles the vendored upstream `SQLite` shell.
//!
//! The shell is compiled *against the `SQLite` this workspace already links*,
//! not against a second copy. `libsqlite3-sys` publishes its amalgamation
//! directory as `DEP_SQLITE3_INCLUDE`, so `shell.c` picks up exactly the
//! `sqlite3.h` matching the library its symbols will resolve to. Sharing one
//! library is the whole point: a VFS registered from Rust is then visible to
//! the shell, because there is only one VFS registry.

use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo::rerun-if-changed=vendor/shell.c");
    println!("cargo::rerun-if-changed=vendor/trampoline.c");

    // Provided by libsqlite3-sys (`links = "sqlite3"`, `cargo:include=...`).
    // Its absence means we would compile against some other sqlite3.h, which
    // is exactly the mismatch this crate exists to avoid.
    let include =
        PathBuf::from(env::var_os("DEP_SQLITE3_INCLUDE").expect(
            "DEP_SQLITE3_INCLUDE is unset: this crate must link the bundled libsqlite3-sys",
        ));

    // Both files go into one archive. They refer to each other — the
    // trampoline calls the shell's renamed `main`, the shell calls the
    // trampoline's `exit` replacement — and two archives with a cycle between
    // them are not reliably resolvable in link order.
    let mut build = cc::Build::new();
    build.file("vendor/shell.c");
    build.file("vendor/trampoline.c");
    build.include(&include);

    // `shell.c` is a program. Renaming its entry point turns it into a library
    // without patching the vendored source.
    build.define("main", "covalence_sqlite_shell_main");

    // Programs terminate by calling `exit()`, which would take the host
    // process with them. Redirecting the whole translation unit sends every
    // such call — `cli_exit`'s and the direct ones in argument parsing — to
    // the trampoline instead. See `vendor/trampoline.c`.
    build.define("exit", "covalence_shell_exit");

    // The shell is a debugging surface, not a capability boundary. These
    // removals keep it from acquiring capabilities the host process does not
    // already intend to hand it.
    build.define("SQLITE_OMIT_LOAD_EXTENSION", None);
    build.define("SQLITE_NOHAVE_SYSTEM", None);
    build.define("SQLITE_SHELL_IS_UTF8", None);

    // No line editing: linking readline or editline would add a dependency
    // that the browser build cannot have, and the difference is only comfort.
    build.define("HAVE_READLINE", "0");
    build.define("HAVE_EDITLINE", "0");
    build.define("HAVE_LINENOISE", "0");

    build.warnings(false);
    build.compile("covalence_sqlite_shell");
}
