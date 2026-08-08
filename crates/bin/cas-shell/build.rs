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

    // Provided by libsqlite3-sys (`links = "sqlite3"`, `cargo:include=...`).
    // Its absence means we would compile against some other sqlite3.h, which
    // is exactly the mismatch this crate exists to avoid.
    let include =
        PathBuf::from(env::var_os("DEP_SQLITE3_INCLUDE").expect(
            "DEP_SQLITE3_INCLUDE is unset: this crate must link the bundled libsqlite3-sys",
        ));

    let mut build = cc::Build::new();
    build.file("vendor/shell.c");
    build.include(&include);

    // `shell.c` is a program. Renaming its entry point turns it into a library
    // without patching the vendored source.
    build.define("main", "covalence_sqlite_shell_main");

    // Upstream's hook for exactly this case: "initialization actions on
    // SQLite that occur just before or after sqlite3_initialize(). Use this
    // compile-time option to embed this shell program in larger
    // applications." Mounting the CAS here rather than before entering the
    // shell keeps SQLite uninitialized until the shell says so, which is what
    // its own `verify_uninitialized` check is asserting.
    build.define("SQLITE_SHELL_INIT_PROC", "covalence_shell_init");

    // `exit()` is deliberately left alone. This is a shell process, so a
    // program terminating the process is the correct outcome, and upstream's
    // exit codes and `atexit` handlers survive. Redirecting it would only be
    // necessary if the shell shared an address space with something that had
    // to outlive it, which is exactly what running it separately avoids.

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
