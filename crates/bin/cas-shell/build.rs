//! Compiles the upstream shell against the workspace's `SQLite` library.

use std::env;
use std::path::PathBuf;

fn main() {
    println!("cargo::rerun-if-changed=vendor/shell.c");
    println!("cargo::rerun-if-changed=vendor/trampoline.c");

    // Use the header matching the linked SQLite library.
    let include =
        PathBuf::from(env::var_os("DEP_SQLITE3_INCLUDE").expect(
            "DEP_SQLITE3_INCLUDE is unset: this crate must link the bundled libsqlite3-sys",
        ));

    // Keep the mutually dependent shell and trampoline in one archive.
    let mut build = cc::Build::new();
    build.file("vendor/shell.c");
    build.file("vendor/trampoline.c");
    build.include(&include);

    // Rename the entry point without patching vendored source.
    build.define("main", "covalence_sqlite_shell_main");

    // Route process exit through the trampoline.
    build.define("exit", "covalence_shell_exit");

    // Disable capabilities not granted to the shell process.
    build.define("SQLITE_OMIT_LOAD_EXTENSION", None);
    build.define("SQLITE_NOHAVE_SYSTEM", None);
    build.define("SQLITE_SHELL_IS_UTF8", None);

    // Keep native and browser builds dependency-compatible.
    build.define("HAVE_READLINE", "0");
    build.define("HAVE_EDITLINE", "0");
    build.define("HAVE_LINENOISE", "0");

    build.warnings(false);
    build.compile("covalence_sqlite_shell");
}
