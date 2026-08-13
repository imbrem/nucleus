//! Compiles the upstream shell against the workspace's `SQLite` library.

use std::env;
use std::path::PathBuf;
use std::process::Command;

/// Finds a library in the target compiler's sysroot.
fn library_directory(build: &cc::Build, library: &str) -> Option<PathBuf> {
    let compiler = build.try_get_compiler().ok()?;
    let file = format!("lib{library}.a");
    let output = Command::new(compiler.path())
        .args(compiler.args())
        .arg(format!("-print-file-name={file}"))
        .output()
        .ok()?;
    let path = PathBuf::from(String::from_utf8(output.stdout).ok()?.trim());
    if path.as_os_str() == file.as_str() || !path.is_file() {
        return None;
    }
    path.parent().map(PathBuf::from)
}

fn main() {
    println!("cargo::rerun-if-changed=vendor/shell.c");

    let include =
        PathBuf::from(env::var_os("DEP_SQLITE3_INCLUDE").expect(
            "DEP_SQLITE3_INCLUDE is unset: this crate must link the bundled libsqlite3-sys",
        ));

    let mut build = cc::Build::new();
    build.file("vendor/shell.c");
    build.include(&include);

    build.define("main", "covalence_sqlite_shell_main");
    build.define("SQLITE_SHELL_INIT_PROC", "covalence_shell_init");
    build.define("SQLITE_OMIT_LOAD_EXTENSION", None);
    build.define("SQLITE_NOHAVE_SYSTEM", None);
    build.define("SQLITE_SHELL_IS_UTF8", None);

    build.define("HAVE_READLINE", "0");
    build.define("HAVE_EDITLINE", "0");
    build.define("HAVE_LINENOISE", "0");

    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("wasi") {
        build.define("SQLITE_WASI", None);
        // Upstream uses both spellings around unsupported resource timing.
        build.define("__minux", None);
        build.define("__minix", None);
        for feature in [
            "_WASI_EMULATED_SIGNAL",
            "_WASI_EMULATED_GETPID",
            "_WASI_EMULATED_PROCESS_CLOCKS",
            "_WASI_EMULATED_MMAN",
        ] {
            build.define(feature, None);
        }
        let libraries = [
            "wasi-emulated-signal",
            "wasi-emulated-getpid",
            "wasi-emulated-process-clocks",
            "wasi-emulated-mman",
        ];
        for library in libraries {
            if let Some(directory) = library_directory(&build, library) {
                println!("cargo::rustc-link-search=native={}", directory.display());
            }
            println!("cargo::rustc-link-lib={library}");
        }
    }

    build.warnings(false);
    build.compile("covalence_sqlite_shell");
}
