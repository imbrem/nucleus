//! Compiles the upstream shell against the workspace's `SQLite` library.

use std::env;
use std::path::PathBuf;
use std::process::Command;

/// Asks the C compiler where a sysroot library lives.
///
/// `-print-file-name` returns the input unchanged when it cannot find the
/// library, which is the case this treats as "not found".
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

    // Use the header matching the linked SQLite library.
    let include =
        PathBuf::from(env::var_os("DEP_SQLITE3_INCLUDE").expect(
            "DEP_SQLITE3_INCLUDE is unset: this crate must link the bundled libsqlite3-sys",
        ));

    let mut build = cc::Build::new();
    build.file("vendor/shell.c");
    build.include(&include);

    // Rename the entry point without patching vendored source.
    build.define("main", "covalence_sqlite_shell_main");

    // Mount the CAS through upstream's pre-initialization hook.
    build.define("SQLITE_SHELL_INIT_PROC", "covalence_shell_init");

    // Disable capabilities not granted to the shell process.
    build.define("SQLITE_OMIT_LOAD_EXTENSION", None);
    build.define("SQLITE_NOHAVE_SYSTEM", None);
    build.define("SQLITE_SHELL_IS_UTF8", None);

    // Keep native and browser builds dependency-compatible.
    build.define("HAVE_READLINE", "0");
    build.define("HAVE_EDITLINE", "0");
    build.define("HAVE_LINENOISE", "0");

    // WASI needs three more.
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("wasi") {
        // Upstream's own WASI flag: skips `pwd.h`, `getpwuid`, and `popen`,
        // none of which wasi-libc has.
        build.define("SQLITE_WASI", None);

        // The `.timer` command uses `getrusage`, which wasi-libc also lacks,
        // and `SQLITE_WASI` does not cover it. Upstream guards that whole
        // block with `__minux` — its own typo for `__minix` — and falls back
        // to no-op timer macros. Both spellings are defined so that a future
        // upstream fixing the typo keeps working; if upstream instead drops
        // the guard, this fails loudly at compile time rather than silently.
        build.define("__minux", None);
        build.define("__minix", None);

        // wasi-libc ships these as opt-in emulations rather than as part of
        // the core library, because none of them is a thing WASI actually has.
        // The shell wants signals for its interrupt handler, `getpid` for
        // temporary names, and process clocks for timing; SQLite wants `mman`
        // for its memory-mapped I/O paths.
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
        // These live in the wasi-libc sysroot, which is wherever the toolchain
        // put it. Ask the compiler rather than guessing, so this survives a
        // different sysroot without a hardcoded path.
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
