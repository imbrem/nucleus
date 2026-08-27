//! Internal implementations of Buck actions.
//!
//! The checked-in `BUCK` graph owns dependencies, invalidation, and outputs.
//! These functions only perform individual actions requested by that graph.
//! They are not a stable developer-facing API; use the public `glu build`,
//! `glu test`, and `glu docs` commands instead.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::{self, Command},
};

use color_eyre::eyre::{Result, WrapErr, bail};

use crate::{
    loc,
    runner::{Runner, copy_dir},
};

impl Runner {
    pub(crate) fn artifact_loc(&self, out: &Path) -> Result<()> {
        loc::write_to(self.root(), &absolute(out)?, self.verbose() > 0)
    }

    pub(crate) fn artifact_rustdoc(&self, out: &Path) -> Result<()> {
        let out = absolute(out)?;
        let target = artifact_temp(&out, "rustdoc-target")?;
        self.run(
            "document production",
            "cargo",
            [
                "--locked",
                "doc",
                "--target-dir",
                as_utf8(&target, "temporary target")?,
                "--workspace",
                "--no-deps",
            ],
        )?;
        copy_dir(&target.join("doc"), &out)
    }

    pub(crate) fn artifact_wasm(&self, out: &Path) -> Result<()> {
        let out = absolute(out)?;
        let target = artifact_temp(&out, "wasm-target")?;
        let staged = artifact_temp(&out, "wasm-package")?;
        let package = self.root().join("packages/nucleus");
        self.run(
            "compile the browser kernel for Wasm",
            "cargo",
            [
                "--locked",
                "build",
                "--target-dir",
                as_utf8(&target, "temporary target")?,
                "-p",
                "covalence-browser",
                "--target",
                "wasm32-unknown-unknown",
            ],
        )?;
        let generated = staged.join("generated");
        fs::create_dir_all(&generated).wrap_err("could not create Wasm output directory")?;
        self.run(
            "generate Wasm bindings",
            "wasm-bindgen",
            [
                as_utf8(
                    &target.join("wasm32-unknown-unknown/debug/covalence_browser.wasm"),
                    "Wasm",
                )?,
                "--out-dir",
                as_utf8(&generated, "Wasm output")?,
                "--out-name",
                "nucleus",
                "--target",
                "web",
            ],
        )?;
        self.artifact_shell(&generated)?;
        self.artifact_proof_host(&generated)?;

        // Stage the package so this build uses its own configuration.
        copy_dir(&package.join("src"), &staged.join("src"))?;
        for dependency in ["jco", "jco-transpile", "preview2-shim"] {
            copy_dir(
                &package
                    .join("node_modules/@bytecodealliance")
                    .join(dependency),
                &staged
                    .join("node_modules/@bytecodealliance")
                    .join(dependency),
            )?;
        }
        fs::copy(package.join("tsconfig.json"), staged.join("tsconfig.json"))
            .wrap_err("could not stage tsconfig.json")?;
        let dist = out.join("dist");
        fs::create_dir_all(&dist).wrap_err("could not create TypeScript output directory")?;
        self.run(
            "compile TypeScript wrapper",
            "pnpm",
            [
                "--filter",
                "@nucleus/nucleus",
                "exec",
                "tsc",
                "--project",
                as_utf8(&staged.join("tsconfig.json"), "TypeScript project")?,
                "--outDir",
                as_utf8(&dist, "TypeScript output")?,
            ],
        )?;
        copy_dir(&generated, &out.join("generated"))
    }

    /// Stage the `covalence` Python package: hand-written sources plus the
    /// compiled extension module beside them.
    ///
    /// Cargo compiles it rather than Buck. `rust_library` produces an rlib, so
    /// there is no Rust rule that emits something an interpreter can import,
    /// and `pyo3`'s build script needs `links` metadata Buck's prelude
    /// discards. Same shape as `artifact_wasm`, for the same reason.
    ///
    /// Built with `extension-module`, which is what a wheel ships: no libpython
    /// to link, Python symbols resolved by the interpreter doing the loading.
    pub(crate) fn artifact_python(&self, out: &Path) -> Result<()> {
        let out = absolute(out)?;
        let target = artifact_temp(&out, "python-target")?;
        self.run(
            "build Python extension",
            "cargo",
            [
                "--locked",
                "build",
                "--target-dir",
                as_utf8(&target, "temporary target")?,
                "-p",
                "covalence-ffi-python",
                "--features",
                "extension-module",
            ],
        )?;

        let package = out.join("covalence");
        copy_dir(
            &self.root().join("crates/ffi/python/python/covalence"),
            &package,
        )?;
        // `.abi3.so` rather than a bare `.so`, because the stable ABI is what
        // this is built against and the name is the only place that shows.
        // CPython accepts the suffix on every platform that uses `.so`.
        let (built, staged) = extension_names();
        fs::copy(target.join("debug").join(built), package.join(staged))
            .wrap_err("could not stage the compiled extension module")?;
        Ok(())
    }

    fn artifact_shell(&self, generated: &Path) -> Result<()> {
        let temp = env::temp_dir();
        let temp = if temp.is_absolute() && !temp.starts_with(self.root()) {
            temp
        } else {
            // Buck may place TMPDIR on the workspace bind mount.
            PathBuf::from("/tmp")
        };
        let component_target = temp.join(format!("nucleus-component-target-{}", process::id()));
        fs::create_dir_all(&component_target)
            .wrap_err("could not create component target directory")?;
        let result = (|| {
            self.run_with_env(
                "compile the SQLite shell component",
                "cargo",
                [
                    "component",
                    "build",
                    "--locked",
                    "--target-dir",
                    as_utf8(&component_target, "temporary target")?,
                    "--profile",
                    "wasm-release",
                    "-p",
                    "covalence-bin-cas-shell",
                    "--target",
                    "wasm32-wasip2",
                    "--lib",
                ],
                &[
                    ("CARGO_TARGET_DIR", component_target.as_os_str()),
                    ("TMPDIR", component_target.as_os_str()),
                ],
            )?;
            self.run(
                "generate SQLite shell bindings",
                "pnpm",
                [
                    "--filter",
                    "@nucleus/nucleus",
                    "exec",
                    "jco",
                    "transpile",
                    as_utf8(
                        &component_target
                            .join("wasm32-wasip2/wasm-release/covalence_bin_cas_shell.wasm"),
                        "shell component",
                    )?,
                    "--out-dir",
                    as_utf8(&generated.join("shell"), "shell output")?,
                    "--name",
                    "shell",
                    "--async-mode",
                    "jspi",
                    "--async-imports",
                    "covalence:sqlite-shell/read-only-vfs#open",
                    "covalence:sqlite-shell/read-only-vfs#[method]file.size",
                    "covalence:sqlite-shell/read-only-vfs#[method]file.read-at",
                    "--async-exports",
                    "run",
                    "--map",
                    "covalence:sqlite-shell/read-only-vfs=../../dist/vfs-host.js",
                ],
            )
        })();
        let cleanup = fs::remove_dir_all(&component_target)
            .wrap_err("could not remove component target directory");
        result.and(cleanup)
    }

    fn artifact_proof_host(&self, generated: &Path) -> Result<()> {
        let temp = env::temp_dir();
        let temp = if temp.is_absolute() && !temp.starts_with(self.root()) {
            temp
        } else {
            PathBuf::from("/tmp")
        };
        let component_target = temp.join(format!("nucleus-proof-host-target-{}", process::id()));
        fs::create_dir_all(&component_target)
            .wrap_err("could not create proof host target directory")?;
        let result = (|| {
            self.run_with_env(
                "compile the proof host component",
                "cargo",
                [
                    "build",
                    "--locked",
                    "--target",
                    "wasm32-unknown-unknown",
                    "--target-dir",
                    as_utf8(&component_target, "temporary target")?,
                    "--profile",
                    "wasm-release",
                    "-p",
                    "covalence-proof-host",
                ],
                &[
                    ("CARGO_TARGET_DIR", component_target.as_os_str()),
                    ("TMPDIR", component_target.as_os_str()),
                ],
            )?;
            let core = component_target
                .join("wasm32-unknown-unknown/wasm-release/covalence_proof_host.wasm");
            let component = component_target.join("covalence_proof_host.component.wasm");
            self.run(
                "wrap the proof host component",
                "wasm-tools",
                [
                    "component",
                    "new",
                    as_utf8(&core, "proof host core module")?,
                    "-o",
                    as_utf8(&component, "proof host component")?,
                ],
            )?;
            self.run(
                "generate proof host bindings",
                "pnpm",
                [
                    "--filter",
                    "@nucleus/nucleus",
                    "exec",
                    "jco",
                    "transpile",
                    as_utf8(&component, "proof host component")?,
                    "--out-dir",
                    as_utf8(&generated.join("proof-host"), "proof host output")?,
                    "--name",
                    "host",
                    "--async-mode",
                    "jspi",
                ],
            )
        })();
        let cleanup = fs::remove_dir_all(&component_target)
            .wrap_err("could not remove proof host target directory");
        result.and(cleanup)
    }

    pub(crate) fn artifact_docs(
        &self,
        metadata: [(&Path, &str); 2],
        loc: &Path,
        rustdoc: &Path,
        out: &Path,
    ) -> Result<()> {
        let metadata = metadata
            .map(|(path, name)| absolute(path).map(|path| (path, name)))
            .into_iter()
            .collect::<Result<Vec<_>>>()?;
        let loc = absolute(loc)?;
        let rustdoc = absolute(rustdoc)?;
        let out = absolute(out)?;

        let kit = self.root().join("apps/docs/.svelte-kit");
        if kit.exists() {
            fs::remove_dir_all(&kit).wrap_err("could not clear Svelte build state")?;
        }
        let status = Command::new("pnpm")
            .args(["--filter", "@nucleus/docs", "build"])
            .current_dir(self.root())
            .env("DOCS_OUT_DIR", &out)
            .status()
            .wrap_err("could not build documentation site")?;
        if !status.success() {
            bail!("build documentation site failed with {status}");
        }
        fs::create_dir_all(out.join("generated"))
            .wrap_err("could not create generated documentation directory")?;
        for (source, name) in metadata {
            fs::copy(source, out.join("generated").join(name))
                .wrap_err_with(|| format!("could not publish {name}"))?;
        }
        fs::copy(loc, out.join("generated/loc.json")).wrap_err("could not publish line counts")?;
        copy_dir(&rustdoc, &out.join("api"))
    }

    pub(crate) fn artifact_component(&self, out: &Path) -> Result<()> {
        let out = absolute(out)?;
        let target = artifact_temp(&out, "component-target")?;
        let bindings = self.root().join("crates/nucleus/src/bindings.rs");
        let before = fs::read(&bindings).wrap_err("could not read committed component bindings")?;
        self.run_with_env(
            "build nucleus component",
            "cargo",
            ["component", "build", "--locked", "-p", "covalence-nucleus"],
            &[("CARGO_TARGET_DIR", target.as_os_str())],
        )?;
        let after =
            fs::read(&bindings).wrap_err("could not read regenerated component bindings")?;
        if before != after {
            fs::write(&bindings, before).wrap_err("could not restore stale component bindings")?;
            bail!("component bindings are stale; run `cargo component bindings` in crates/nucleus");
        }
        fs::copy(
            target.join("wasm32-wasip1/debug/covalence_nucleus.wasm"),
            &out,
        )
        .wrap_err("could not copy nucleus component")?;
        Ok(())
    }

    /// Transpile the component into JavaScript plus its core modules.
    ///
    /// This is the component-model route to JavaScript: the interface comes
    /// from WIT, so it does not pull in `wasm-bindgen` and is not restricted to
    /// `wasm32-unknown-unknown`. It runs alongside, not instead of, the
    /// `wasm-bindgen` package that `artifact_wasm` builds.
    ///
    /// jco is a pnpm dependency of `@nucleus/nucleus` rather than a tool in the
    /// Nix shell, so it is reached through pnpm rather than as a binary on
    /// PATH.
    pub(crate) fn artifact_component_js(&self, component: &Path, out: &Path) -> Result<()> {
        let component = absolute(component)?;
        let out = absolute(out)?;
        self.run(
            "transpile nucleus component",
            "pnpm",
            [
                "--filter",
                "@nucleus/nucleus",
                "exec",
                "jco",
                "transpile",
                as_utf8(&component, "component")?,
                "--out-dir",
                as_utf8(&out, "transpiled component output")?,
                "--name",
                "nucleus",
            ],
        )
    }

    pub(crate) fn artifact_cli_component(&self, out: &Path) -> Result<()> {
        let out = absolute(out)?;
        let target = artifact_temp(&out, "cli-component-target")?;
        self.run(
            "build nucleus CLI component",
            "cargo",
            [
                "--locked",
                "build",
                "--target-dir",
                as_utf8(&target, "component target")?,
                "-p",
                "covalence-bin-nucleus",
                "--target",
                "wasm32-wasip2",
            ],
        )?;
        fs::copy(target.join("wasm32-wasip2/debug/nucleus.wasm"), &out)
            .wrap_err("could not copy nucleus CLI component")?;
        Ok(())
    }
}

/// What cargo calls the `cdylib`, and what it has to be called for an
/// interpreter to find it as `covalence._covalence`.
const fn extension_names() -> (&'static str, &'static str) {
    if cfg!(target_os = "windows") {
        ("covalence_ffi_python.dll", "_covalence.pyd")
    } else if cfg!(target_os = "macos") {
        // macOS builds a `.dylib`, which CPython will not consider; the
        // extension has to be renamed, not just moved.
        ("libcovalence_ffi_python.dylib", "_covalence.abi3.so")
    } else {
        ("libcovalence_ffi_python.so", "_covalence.abi3.so")
    }
}

fn artifact_temp(out: &Path, name: &str) -> Result<PathBuf> {
    env::var_os("BUCK_SCRATCH_PATH").map_or_else(
        || Ok(out.parent().unwrap_or_else(|| Path::new(".")).join(name)),
        |scratch| absolute(&PathBuf::from(scratch).join(name)),
    )
}

fn absolute(path: &Path) -> Result<PathBuf> {
    if path.is_absolute() {
        Ok(path.to_owned())
    } else {
        Ok(env::current_dir()
            .wrap_err("could not read the current directory")?
            .join(path))
    }
}

fn as_utf8<'a>(path: &'a Path, description: &str) -> Result<&'a str> {
    path.to_str()
        .ok_or_else(|| color_eyre::eyre::eyre!("{description} path is not UTF-8"))
}
