//! Internal implementations of Buck actions.
//!
//! The checked-in `BUCK` graph owns dependencies, invalidation, and outputs.
//! These functions only perform individual actions requested by that graph.
//! They are not a stable developer-facing API; use the public `glu build`,
//! `glu test`, and `glu docs` commands instead.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
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
        // The upstream SQLite shell, as its own module. It targets WASI
        // because it needs real stdio, which `wasm32-unknown-unknown` does not
        // have.
        self.run(
            "compile the SQLite shell for WASI",
            "cargo",
            [
                "--locked",
                "build",
                "--target-dir",
                as_utf8(&target, "temporary target")?,
                "--profile",
                "wasm-release",
                "-p",
                "covalence-bin-cas-shell",
                "--target",
                "wasm32-wasip1",
            ],
        )?;
        fs::copy(
            target.join("wasm32-wasip1/wasm-release/covalence-cas-shell.wasm"),
            generated.join("shell.wasm"),
        )
        .wrap_err("could not stage the shell Wasm")?;

        // Stage the package as a package, so its own `tsconfig.json` is what
        // compiles it, and copy the whole `src` directory rather than naming
        // files. Both are the same point: this build and `pnpm build` must not
        // be able to disagree about the same source.
        let package = self.root().join("packages/nucleus");
        copy_dir(&package.join("src"), &staged.join("src"))?;
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
