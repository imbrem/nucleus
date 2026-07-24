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
    cargo, loc,
    runner::{Runner, copy_dir},
};

impl Runner {
    pub(crate) fn artifact_cargo_graph(&self, out: &Path) -> Result<()> {
        cargo::write_graph_to(self.root(), &absolute(out)?)
    }

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
            "compile nucleus for Wasm",
            "cargo",
            [
                "--locked",
                "build",
                "--target-dir",
                as_utf8(&target, "temporary target")?,
                "-p",
                "covalence-nucleus",
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
                    &target.join("wasm32-unknown-unknown/debug/covalence_nucleus.wasm"),
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
        fs::create_dir_all(staged.join("src"))
            .wrap_err("could not create staged TypeScript source directory")?;
        fs::copy(
            self.root().join("packages/nucleus/src/index.ts"),
            staged.join("src/index.ts"),
        )
        .wrap_err("could not stage TypeScript wrapper")?;
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
                as_utf8(&staged.join("src/index.ts"), "TypeScript source")?,
                "--declaration",
                "--module",
                "NodeNext",
                "--moduleResolution",
                "NodeNext",
                "--outDir",
                as_utf8(&dist, "TypeScript output")?,
                "--strict",
                "--target",
                "ES2022",
            ],
        )?;
        copy_dir(&generated, &out.join("generated"))
    }

    pub(crate) fn artifact_docs(
        &self,
        graph: &Path,
        loc: &Path,
        rustdoc: &Path,
        out: &Path,
    ) -> Result<()> {
        let graph = absolute(graph)?;
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
        fs::copy(graph, out.join("generated/cargo-graph.json"))
            .wrap_err("could not publish Cargo dependency graph")?;
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
