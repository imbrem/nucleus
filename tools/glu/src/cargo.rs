use std::{collections::BTreeSet, path::Path, process::Command};

use cargo_metadata::{Metadata, MetadataCommand, Package};
use color_eyre::eyre::{Result, WrapErr, bail};

const LICENSE: &str = "CC0-1.0";
const VERSION: &str = "0.0.0";
const RUST_VERSION: &str = "1.97";

#[derive(Debug)]
pub(crate) struct Summary {
    pub(crate) workspace_packages: usize,
    pub(crate) external_packages: usize,
    pub(crate) edges: usize,
}

pub(crate) fn check(root: &Path) -> Result<Summary> {
    let metadata = load(root)?;
    let violations = violations(&metadata);
    if !violations.is_empty() {
        bail!(
            "Cargo dependency policy failed:\n{}",
            violations
                .iter()
                .map(|violation| format!("  - {violation}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }

    Ok(summary(&metadata))
}

pub(crate) fn load(root: &Path) -> Result<Metadata> {
    load_manifest(root, &root.join("Cargo.toml"))
}

pub(crate) fn load_manifest(root: &Path, manifest: &Path) -> Result<Metadata> {
    let host = Command::new("rustc")
        .args(["--print", "host-tuple"])
        .current_dir(root)
        .output()
        .wrap_err("could not inspect the Rust host target")?;
    if !host.status.success() {
        bail!("rustc --print host-tuple failed with {}", host.status);
    }
    let host = String::from_utf8(host.stdout)
        .wrap_err("rustc --print host-tuple returned non-UTF-8 output")?;
    let host = host.trim();
    if host.is_empty() {
        bail!("rustc --print host-tuple returned an empty host target");
    }
    let mut command = MetadataCommand::new();
    command
        .manifest_path(manifest)
        .current_dir(root)
        .other_options(vec![format!("--filter-platform={host}")]);
    command
        .exec()
        .wrap_err_with(|| format!("could not read Cargo metadata for {}", manifest.display()))
}

fn violations(metadata: &Metadata) -> Vec<String> {
    let workspace: BTreeSet<_> = metadata.workspace_members.iter().collect();
    let mut violations = Vec::new();

    for package in metadata
        .packages
        .iter()
        .filter(|package| workspace.contains(&package.id))
    {
        check_package(package, &mut violations);
    }

    for package in &metadata.packages {
        if let Some(source) = &package.source
            && !source.is_crates_io()
        {
            violations.push(format!(
                "{} {} uses unsupported source {source}; use crates.io or a workspace path",
                package.name, package.version,
            ));
        }
    }
    violations
}

fn check_package(package: &Package, violations: &mut Vec<String>) {
    if package.license.as_deref() != Some(LICENSE) {
        violations.push(format!(
            "{} must use license {LICENSE}, found {}",
            package.name,
            package.license.as_deref().unwrap_or("none")
        ));
    }
    if package.version.to_string() != VERSION {
        violations.push(format!(
            "{} must use version {VERSION}, found {}",
            package.name, package.version
        ));
    }
    if package.description.as_deref().is_none_or(str::is_empty) {
        violations.push(format!("{} must declare a description", package.name));
    }
    if package
        .publish
        .as_ref()
        .is_none_or(|registries| !registries.is_empty())
    {
        violations.push(format!("{} must set publish = false", package.name));
    }
    if package.edition.to_string() != "2024" {
        violations.push(format!(
            "{} must use edition 2024, found {}",
            package.name, package.edition
        ));
    }
    if package
        .rust_version
        .as_ref()
        .is_none_or(|version| version.major != 1 || version.minor != 97 || version.patch != 0)
    {
        violations.push(format!(
            "{} must declare rust-version {RUST_VERSION}",
            package.name
        ));
    }
}

fn summary(metadata: &Metadata) -> Summary {
    let workspace: BTreeSet<_> = metadata.workspace_members.iter().collect();
    Summary {
        workspace_packages: workspace.len(),
        external_packages: metadata
            .packages
            .iter()
            .filter(|package| !workspace.contains(&package.id))
            .count(),
        edges: metadata.resolve.as_ref().map_or(0, |resolve| {
            resolve.nodes.iter().map(|node| node.deps.len()).sum()
        }),
    }
}
