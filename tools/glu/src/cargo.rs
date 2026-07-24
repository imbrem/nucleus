use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    process::Command,
};

use cargo_metadata::{Metadata, MetadataCommand, Package};
use color_eyre::eyre::{Result, WrapErr, bail};
use serde::Serialize;

const LICENSE: &str = "CC0-1.0";
const VERSION: &str = "0.0.0";
const RUST_VERSION: &str = "1.97";

#[derive(Debug)]
pub(crate) struct Summary {
    pub(crate) workspace_packages: usize,
    pub(crate) external_packages: usize,
    pub(crate) edges: usize,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Graph {
    generated_by: &'static str,
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
}

#[derive(Serialize)]
struct GraphNode {
    id: String,
    name: String,
    version: String,
    workspace: bool,
    direct: bool,
    category: &'static str,
}

#[derive(Serialize)]
struct GraphEdge {
    source: String,
    target: String,
    kinds: Vec<String>,
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

pub(crate) fn write_graph_to(root: &Path, target: &Path) -> Result<()> {
    let production = load_manifest_all(root, &root.join("Cargo.toml"))?;
    let tools = load_manifest_all(root, &root.join("tools/glu/Cargo.toml"))?;
    let mut combined = graph(&production, false)?;
    let tools = graph(&tools, true)?;
    for node in tools.nodes {
        if let Some(existing) = combined
            .nodes
            .iter_mut()
            .find(|existing| existing.id == node.id)
        {
            existing.direct |= node.direct;
        } else {
            combined.nodes.push(node);
        }
    }
    combined.edges.extend(tools.edges);
    combined.nodes.sort_by(|left, right| {
        right
            .workspace
            .cmp(&left.workspace)
            .then_with(|| left.name.cmp(&right.name))
            .then_with(|| left.version.cmp(&right.version))
    });
    combined.edges.sort_by(|left, right| {
        left.source
            .cmp(&right.source)
            .then_with(|| left.target.cmp(&right.target))
            .then_with(|| left.kinds.cmp(&right.kinds))
    });
    let mut edges: Vec<GraphEdge> = Vec::new();
    for edge in combined.edges {
        if let Some(existing) = edges.last_mut()
            && existing.source == edge.source
            && existing.target == edge.target
        {
            existing.kinds.extend(edge.kinds);
            existing.kinds.sort();
            existing.kinds.dedup();
        } else {
            edges.push(edge);
        }
    }
    combined.edges = edges;
    fs::create_dir_all(target.parent().expect("graph has a parent directory"))
        .wrap_err("could not create generated documentation directory")?;
    let json =
        serde_json::to_string_pretty(&combined).wrap_err("could not serialize Cargo graph")?;
    fs::write(target, format!("{json}\n"))
        .wrap_err_with(|| format!("could not write {}", target.display()))
}

fn load(root: &Path) -> Result<Metadata> {
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

fn load_manifest_all(root: &Path, manifest: &Path) -> Result<Metadata> {
    MetadataCommand::new()
        .manifest_path(manifest)
        .current_dir(root)
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

    let mut versions: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    for package in &metadata.packages {
        versions
            .entry(&package.name)
            .or_default()
            .insert(package.version.to_string());
        if let Some(source) = &package.source
            && !source.is_crates_io()
        {
            violations.push(format!(
                "{} {} uses unsupported source {source}; use crates.io or a workspace path",
                package.name, package.version,
            ));
        }
    }
    for (name, versions) in versions {
        if versions.len() > 1 {
            violations.push(format!(
                "{name} appears at multiple versions: {}",
                versions.into_iter().collect::<Vec<_>>().join(", ")
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

fn graph(metadata: &Metadata, tools: bool) -> Result<Graph> {
    let workspace: BTreeSet<_> = metadata.workspace_members.iter().collect();
    let packages: BTreeMap<&str, &Package> = metadata
        .packages
        .iter()
        .map(|package| (package.id.repr.as_str(), package))
        .collect();
    let resolve = metadata
        .resolve
        .as_ref()
        .ok_or_else(|| color_eyre::eyre::eyre!("Cargo metadata did not include a resolve graph"))?;
    let direct: BTreeSet<_> = resolve
        .nodes
        .iter()
        .filter(|node| workspace.contains(&node.id))
        .flat_map(|node| node.deps.iter().map(|dependency| &dependency.pkg))
        .filter(|package| !workspace.contains(package))
        .collect();

    let mut nodes = metadata
        .packages
        .iter()
        .map(|package| GraphNode {
            id: package.id.repr.clone(),
            name: package.name.to_string(),
            version: package.version.to_string(),
            workspace: workspace.contains(&package.id),
            direct: direct.contains(&package.id),
            category: package_category(metadata, package, tools, &workspace),
        })
        .collect::<Vec<_>>();
    nodes.sort_by(|left, right| {
        right
            .workspace
            .cmp(&left.workspace)
            .then_with(|| left.name.cmp(&right.name))
            .then_with(|| left.version.cmp(&right.version))
    });

    let mut edges = Vec::new();
    for node in &resolve.nodes {
        for dependency in &node.deps {
            let mut kinds = dependency
                .dep_kinds
                .iter()
                .map(|kind| {
                    let target = kind
                        .target
                        .as_ref()
                        .map(|target| format!(" ({target})"))
                        .unwrap_or_default();
                    format!("{}{target}", kind.kind)
                })
                .collect::<Vec<_>>();
            kinds.sort();
            kinds.dedup();
            edges.push(GraphEdge {
                source: node.id.repr.clone(),
                target: dependency.pkg.repr.clone(),
                kinds,
            });
        }
    }
    edges.sort_by(|left, right| {
        package_name(&packages, &left.source)
            .cmp(&package_name(&packages, &right.source))
            .then_with(|| {
                package_name(&packages, &left.target).cmp(&package_name(&packages, &right.target))
            })
            .then_with(|| left.source.cmp(&right.source))
            .then_with(|| left.target.cmp(&right.target))
            .then_with(|| left.kinds.cmp(&right.kinds))
    });

    Ok(Graph {
        generated_by: concat!("glu ", env!("CARGO_PKG_VERSION")),
        nodes,
        edges,
    })
}

fn package_category(
    metadata: &Metadata,
    package: &Package,
    tools: bool,
    workspace: &BTreeSet<&cargo_metadata::PackageId>,
) -> &'static str {
    if !workspace.contains(&package.id) {
        "external"
    } else if tools {
        "tool"
    } else if package
        .manifest_path
        .strip_prefix(&metadata.workspace_root)
        .is_ok_and(|path| path.starts_with("crates/bin"))
    {
        "product"
    } else {
        "tcb"
    }
}

fn package_name(packages: &BTreeMap<&str, &Package>, id: &str) -> String {
    packages
        .get(id)
        .map_or_else(|| id.to_owned(), |package| package.name.to_string())
}
