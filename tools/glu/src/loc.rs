use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
    path::Path,
    process::{Command, Output},
};

use color_eyre::eyre::{Result, WrapErr, bail};
use serde::{Deserialize, Serialize};

use crate::cargo;

const INTEGRATION: &[&str] = &[
    "crates/nucleus/core",
    // Signing has not yet moved into `nucleus/core`; count its current
    // implementation as integration until that boundary cleanup lands.
    "crates/nucleus/src/snapshot.rs",
    "crates/nucleus/src/snapshot/signing.rs",
];

const TRANSITIONAL_GLUE: &[&str] = &["crates/lib/crypto"];

#[derive(Debug, PartialEq, Eq, Serialize)]
pub(crate) struct Report {
    total: usize,
    crates: usize,
    integration: usize,
    logic: usize,
    data: usize,
    glue: usize,
    tcb: usize,
}

#[derive(Deserialize)]
struct Language {
    #[serde(rename = "Code")]
    code: usize,
}

pub(crate) fn count(root: &Path, verbose: bool) -> Result<Report> {
    let dependencies = core_workspace_dependencies(root)?;
    let logic = dependency_paths(&dependencies, "crates/logic/");
    let data = dependency_paths(&dependencies, "crates/data/");
    let mut glue = dependency_paths(&dependencies, "crates/lib/");
    glue.extend(TRANSITIONAL_GLUE.iter().map(|path| (*path).to_owned()));
    glue.sort();
    glue.dedup();

    let integration = count_paths(root, INTEGRATION, verbose)?;
    let logic = count_owned_paths(root, &logic, verbose)?;
    let data = count_owned_paths(root, &data, verbose)?;
    let glue = count_owned_paths(root, &glue, verbose)?;
    let tcb = integration + logic + data;
    let report = Report {
        total: count_paths(root, &["."], verbose)?,
        crates: count_paths(root, &["crates"], verbose)?,
        integration,
        logic,
        data,
        glue,
        tcb,
    };
    if !(report.total > report.crates && report.crates > report.tcb) {
        bail!(
            "LoC sets must satisfy total > crates > TCB, found {} > {} > {}",
            report.total,
            report.crates,
            report.tcb
        );
    }
    Ok(report)
}

fn core_workspace_dependencies(root: &Path) -> Result<BTreeSet<String>> {
    let metadata = cargo::load(root)?;
    let resolve = metadata
        .resolve
        .as_ref()
        .ok_or_else(|| color_eyre::eyre::eyre!("Cargo metadata omitted the resolve graph"))?;
    let packages = metadata
        .packages
        .iter()
        .map(|package| (&package.id, package))
        .collect::<BTreeMap<_, _>>();
    let nodes = resolve
        .nodes
        .iter()
        .map(|node| (&node.id, node))
        .collect::<BTreeMap<_, _>>();
    let root_id = metadata
        .packages
        .iter()
        .find(|package| package.name == "covalence-nucleus-core")
        .map(|package| &package.id)
        .ok_or_else(|| color_eyre::eyre::eyre!("workspace has no covalence-nucleus-core"))?;
    let workspace = metadata.workspace_members.iter().collect::<BTreeSet<_>>();
    let mut pending = VecDeque::from([root_id]);
    let mut visited = BTreeSet::new();
    let mut paths = BTreeSet::new();
    while let Some(id) = pending.pop_front() {
        if !visited.insert(id) {
            continue;
        }
        if workspace.contains(id) {
            let package = packages
                .get(id)
                .ok_or_else(|| color_eyre::eyre::eyre!("resolved package {id} is missing"))?;
            let directory = package
                .manifest_path
                .parent()
                .ok_or_else(|| color_eyre::eyre::eyre!("package {id} has no directory"))?;
            let relative = directory
                .strip_prefix(root)
                .map_err(|_| color_eyre::eyre::eyre!("package {id} is outside the workspace"))?;
            paths.insert(relative.as_str().to_owned());
        }
        if let Some(node) = nodes.get(id) {
            pending.extend(node.dependencies.iter());
        }
    }
    Ok(paths)
}

fn dependency_paths(dependencies: &BTreeSet<String>, prefix: &str) -> Vec<String> {
    dependencies
        .iter()
        .filter(|path| path.starts_with(prefix))
        .cloned()
        .collect()
}

fn count_owned_paths(root: &Path, paths: &[String], verbose: bool) -> Result<usize> {
    if paths.is_empty() {
        return Ok(0);
    }
    count_paths(
        root,
        &paths.iter().map(String::as_str).collect::<Vec<_>>(),
        verbose,
    )
}

pub(crate) fn write_to(root: &Path, target: &Path, verbose: bool) -> Result<()> {
    let json =
        serde_json::to_string_pretty(&count(root, verbose)?).wrap_err("could not serialize LoC")?;
    std::fs::write(target, format!("{json}\n"))
        .wrap_err_with(|| format!("could not write {}", target.display()))
}

fn count_paths(root: &Path, paths: &[&str], verbose: bool) -> Result<usize> {
    let mut command = Command::new("scc");
    command
        .args([
            "--format",
            "json",
            "--no-cocomo",
            "--no-complexity",
            "--remap-unknown",
            "genrule:Bazel,system_rust_toolchain:Bazel",
        ])
        .args(paths)
        .current_dir(root);
    if verbose {
        eprintln!("  $ scc {}", paths.join(" "));
    }
    let output = command
        .output()
        .wrap_err("could not run scc; enter the Nix development shell")?;
    parse(&output)
}

fn parse(output: &Output) -> Result<usize> {
    if !output.status.success() {
        bail!(
            "scc failed with {}\n{}{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let languages: Vec<Language> =
        serde_json::from_slice(&output.stdout).wrap_err("scc returned invalid JSON")?;
    Ok(languages.iter().map(|language| language.code).sum())
}

impl fmt::Display for Report {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(formatter, "Lines of code")?;
        writeln!(formatter, "┌────────┬──────────┬────────────────────┐")?;
        writeln!(formatter, "│ scope  │    lines │ description        │")?;
        writeln!(formatter, "├────────┼──────────┼────────────────────┤")?;
        writeln!(
            formatter,
            "│ total  │ {:>8} │ repository         │",
            grouped(self.total)
        )?;
        writeln!(
            formatter,
            "│ crates │ {:>8} │ production crates  │",
            grouped(self.crates)
        )?;
        writeln!(
            formatter,
            "│ TCB    │ {:>8} │ authority headline │",
            grouped(self.tcb)
        )?;
        writeln!(
            formatter,
            "│  integ │ {:>8} │ integration        │",
            grouped(self.integration)
        )?;
        writeln!(
            formatter,
            "│  logic │ {:>8} │ core logic deps    │",
            grouped(self.logic)
        )?;
        writeln!(
            formatter,
            "│  data  │ {:>8} │ core data deps     │",
            grouped(self.data)
        )?;
        writeln!(
            formatter,
            "│ glue   │ {:>8} │ excluded support   │",
            grouped(self.glue)
        )?;
        write!(formatter, "└────────┴──────────┴────────────────────┘")
    }
}

impl Report {
    pub(crate) fn headline(&self) -> String {
        format!(
            "Nucleus status\n  TCB         {:>8} lines\n  production  {:>8} lines\n  repository  {:>8} lines",
            grouped(self.tcb),
            grouped(self.crates),
            grouped(self.total),
        )
    }
}

fn grouped(value: usize) -> String {
    let digits = value.to_string();
    let mut output = String::with_capacity(digits.len() + digits.len() / 3);
    for (index, digit) in digits.chars().enumerate() {
        if index != 0 && (digits.len() - index).is_multiple_of(3) {
            output.push(',');
        }
        output.push(digit);
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_nested_report() {
        assert_eq!(
            Report {
                total: 12_345,
                crates: 234,
                integration: 18,
                logic: 200,
                data: 0,
                glue: 55,
                tcb: 218,
            }
            .to_string(),
            "Lines of code\n\
             ┌────────┬──────────┬────────────────────┐\n\
             │ scope  │    lines │ description        │\n\
             ├────────┼──────────┼────────────────────┤\n\
             │ total  │   12,345 │ repository         │\n\
             │ crates │      234 │ production crates  │\n\
             │ TCB    │      218 │ authority headline │\n\
             │  integ │       18 │ integration        │\n\
             │  logic │      200 │ core logic deps    │\n\
             │  data  │        0 │ core data deps     │\n\
             │ glue   │       55 │ excluded support   │\n\
             └────────┴──────────┴────────────────────┘"
        );
    }

    #[test]
    fn groups_decimal_digits() {
        assert_eq!(grouped(0), "0");
        assert_eq!(grouped(999), "999");
        assert_eq!(grouped(1_000), "1,000");
        assert_eq!(grouped(1_234_567), "1,234,567");
    }
}
