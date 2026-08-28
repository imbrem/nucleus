use std::{
    fmt,
    path::Path,
    process::{Command, Output},
};

use color_eyre::eyre::{Result, WrapErr, bail};
use serde::{Deserialize, Serialize};

const TCB: &[&str] = &[
    "crates/lib/hash",
    "crates/lib/rand",
    "crates/lib/sqlite",
    "crates/data/basic",
    "crates/proton",
    "crates/neutron",
    // `nucleus` also contains explicitly untrusted frontends. Its core is a
    // separate package so the authority boundary is visible to build tooling.
    "crates/nucleus/core",
];

#[derive(Debug, PartialEq, Eq, Serialize)]
pub(crate) struct Report {
    total: usize,
    crates: usize,
    tcb: usize,
}

#[derive(Deserialize)]
struct Language {
    #[serde(rename = "Code")]
    code: usize,
}

pub(crate) fn count(root: &Path, verbose: bool) -> Result<Report> {
    let report = Report {
        total: count_paths(root, &["."], verbose)?,
        crates: count_paths(root, &["crates"], verbose)?,
        tcb: count_paths(root, TCB, verbose)?,
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
            "│ TCB    │ {:>8} │ trusted core       │",
            grouped(self.tcb)
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
                tcb: 218,
            }
            .to_string(),
            "Lines of code\n\
             ┌────────┬──────────┬────────────────────┐\n\
             │ scope  │    lines │ description        │\n\
             ├────────┼──────────┼────────────────────┤\n\
             │ total  │   12,345 │ repository         │\n\
             │ crates │      234 │ production crates  │\n\
             │ TCB    │      218 │ trusted core       │\n\
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
