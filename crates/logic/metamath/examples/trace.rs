//! Report what a theorem rests on, over a real database.
//!
//! ```sh
//! cargo run --release -p covalence-logic-metamath --example trace -- set.mm ac6 id
//! ```
//!
//! With no labels, prints a census of the database's `$a` by
//! [`AxiomRole`](covalence_logic_metamath::trace::AxiomRole) and the mean and
//! maximum axiom-closure size over its theorems, building the whole-database
//! [`AxiomIndex`](covalence_logic_metamath::trace::AxiomIndex) once.

use std::path::Path;

use covalence_logic_metamath::trace::{AxiomIndex, AxiomRole, Conventions, classify};
use covalence_logic_metamath::{FileResolver, parse_with_resolver};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .ok_or("usage: trace <database.mm> [label ...]")?;
    let labels: Vec<String> = args.collect();

    let file = Path::new(&path);
    let root = file.parent().unwrap_or(Path::new("."));
    let name = file
        .file_name()
        .ok_or("database path names no file")?
        .to_string_lossy()
        .into_owned();

    let database = parse_with_resolver(&name, &FileResolver::new(root))?;
    let conventions = Conventions::default();
    let index = AxiomIndex::build(&database)?;

    if labels.is_empty() {
        census(&database, &index, &conventions);
        return Ok(());
    }

    for label in &labels {
        let Some(used) = index.axioms_where(&database, label, &conventions, |role| {
            role != AxiomRole::Syntax
        }) else {
            println!("{label}: not an assertion of {name}");
            continue;
        };
        let used: Vec<_> = used.collect();
        println!("{label} rests on {} logical $a:", used.len());
        for (axiom, role) in used {
            println!("  {axiom:<16} {role}");
        }
    }
    Ok(())
}

fn census(
    database: &covalence_logic_metamath::Database,
    index: &AxiomIndex<'_>,
    conventions: &Conventions,
) {
    let mut roles = [0_usize; 4];
    for label in index.axiom_labels() {
        match classify(database, label, conventions) {
            Some(AxiomRole::Syntax) => roles[0] += 1,
            Some(AxiomRole::Axiom) => roles[1] += 1,
            Some(AxiomRole::Definition) => roles[2] += 1,
            Some(AxiomRole::Unclassified) => roles[3] += 1,
            None => {}
        }
    }
    println!(
        "$a: {} total — {} syntax, {} axiom, {} definition, {} unclassified",
        index.axiom_labels().len(),
        roles[0],
        roles[1],
        roles[2],
        roles[3]
    );

    let (mut theorems, mut total, mut max) = (0_usize, 0_usize, 0_usize);
    let (mut logical_total, mut logical_max) = (0_usize, 0_usize);
    for assertion in database.assertions() {
        if assertion.proof.is_none() {
            continue;
        }
        let Some(used) = index.axioms(&assertion.label) else {
            continue;
        };
        let mut count = 0;
        let mut logical = 0;
        for axiom in used {
            count += 1;
            if classify(database, axiom, conventions) != Some(AxiomRole::Syntax) {
                logical += 1;
            }
        }
        theorems += 1;
        total += count;
        logical_total += logical;
        max = max.max(count);
        logical_max = logical_max.max(logical);
    }
    if theorems > 0 {
        println!("theorems: {theorems}");
        println!(
            "  all $a in closure:     mean {}, max {max}",
            mean(total, theorems)
        );
        println!(
            "  logical $a in closure: mean {}, max {logical_max}",
            mean(logical_total, theorems)
        );
    }
}

/// `sum / count` to one decimal place, half-up, in integer arithmetic — the
/// counts run to the tens of millions and a `f64` cast is a lint away.
fn mean(sum: usize, count: usize) -> String {
    let tenths = (sum * 10 + count / 2) / count;
    format!("{}.{}", tenths / 10, tenths % 10)
}
