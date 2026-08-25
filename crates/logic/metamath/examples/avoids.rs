//! Check a database's own `$j usage '<theorem>' avoids '<label>' ...;` claims
//! against [`AxiomIndex`](covalence_logic_metamath::trace::AxiomIndex).
//!
//! ```sh
//! cargo run --release -p covalence-logic-metamath --example avoids -- set.mm
//! ```
//!
//! `set.mm` carries over a thousand of these — assertions by the database's
//! authors that a theorem does *not* rest on a given statement. They are the
//! only large body of independently-written ground truth for this query, so
//! they are the crate's best cross-check on it.
//!
//! Two notes on what this checks that the reference implementation does not.
//! `metamath-knife`'s `--verify-usage` is the only other tool that reads these,
//! and it contains `if !axiom.starts_with(b"ax-") { continue; }` — so every
//! non-`ax-` entry is silently skipped. Nothing here is skipped. And the claim
//! is read as being about the *transitive* closure, which is what the
//! directives mean.
//!
//! The directives are scraped from the source text rather than from the
//! [`Database`](covalence_logic_metamath::Database), because comments are
//! discarded during parsing today. That makes this an example and not a test;
//! comment retention turns it into one. Only the named file is scraped, so
//! directives inside an included file are not seen.

use std::path::Path;

use covalence_logic_metamath::trace::AxiomIndex;
use covalence_logic_metamath::{FileResolver, parse_with_resolver};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args()
        .nth(1)
        .ok_or("usage: avoids <database.mm>")?;
    let file = Path::new(&path);
    let root = file.parent().unwrap_or(Path::new("."));
    let name = file
        .file_name()
        .ok_or("database path names no file")?
        .to_string_lossy()
        .into_owned();

    let source = std::fs::read_to_string(file)?;
    let database = parse_with_resolver(&name, &FileResolver::new(root))?;
    let index = AxiomIndex::build(&database)?;

    let claims = usage_claims(&source);
    let (mut checked, mut violated, mut unknown) = (0_usize, 0_usize, 0_usize);
    for (theorem, avoided) in &claims {
        if index.axioms(theorem).is_none() {
            println!("?  {theorem}: no such assertion");
            unknown += 1;
            continue;
        }
        for label in avoided {
            checked += 1;
            if index.rests_on(theorem, label) {
                println!("!  {theorem} declares it avoids {label}, but reaches it");
                violated += 1;
            }
        }
    }

    println!(
        "\n{} directives over {} theorems: {checked} claims checked, \
         {violated} violated, {unknown} theorems unknown",
        claims.len(),
        claims
            .iter()
            .map(|(t, _)| t.as_str())
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
    );
    if violated == 0 {
        Ok(())
    } else {
        Err(format!("{violated} usage claims are false").into())
    }
}

/// Every `usage '<theorem>' avoids '<label>' ...` directive in `source`.
///
/// Metamath markup lives in `$( $j ... $)` comments as `;`-terminated
/// statements whose arguments are single-quoted. Anything that is not a
/// `usage`/`avoids` statement is skipped.
fn usage_claims(source: &str) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    let mut rest = source;
    while let Some(open) = rest.find("$(") {
        let body = &rest[open + 2..];
        let Some(close) = body.find("$)") else { break };
        let comment = &body[..close];
        rest = &body[close + 2..];

        let trimmed = comment.trim_start();
        let Some(markup) = trimmed.strip_prefix("$j") else {
            continue;
        };
        for statement in markup.split(';') {
            let mut words = statement.split_whitespace();
            if words.next() != Some("usage") {
                continue;
            }
            let quoted: Vec<&str> = statement
                .split('\'')
                .skip(1)
                .step_by(2)
                .map(str::trim)
                .collect();
            let Some((theorem, avoided)) = quoted.split_first() else {
                continue;
            };
            if !statement.split_whitespace().any(|w| w == "avoids") || avoided.is_empty() {
                continue;
            }
            out.push((
                (*theorem).to_owned(),
                avoided.iter().map(|l| (*l).to_owned()).collect(),
            ));
        }
    }
    out
}
