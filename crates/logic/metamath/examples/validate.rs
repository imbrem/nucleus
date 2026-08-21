use std::path::Path;
use std::time::Instant;

use covalence_logic_metamath::{FileResolver, parse_with_resolver, verify_all};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let paths: Vec<_> = std::env::args_os().skip(1).collect();
    if paths.is_empty() {
        return Err("usage: validate DATABASE.mm [DATABASE.mm ...]".into());
    }

    for path in paths {
        let path = Path::new(&path);
        let filename = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("database path has no UTF-8 filename")?;
        let resolver = FileResolver::new(path.parent().unwrap_or_else(|| Path::new(".")));
        let bytes = std::fs::metadata(path)?.len();

        let started = Instant::now();
        let database = parse_with_resolver(filename, &resolver)?;
        let parsed = started.elapsed();
        let statements = database.statements().len();
        let assertions = database.assertions().count();

        let started = Instant::now();
        let theorems = verify_all(&database)?;
        let verified = started.elapsed();

        println!(
            "{}\tbytes={bytes}\tstatements={statements}\tassertions={assertions}\ttheorems={theorems}\tparse_ms={}\tverify_ms={}",
            path.display(),
            parsed.as_millis(),
            verified.as_millis(),
        );
    }
    Ok(())
}
