use std::{env, error::Error, fs, path::Path, process::ExitCode};

use covalence_lib_crypto::ed25519::{SigningKey, VerifyingKey};
use covalence_nucleus::{
    AdditionFact, AdditionLayout, Connection, Ed25519Signer, Ed25519Verifier, SignedSnapshot,
};

fn main() -> ExitCode {
    match run(env::args().skip(1)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("nucleus: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(mut arguments: impl Iterator<Item = String>) -> Result<(), Box<dyn Error>> {
    match (arguments.next().as_deref(), arguments.next().as_deref()) {
        (Some("snapshot"), Some("export")) => {
            let envelope = required(&mut arguments, "snapshot envelope path")?;
            let secret_key = required(&mut arguments, "32-byte secret-key path")?;
            no_more(arguments)?;
            export_snapshot(Path::new(&envelope), Path::new(&secret_key))
        }
        (Some("snapshot"), Some("import")) => {
            let envelope = required(&mut arguments, "snapshot envelope path")?;
            let public_key = required(&mut arguments, "32-byte public-key path")?;
            no_more(arguments)?;
            import_snapshot(Path::new(&envelope), Path::new(&public_key))
        }
        _ => Err(
            "usage: nucleus snapshot {export ENVELOPE SECRET_KEY | import ENVELOPE PUBLIC_KEY}"
                .into(),
        ),
    }
}

fn required(
    arguments: &mut impl Iterator<Item = String>,
    description: &str,
) -> Result<String, Box<dyn Error>> {
    arguments
        .next()
        .ok_or_else(|| format!("missing {description}").into())
}

fn no_more(mut arguments: impl Iterator<Item = String>) -> Result<(), Box<dyn Error>> {
    if let Some(argument) = arguments.next() {
        return Err(format!("unexpected argument {argument:?}").into());
    }
    Ok(())
}

fn export_snapshot(envelope_path: &Path, secret_key_path: &Path) -> Result<(), Box<dyn Error>> {
    let secret_key = read_array(secret_key_path)?;
    let signing_key = SigningKey::from_bytes(&secret_key);
    let signing_capability = Ed25519Signer::new(signing_key);
    let key_id = signing_capability.key_id();

    let mut connection = Connection::create_in_memory()?;
    let naturals = connection.create_addition_table("naturals", AdditionLayout::RowId)?;
    let integers = connection.create_addition_table("integers", AdditionLayout::WithoutRowId)?;
    for (table, lhs, rhs) in [
        (&naturals, 1, 1),
        (&naturals, 20, 22),
        (&integers, -20, -22),
        (&integers, i64::MIN, 1),
    ] {
        connection.insert_addition(table, AdditionFact::sum(lhs, rhs)?)?;
    }
    connection
        .cas()
        .store(b"CAS content is deliberately connection-local")?;
    connection.register_signer(key_id, Box::new(signing_capability))?;

    let snapshot = connection.sign_snapshot(key_id)?;
    fs::write(envelope_path, snapshot.encode()?)?;
    println!(
        "exported {} addition tables signed by {key_id}",
        connection.addition_tables()?.len()
    );
    Ok(())
}

fn import_snapshot(envelope_path: &Path, public_key_path: &Path) -> Result<(), Box<dyn Error>> {
    let encoded = fs::read(envelope_path)?;
    let snapshot = SignedSnapshot::decode(&encoded)?;
    let public_key = VerifyingKey::from_bytes(&read_array(public_key_path)?)?;
    let connection =
        Connection::open_signed_snapshot(&snapshot, Box::new(Ed25519Verifier::new(public_key)))?;
    let tables = connection.addition_tables()?;
    println!(
        "accepted snapshot {} signed by {}",
        connection.cas().hash(snapshot.image()),
        snapshot.key()
    );
    for table in &tables {
        let facts = connection.addition_facts(table)?;
        println!(
            "{} {:?}: {} facts",
            table.name(),
            table.layout(),
            facts.len()
        );
    }
    let stored = connection
        .cas()
        .fetch(connection.cas().hash(snapshot.image()))?
        .is_some();
    println!("snapshot image resident in CAS: {stored}");
    Ok(())
}

fn read_array(path: &Path) -> Result<[u8; 32], Box<dyn Error>> {
    let bytes = fs::read(path)?;
    bytes.try_into().map_err(|bytes: Vec<u8>| {
        format!(
            "{} must contain 32 bytes, got {}",
            path.display(),
            bytes.len()
        )
        .into()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_incomplete_commands() {
        assert!(run(["snapshot".into(), "export".into()].into_iter()).is_err());
        assert!(run(["unknown".into()].into_iter()).is_err());
    }
}
