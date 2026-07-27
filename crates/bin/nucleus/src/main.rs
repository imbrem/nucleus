use std::{env, error::Error, fs, path::Path, process::ExitCode};

use covalence_lib_crypto::ed25519::{SigningKey, VerifyingKey};
use covalence_nucleus::{AdditionFact, Connection, Ed25519Signer, Ed25519Verifier, SignedSnapshot};

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
        (None, None) => {
            println!(
                "hello from nucleus: SQLite returned {}",
                covalence_nucleus::smoke()
            );
            Ok(())
        }
        (Some("snapshot"), Some("export")) => {
            let envelope = required(&mut arguments, "snapshot envelope path")?;
            let secret_key = required(&mut arguments, "32-byte secret-key path")?;
            let public_key = required(&mut arguments, "public-key output path")?;
            no_more(arguments)?;
            export_snapshot(
                Path::new(&envelope),
                Path::new(&secret_key),
                Path::new(&public_key),
            )
        }
        (Some("snapshot"), Some("import")) => {
            let envelope = required(&mut arguments, "snapshot envelope path")?;
            let public_key = required(&mut arguments, "32-byte public-key path")?;
            no_more(arguments)?;
            import_snapshot(Path::new(&envelope), Path::new(&public_key))
        }
        _ => Err(
            "usage: nucleus snapshot {export ENVELOPE SECRET_KEY PUBLIC_KEY | import ENVELOPE PUBLIC_KEY}"
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

fn export_snapshot(
    envelope_path: &Path,
    secret_key_path: &Path,
    public_key_path: &Path,
) -> Result<(), Box<dyn Error>> {
    let secret_key = read_array(secret_key_path)?;
    let signing_key = SigningKey::from_bytes(&secret_key);
    let public_key = signing_key.verifying_key().to_bytes();
    let signing_capability = Ed25519Signer::new(signing_key);
    let key_id = signing_capability.key_id();

    let mut connection = Connection::create_in_memory()?;
    {
        let naturals = connection.create_addition("naturals")?;
        let integers = connection.create_addition("integers")?;
        for (addition, lhs, rhs) in [
            (&naturals, 1, 1),
            (&naturals, 20, 22),
            (&integers, -20, -22),
            (&integers, i64::MIN, 1),
        ] {
            addition.insert(AdditionFact::sum(lhs, rhs)?)?;
        }

        let text = connection.create_cas_table("text_cas")?;
        let binary = connection.create_cas_table("binary_cas")?;
        let lengths = connection.create_byte_lengths("byte_lengths")?;
        lengths.record(&text, b"shared")?;
        lengths.record(&text, b"hello, nucleus")?;
        lengths.record(&binary, b"shared")?;
        lengths.record(&binary, &[0, 1, 2, 3])?;
    }
    connection
        .cas()
        .store(b"CAS content is deliberately connection-local")?;
    connection.register_signer(key_id, Box::new(signing_capability))?;

    let snapshot = connection.sign_snapshot(key_id)?;
    fs::write(envelope_path, snapshot.encode()?)?;
    fs::write(public_key_path, public_key)?;
    println!("exported snapshot signed by {key_id}");
    println!("  {} addition tables", connection.additions()?.len());
    println!("  {} persistent CAS tables", connection.cas_tables()?.len());
    println!(
        "  {} byte-length relations",
        connection.byte_length_tables()?.len()
    );
    Ok(())
}

fn import_snapshot(envelope_path: &Path, public_key_path: &Path) -> Result<(), Box<dyn Error>> {
    let encoded = fs::read(envelope_path)?;
    let snapshot = SignedSnapshot::decode(&encoded)?;
    let public_key = VerifyingKey::from_bytes(&read_array(public_key_path)?)?;
    let connection =
        Connection::open_signed_snapshot(&snapshot, Box::new(Ed25519Verifier::new(public_key)))?;
    println!(
        "accepted snapshot {} signed by {}",
        snapshot.snapshot_hash(),
        snapshot.key()
    );
    for addition in connection.additions()? {
        let facts = addition.facts()?;
        println!("{}: {} facts", addition.name(), facts.len());
        for fact in facts {
            println!("  {} = {} + {}", fact.tm, fact.lhs, fact.rhs);
        }
    }
    let cas_tables = connection.cas_tables()?;
    println!("persistent CAS tables: {}", cas_tables.len());
    for cas in &cas_tables {
        println!("  {}", cas.name());
    }
    for relation in connection.byte_length_tables()? {
        let facts = relation.facts()?;
        println!("{}: {} byte-length facts", relation.name(), facts.len());
        for fact in facts {
            println!("  {}/{}: {} bytes", fact.cas_table, fact.hash, fact.length);
        }
    }
    let stored = connection.cas().fetch(snapshot.snapshot_hash())?.is_some();
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
