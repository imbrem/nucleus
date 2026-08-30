//! Minimal JSON/DRISL conversion tool for debugging wire objects.

use std::io::{Read as _, Write as _};

use covalence_data_cbor::drisl::{self, Policy, json};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args().skip(1);
    let Some(command) = arguments.next() else {
        return usage();
    };
    let policy = match arguments.next().as_deref() {
        None => Policy::ATPROTO,
        Some("--nucleus") => Policy::NUCLEUS,
        Some(_) => return usage(),
    };
    if arguments.next().is_some() {
        return usage();
    }

    let mut input = Vec::new();
    std::io::stdin().read_to_end(&mut input)?;
    let output = match command.as_str() {
        "to-cbor" => drisl::encode(policy, &json::decode(policy, &input)?)?,
        "to-json" => json::encode(&drisl::decode(policy, &input)?)?,
        "roundtrip-json" => {
            let value = json::decode(policy, &input)?;
            let block = drisl::encode(policy, &value)?;
            json::encode(&drisl::decode(policy, &block)?)?
        }
        "roundtrip-cbor" => {
            let value = drisl::decode(policy, &input)?;
            let debug = json::encode(&value)?;
            drisl::encode(policy, &json::decode(policy, &debug)?)?
        }
        _ => return usage(),
    };
    std::io::stdout().write_all(&output)?;
    Ok(())
}

fn usage<T>() -> Result<T, Box<dyn std::error::Error>> {
    Err("usage: drisl-json <to-cbor|to-json|roundtrip-json|roundtrip-cbor> [--nucleus]".into())
}
