//! End-to-end proof execution with `SQLite` as the injected async CAS.

use std::path::PathBuf;
use std::sync::Arc;

use covalence_data_cas::CasShared;
use covalence_data_cas_sqlite::SqliteCas;
use covalence_lib_hash::O256;

fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|data| data.parent())
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm")
}

#[test]
#[ignore = "requires `pnpm --filter @nucleus/nucleus build:proof-demo`"]
fn an_async_proof_fetches_its_input_from_sqlite() {
    let path = demo_component();
    let component = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("{} could not be read: {error}", path.display()));
    let cas = SqliteCas::open_in_memory().expect("open SQLite CAS");
    cas.insert("nucleus proof demo".into())
        .expect("insert proof input");

    let kernel = futures::executor::block_on(covalence_nucleus::load_proof_with_cas_async(
        &component,
        O256::from_array([0; 32]),
        Arc::new(cas),
    ))
    .expect("run proof with SQLite CAS");

    assert!(kernel.axioms().any(|name| name == "ax.sub"));
    assert!(!kernel.is_empty());
}
