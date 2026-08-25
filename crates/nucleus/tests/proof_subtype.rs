//! End-to-end: a proof component uses the subtype axiom through the WIT
//! surface, and the kernel it returns records that it did.
//!
//! Ignored by default because it consumes a build artifact rather than a
//! source fixture: run `cargo component build -p covalence-proof-demo` first,
//! then `cargo test -p covalence-nucleus --test proof_subtype -- --ignored`.

use std::path::PathBuf;

fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-wasip1/debug/covalence_proof_demo.wasm")
}

#[test]
#[ignore = "requires `cargo component build -p covalence-proof-demo`"]
fn the_demo_component_takes_on_the_subtype_axiom() {
    let path = demo_component();
    let component = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("{} could not be read: {error}", path.display()));

    let kernel = covalence_nucleus::load_standard_proof(&component)
        .expect("the demo proof should run to completion");

    assert!(
        kernel.axioms().any(|name| name == "ax.sub"),
        "the returned arena must record the axiom the component used"
    );
    assert!(
        !kernel.is_empty(),
        "the component built rows, so the arena is not empty"
    );
}
