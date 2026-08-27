//! End-to-end: a proof component uses the subtype axiom through the WIT
//! surface, and the kernel it returns records that it did.
//!
//! Ignored by default because it consumes a build artifact rather than a
//! source fixture: run `pnpm --filter @nucleus/nucleus build:proof-demo` first,
//! then `cargo test -p covalence-nucleus --test proof_subtype -- --ignored`.

use std::path::PathBuf;

fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm")
}

fn natural_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-unknown-unknown/debug/covalence_proof_naturals.component.wasm")
}

#[test]
#[ignore = "requires `pnpm --filter @nucleus/nucleus build:proof-demo`"]
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

#[test]
#[ignore = "requires `pnpm --filter @nucleus/nucleus build:proof-naturals`"]
fn the_natural_component_runs_through_the_standard_async_loader() {
    let path = natural_component();
    let component = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("{} could not be read: {error}", path.display()));

    let kernel = covalence_nucleus::load_standard_proof(&component)
        .expect("the natural proof sketch should run to completion");

    assert_eq!(
        kernel.axioms().collect::<Vec<_>>(),
        ["ax.inf", "ax.sub"],
        "the returned arena must record both capabilities used by the construction"
    );
    assert!(
        !kernel.is_empty(),
        "the component built rows, so the arena is not empty"
    );
}
