//! End-to-end: the standard asynchronous proof ABI is implementable in C.
//!
//! Ignored by default because it consumes a generated build artifact: run
//! `pnpm --filter @nucleus/nucleus build:proof-c-demo` first, then
//! `cargo test -p covalence-nucleus --test proof_c -- --ignored`.

#[cfg(not(feature = "buck-test-fixtures"))]
use std::path::PathBuf;

#[cfg(not(feature = "buck-test-fixtures"))]
fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-wasip1/covalence_proof_c_demo.component.wasm")
}

#[cfg(feature = "buck-test-fixtures")]
const DEMO_COMPONENT: &[u8] = include_bytes!("../fixtures/covalence-proof-c-demo.component.wasm");

#[test]
#[cfg_attr(
    not(feature = "buck-test-fixtures"),
    ignore = "requires `pnpm --filter @nucleus/nucleus build:proof-c-demo`"
)]
fn c_can_implement_the_async_proof_world() {
    #[cfg(feature = "buck-test-fixtures")]
    let component = DEMO_COMPONENT;
    #[cfg(not(feature = "buck-test-fixtures"))]
    let component = {
        let path = demo_component();
        std::fs::read(&path)
            .unwrap_or_else(|error| panic!("{} could not be read: {error}", path.display()))
    };

    let kernel = covalence_nucleus::load_standard_proof(component.as_ref())
        .expect("the C proof should run to completion");

    assert!(
        kernel.is_empty(),
        "the micro-demo deliberately returns an empty checked kernel"
    );
}
