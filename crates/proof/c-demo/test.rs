//! End-to-end: the standard asynchronous proof ABI is implementable in C.
//!
//! Ignored by default because it consumes a generated build artifact: run
//! `pnpm --filter @nucleus/nucleus build:proof-c-demo` first, then
//! `cargo test -p covalence-proof-c-demo-test --test proof_c -- --ignored`.

#[cfg(not(feature = "buck-test-fixtures"))]
use std::path::PathBuf;

#[cfg(not(feature = "buck-test-fixtures"))]
fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|proof| proof.parent())
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-wasip1/covalence_proof_c_demo.component.wasm")
}

#[cfg(feature = "buck-test-fixtures")]
const DEMO_COMPONENT: &[u8] = include_bytes!("fixtures/covalence-proof-c-demo.component.wasm");

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

    let mut proof = covalence_nucleus::Strategy::from_bytes(component.as_ref())
        .expect("the C proof should instantiate");
    let zero = covalence_nucleus::core::cas::O256::from_array([0; 32]);
    assert!(
        proof
            .apply_tactic(
                99,
                Vec::new(),
                Some(covalence_nucleus::core::hol::Kernel::new()),
            )
            .is_err(),
        "rejecting an unknown tactic must clean up its supplied kernel"
    );
    let kernels = [
        proof
            .apply_tactic(
                0,
                Vec::new(),
                Some(covalence_nucleus::core::hol::Kernel::new()),
            )
            .expect("indexed tactic with supplied kernel"),
        proof
            .apply_tactic_name("default".to_owned(), None)
            .expect("named tactic with fresh kernel"),
        proof
            .apply_tactic(0, zero.as_ref().to_vec(), None)
            .expect("addressed tactic with fresh kernel"),
    ];

    for kernel in kernels {
        assert!(
            kernel.is_empty(),
            "the micro-demo deliberately returns an empty checked kernel"
        );
    }
}
