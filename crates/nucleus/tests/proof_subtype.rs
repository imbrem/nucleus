//! End-to-end: a proof component uses the subtype axiom through the WIT
//! surface, and the kernel it returns records that it did.
//!
//! Ignored by default because it consumes a build artifact rather than a
//! source fixture: run `pnpm --filter @nucleus/nucleus build:proof-demo` first,
//! then `cargo test -p covalence-nucleus --test proof_subtype -- --ignored`.

use std::{collections::BTreeMap, path::PathBuf, sync::Arc};

use covalence_data_cas::{Bytes, IndexCas};
use covalence_data_vfs::MemoryVfs;
use covalence_lib_hash::O256;

fn demo_component() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|crates| crates.parent())
        .expect("workspace root")
        .to_path_buf();
    root.join("target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm")
}

#[test]
#[ignore = "requires `pnpm --filter @nucleus/nucleus build:proof-demo`"]
fn the_demo_component_takes_on_the_subtype_axiom() {
    let path = demo_component();
    let component = std::fs::read(&path)
        .unwrap_or_else(|error| panic!("{} could not be read: {error}", path.display()));

    let mut proof = covalence_nucleus::ProofInstance::from_bytes(&component)
        .expect("the demo proof should instantiate");
    let kernel = proof
        .prove_addr(
            covalence_lib_hash::O256::from_array([0; 32]),
            covalence_nucleus::core::hol::Kernel::new(),
        )
        .expect("the demo proof should run to completion");
    let repeated = proof
        .prove_name(
            "default".to_owned(),
            covalence_nucleus::core::hol::Kernel::new(),
        )
        .expect("the same proof instance should accept another request");
    let by_bytes = proof
        .prove_bytes(
            Bytes::from_static(b"default"),
            covalence_nucleus::core::hol::Kernel::new(),
        )
        .expect("the proof should accept a shared byte-resource name");
    let by_id = proof
        .prove_ix(0, covalence_nucleus::core::hol::Kernel::new())
        .expect("the proof should accept a compact mutation ID");

    assert!(
        kernel.axioms().any(|name| name == "ax.sub"),
        "the returned arena must record the axiom the component used"
    );
    assert!(
        !kernel.is_empty(),
        "the component built rows, so the arena is not empty"
    );
    assert_eq!(kernel.addr(), repeated.addr());
    assert_eq!(kernel.addr(), by_bytes.addr());
    assert_eq!(kernel.addr(), by_id.addr());

    let resources = MemoryVfs::new(BTreeMap::from([
        (
            "proofs".to_owned(),
            Bytes::from_static(b"(proof demo (wasm proof/demo.wasm))"),
        ),
        (
            "proof/demo.wasm".to_owned(),
            Bytes::copy_from_slice(&component),
        ),
    ]));
    let tree = covalence_nucleus::script::compile_tree("proofs", &resources)
        .expect("compile resource-backed proof");
    let resources: Arc<dyn covalence_data_vfs::ResourceVfs> = Arc::new(resources);
    let outputs = covalence_nucleus::run_script_proofs(&tree, Some(resources), None)
        .expect("run resource-backed proof");
    assert_eq!(outputs[0].name(), "proofs.demo");
    assert!(outputs[0].kernel().len() > tree.module().kernel().len());
    let resource_output = outputs[0].kernel().addr();

    let component_address = O256::from_bytes(&component);
    let mut cas = IndexCas::new();
    cas.insert(Bytes::copy_from_slice(&component));
    let address_source = format!("(proof cached (wasm !{}))", component_address.hex());
    let address_resources = MemoryVfs::new(BTreeMap::from([(
        "addressed".to_owned(),
        Bytes::from(address_source),
    )]));
    let tree = covalence_nucleus::script::compile_tree("addressed", &address_resources)
        .expect("compile address-backed proof");
    let cas: Arc<dyn covalence_data_cas::AsyncCas> = Arc::new(cas);
    let outputs = covalence_nucleus::run_script_proofs(&tree, None, Some(cas))
        .expect("run address-backed proof");
    assert_eq!(outputs[0].kernel().addr(), resource_output);
}
