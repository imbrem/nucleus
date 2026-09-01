//! Regenerates the pinned Wasm 3.0 bundle manifest from already generated IL.
//!
//! Build the pinned upstream `SpecTec` executable and produce
//! `vendor/wasm-3.0/wasm-3.0.ast.sexp` before running this example. Normal
//! builds never invoke `SpecTec` or access the network.

use std::path::{Path, PathBuf};

use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy, Value};
use covalence_data_spectec::{
    Artifact, AstArtifact, BundleManifest, Limits, SPECTEC_VERSION, WASM_3_RELEASE,
    WASM_3_REVISION, WASM_3_SOURCES, WASM_UPSTREAM, canonical_ast, parse_ast,
};

fn read(root: &Path, path: &str) -> Vec<u8> {
    std::fs::read(root.join(path)).unwrap_or_else(|error| {
        panic!("could not read pinned artifact {path:?}: {error}");
    })
}

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("vendor/wasm-3.0");
    let sources = WASM_3_SOURCES
        .iter()
        .map(|name| {
            let path = format!("source/{name}");
            Artifact::from_bytes(&path, &read(&root, &path))
        })
        .collect::<Vec<_>>();
    let ast_path = "wasm-3.0.ast.sexp";
    let ast_bytes = read(&root, ast_path);
    let parsed = parse_ast(&ast_bytes, Limits::default()).expect("generated AST must parse");
    let canonical_ast_bytes = canonical_ast(&ast_bytes, Limits::default())
        .expect("generated AST must print")
        .into_bytes();
    let canonical_parsed =
        parse_ast(&canonical_ast_bytes, Limits::default()).expect("canonical AST must parse");
    assert_eq!(canonical_parsed.document.erase(), parsed.document.erase());

    let licenses = ["license/UPSTREAM-LICENSE", "license/W3C-LICENSE"]
        .into_iter()
        .map(|path| Artifact::from_bytes(path, &read(&root, path)))
        .collect();
    let mut arguments = WASM_3_SOURCES
        .iter()
        .map(|name| format!("specification/wasm-3.0/{name}"))
        .collect::<Vec<_>>();
    arguments.extend([
        "--ast".to_owned(),
        "-o".to_owned(),
        "wasm-3.0.ast.sexp".to_owned(),
    ]);

    let manifest = BundleManifest {
        upstream: WASM_UPSTREAM.to_owned(),
        revision: WASM_3_REVISION.to_owned(),
        release: WASM_3_RELEASE.to_owned(),
        generator_version: SPECTEC_VERSION.to_owned(),
        generator_arguments: arguments,
        sources,
        ast: AstArtifact {
            artifact: Artifact::from_bytes(ast_path, &ast_bytes),
            summary: parsed.summary,
        },
        licenses,
    };

    let canonical = manifest.encode().expect("manifest must encode");
    let debug = drisl::json::encode(&manifest.to_value().expect("manifest must map to DRISL"))
        .expect("manifest debug JSON must encode");
    let address = drisl::address(CidCodec::Drisl, CidHash::Sha256, &canonical);
    let address_json =
        drisl::json::encode(&Value::Link(address)).expect("manifest address JSON must encode");

    std::fs::write(root.join("manifest.drisl"), canonical)
        .expect("could not write canonical manifest");
    std::fs::write(root.join("manifest.json"), with_newline(debug))
        .expect("could not write debug manifest");
    std::fs::write(root.join("manifest.cid.json"), with_newline(address_json))
        .expect("could not write manifest address");

    let reread = std::fs::read(root.join("manifest.drisl")).expect("could not reread manifest");
    assert_eq!(
        BundleManifest::decode(&reread).expect("written manifest must decode"),
        manifest
    );
    assert!(Policy::ATPROTO.accepts(address));
}

fn with_newline(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.push(b'\n');
    bytes
}
