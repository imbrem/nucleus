use std::path::{Path, PathBuf};

use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy, Value};
use covalence_data_spectec::{
    ArtifactError, AstError, AstSummary, BundleManifest, Limits, ManifestError, SPECTEC_VERSION,
    WASM_3_RELEASE, WASM_3_REVISION, WASM_3_SOURCES, WASM_UPSTREAM, canonical_ast, parse_ast,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("vendor/wasm-3.0")
}

fn read(root: &Path, path: &str) -> Vec<u8> {
    std::fs::read(root.join(path)).unwrap_or_else(|error| {
        panic!("could not read pinned artifact {path:?}: {error}");
    })
}

#[test]
fn official_bundle_is_complete_canonical_and_offline_verifiable() {
    let root = root();
    let encoded = read(&root, "manifest.drisl");
    let manifest = BundleManifest::decode(&encoded).unwrap();
    assert_eq!(manifest.encode().unwrap(), encoded);
    assert_eq!(manifest.upstream, WASM_UPSTREAM);
    assert_eq!(manifest.revision, WASM_3_REVISION);
    assert_eq!(manifest.release, WASM_3_RELEASE);
    assert_eq!(manifest.generator_version, SPECTEC_VERSION);
    assert_eq!(
        manifest
            .sources
            .iter()
            .map(|source| source.path.strip_prefix("source/").unwrap())
            .collect::<Vec<_>>(),
        WASM_3_SOURCES
    );

    for artifact in manifest
        .sources
        .iter()
        .chain(std::iter::once(&manifest.ast.artifact))
        .chain(&manifest.licenses)
    {
        artifact.verify(&read(&root, &artifact.path)).unwrap();
        assert_eq!(artifact.cid.codec(), CidCodec::Raw);
        assert_eq!(artifact.cid.hash(), CidHash::Sha256);
    }

    let actual_sources = std::fs::read_dir(root.join("source"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        actual_sources,
        WASM_3_SOURCES
            .iter()
            .map(|name| (*name).to_owned())
            .collect()
    );

    let ast = read(&root, &manifest.ast.artifact.path);
    let parsed = parse_ast(&ast, Limits::default()).unwrap();
    assert_eq!(parsed.summary, manifest.ast.summary);
    let canonical = canonical_ast(&ast, Limits::default()).unwrap();
    let canonical_parsed = parse_ast(canonical.as_bytes(), Limits::default()).unwrap();
    assert_eq!(canonical_parsed.document.erase(), parsed.document.erase());
    assert_eq!(
        AstSummary {
            bytes: parsed.summary.bytes,
            ..canonical_parsed.summary
        },
        parsed.summary
    );

    let debug = drisl::json::decode(Policy::ATPROTO, &read(&root, "manifest.json")).unwrap();
    assert_eq!(debug, manifest.to_value().unwrap());
    let address = drisl::address(CidCodec::Drisl, CidHash::Sha256, &encoded);
    assert_eq!(
        drisl::json::decode(Policy::ATPROTO, &read(&root, "manifest.cid.json")).unwrap(),
        Value::Link(address)
    );
}

#[test]
fn artifact_mismatch_is_typed() {
    let artifact = covalence_data_spectec::Artifact::from_bytes("source", b"abc");
    assert!(matches!(
        artifact.verify(b"ab"),
        Err(ArtifactError::Length { .. })
    ));
    assert!(matches!(
        artifact.verify(b"abd"),
        Err(ArtifactError::Address { .. })
    ));
    let wrong_link = covalence_data_spectec::Artifact {
        cid: drisl::address(CidCodec::Drisl, CidHash::Sha256, b"abc"),
        ..artifact
    };
    assert!(matches!(
        wrong_link.verify(b"abc"),
        Err(ArtifactError::Link { .. })
    ));
}

#[test]
fn manifest_rejects_unsafe_artifact_metadata() {
    let root = root();
    let mut manifest = BundleManifest::decode(&read(&root, "manifest.drisl")).unwrap();
    manifest.sources[0].path = "../outside".to_owned();
    assert!(matches!(
        manifest.encode(),
        Err(ManifestError::ArtifactPath { .. })
    ));

    manifest.sources[0].path = manifest.sources[1].path.clone();
    assert!(matches!(
        manifest.encode(),
        Err(ManifestError::DuplicatePath { .. })
    ));

    manifest.sources[0].path = "source/first.spectec".to_owned();
    manifest.sources[0].cid = drisl::address(CidCodec::Drisl, CidHash::Sha256, b"source");
    assert!(matches!(manifest.encode(), Err(ManifestError::Kind { .. })));
}

#[test]
fn parser_limits_and_malformed_inputs_fail_before_ast_authority() {
    let exact = |bytes, events, depth, roots| Limits {
        bytes,
        events,
        depth,
        roots,
    };
    assert!(matches!(
        parse_ast(b"(x)", exact(2, 10, 10, 10)),
        Err(AstError::Bytes { .. })
    ));
    assert!(matches!(
        parse_ast(b"(x)", exact(10, 2, 10, 10)),
        Err(AstError::Events { .. })
    ));
    assert!(matches!(
        parse_ast(b"((x))", exact(10, 10, 1, 10)),
        Err(AstError::Depth { .. })
    ));
    assert!(matches!(
        parse_ast(b"() ()", exact(10, 10, 10, 1)),
        Err(AstError::Roots { .. })
    ));
    assert!(matches!(
        parse_ast(b"atom", Limits::default()),
        Err(AstError::TopLevelAtom { .. })
    ));
    assert!(matches!(
        parse_ast(b"(", Limits::default()),
        Err(AstError::Parse { .. })
    ));
    assert!(matches!(
        parse_ast(&[0xff], Limits::default()),
        Err(AstError::Utf8 { .. })
    ));
}
