use std::path::{Path, PathBuf};

use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy, Value};
use covalence_data_spectec::{
    ArtifactError, AstError, AstSummary, BundleManifest, DeclarationId, IlDocument, IlKind, Limits,
    ManifestError, RuleId, SPECTEC_VERSION, WASM_3_RELEASE, WASM_3_REVISION, WASM_3_SOURCES,
    WASM_UPSTREAM, canonical_ast, parse_ast,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("vendor/wasm-3.0")
}

#[test]
fn official_il_rule_inventory_has_stable_nested_selectors() {
    let il = covalence_data_spectec::wasm3_bundle().unwrap();
    let il = il.il();

    let pure = DeclarationId::new(628, None).unwrap();
    let pure_rules = il.rules(pure).unwrap().unwrap();
    assert_eq!(pure_rules.len(), 78);
    let binop = RuleId::new(pure, [52]).unwrap();
    assert_eq!(
        pure_rules
            .iter()
            .find(|rule| rule.id() == &binop)
            .unwrap()
            .name(),
        "binop-val"
    );
    assert_eq!(il.rules(pure).unwrap().unwrap(), pure_rules);
    assert!(std::ptr::eq(
        il.rule(&binop).unwrap(),
        il.rule(&binop).unwrap()
    ));

    let read = DeclarationId::new(630, None).unwrap();
    let local_get = RuleId::new(read, [30]).unwrap();
    assert_eq!(
        il.rules(read)
            .unwrap()
            .unwrap()
            .iter()
            .find(|rule| rule.id() == &local_get)
            .unwrap()
            .name(),
        "local.get"
    );

    let step = DeclarationId::new(631, Some(1)).unwrap();
    let nested_pure = RuleId::new(step, [5, 8]).unwrap();
    assert_eq!(
        il.rules(step)
            .unwrap()
            .unwrap()
            .iter()
            .find(|rule| rule.id() == &nested_pure)
            .unwrap()
            .name(),
        "Step_pure"
    );
    assert!(il.rule(&RuleId::new(pure, [51]).unwrap()).is_some());
    assert!(il.rule(&RuleId::new(pure, [999]).unwrap()).is_none());
    assert!(RuleId::new(pure, []).is_none());
    assert!(RuleId::new(pure, [0]).is_none());

    let malformed =
        IlDocument::parse(b"(rel \"R\" x (rule missing-name))", Limits::default()).unwrap();
    assert!(matches!(
        malformed.rules(DeclarationId::new(1, None).unwrap()),
        Err(covalence_data_spectec::IlError::MissingRuleName { .. })
    ));
}

#[test]
fn official_il_declaration_inventory_is_exhaustive() {
    let root = root();
    let manifest = BundleManifest::decode(&read(&root, "manifest.drisl")).unwrap();
    let bytes = read(&root, &manifest.ast.artifact.path);
    let il = IlDocument::parse(&bytes, Limits::default()).unwrap();

    assert_eq!(il.roots().len(), 926);
    assert_eq!(il.declarations().len(), 980);
    assert_eq!(
        il.roots().iter().filter(|root| root.is_recursive()).count(),
        79
    );
    let count = |kind| {
        il.declarations()
            .iter()
            .filter(|declaration| declaration.kind() == kind)
            .count()
    };
    assert_eq!(count(IlKind::Type), 206);
    assert_eq!(count(IlKind::Definition), 458);
    assert_eq!(count(IlKind::Grammar), 229);
    assert_eq!(count(IlKind::Relation), 87);

    assert!(
        il.declarations()
            .iter()
            .all(|declaration| il.expression(declaration.id()).is_some())
    );
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
