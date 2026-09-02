use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy};
use covalence_data_spectec::{DeclarationId, IlDocument, Limits};
use covalence_logic_hol::Kernel;
use covalence_nucleus_spectec::{
    AddSlicePlan, ArtifactError, CompilationRecord, CompileError, Compiler, Disposition,
    KernelRoot, Source, TYPE_NAME, TranslationCase,
};

#[test]
fn add_slice_exhaustively_classifies_exact_structural_forms() {
    let source = Source::wasm3().unwrap();
    let first = AddSlicePlan::build(&source).unwrap();
    let second = AddSlicePlan::build(&source).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.declarations().len(), source.declaration_count());

    let translated = first
        .declarations()
        .iter()
        .map(|entry| entry.disposition)
        .chain(first.clauses().iter().map(|entry| entry.disposition))
        .chain(first.rules().iter().map(|entry| entry.disposition))
        .filter_map(|disposition| match disposition {
            Disposition::Translate { case, source } => Some((case, source)),
            Disposition::Reject(_) => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(translated.len(), 31);
    assert_eq!(
        translated
            .iter()
            .map(|(case, _)| *case)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        translated.len()
    );
    assert!(
        translated
            .iter()
            .any(|(case, _)| *case == TranslationCase::BinaryOperationValueRule)
    );
    assert!(
        translated
            .iter()
            .any(|(case, _)| *case == TranslationCase::LocalGetRule)
    );
    assert!(
        first
            .declarations()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );
    assert!(
        first
            .clauses()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );
    assert!(
        first
            .rules()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );

    let data_root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../data/spectec/vendor/wasm-3.0");
    for (_, span) in translated {
        assert!(span.first_line > 0);
        assert!(span.first_line <= span.last_line);
        let line_count = std::fs::read_to_string(data_root.join(span.path))
            .unwrap()
            .lines()
            .count();
        assert!(usize::try_from(span.last_line).unwrap() <= line_count);
    }
}

#[test]
fn wasm3_source_requires_every_declaration() {
    let source = Source::wasm3().unwrap();
    assert_eq!(source.declaration_count(), 980);
    let compiler = Compiler::new(source, Kernel::new());
    assert!(matches!(
        compiler.finish(),
        Err(CompileError::MissingDeclaration { .. })
    ));
}

#[test]
fn lowering_is_transactional_and_role_checked() {
    let source = Source::wasm3().unwrap();
    let first = DeclarationId::new(1, None).unwrap();
    let mut builder = Compiler::new(source, Kernel::new());
    let before = builder.kernel().len();
    assert!(matches!(
        builder.lower(first, |kernel| {
            let star = kernel.star()?;
            Ok(vec![
                KernelRoot::new("declaration", star),
                KernelRoot::new("declaration", star),
            ])
        }),
        Err(CompileError::DuplicateRole { .. })
    ));
    assert_eq!(builder.kernel().len(), before);
    assert_eq!(builder.completed(), 0);
}

#[test]
fn record_schema_uses_atproto_sha256_links() {
    assert_eq!(TYPE_NAME, "io.github.imbrem.nucleus.spectecCompilationV1");
    let source = Source::wasm3().unwrap();
    let compiler = Compiler::new(source, Kernel::new());
    let Err(CompileError::MissingDeclaration { id }) = compiler.finish() else {
        panic!("incomplete source must not freeze");
    };
    assert_eq!(id, DeclarationId::new(1, None).unwrap());

    let manifest = covalence_data_spectec::wasm3_bundle().unwrap();
    assert_eq!(manifest.manifest_cid().codec(), CidCodec::Drisl);
    assert_eq!(manifest.manifest_cid().hash(), CidHash::Sha256);
    assert!(Policy::ATPROTO.accepts(manifest.manifest_cid()));
    assert!(drisl::addresses(
        manifest.manifest_cid(),
        covalence_data_spectec::WASM_3_MANIFEST_BYTES
    ));
}

#[test]
fn complete_small_compilation_record_and_kernel_round_trip() {
    let il = IlDocument::parse(b"(typ \"T\" (inst (alias nat)))", Limits::default()).unwrap();
    let bundle_bytes = b"source manifest";
    let ast_bytes = b"(typ \"T\" (inst (alias nat)))";
    let bundle = drisl::address(CidCodec::Drisl, CidHash::Sha256, bundle_bytes);
    let ast = drisl::address(CidCodec::Raw, CidHash::Sha256, ast_bytes);
    let source = Source::new(bundle, ast, "test", "revision", &il).unwrap();
    let mut builder = Compiler::new(source, Kernel::new());
    let declaration = DeclarationId::new(1, None).unwrap();
    builder
        .lower(declaration, |kernel| {
            let star = kernel.star()?;
            Ok(vec![KernelRoot::new("declaration", star)])
        })
        .unwrap();
    let compiled = builder.finish().unwrap();

    let decoded = CompilationRecord::decode(compiled.record_drisl()).unwrap();
    assert_eq!(&decoded, compiled.record());
    assert_eq!(decoded.encode().unwrap(), compiled.record_drisl());
    let source = Source::new(bundle, ast, "test", "revision", &il).unwrap();
    decoded.verify_source(&source).unwrap();
    assert_eq!(
        decoded.verify_kernel(compiled.kernel_cbor()).unwrap(),
        *compiled.kernel().arena()
    );

    let mut damaged = compiled.kernel_cbor().to_vec();
    damaged.push(0);
    assert!(matches!(
        decoded.verify_kernel(&damaged),
        Err(ArtifactError::KernelAddress)
    ));
}
