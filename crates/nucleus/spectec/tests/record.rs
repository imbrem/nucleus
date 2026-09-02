use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy};
use covalence_data_spectec::{ClauseId, DeclarationId, IlDocument, Limits};
use covalence_logic_hol::{Kernel, Tag, TmTag};
use covalence_nucleus_spectec::{
    ADD_SLICE_TYPE_NAME, AddSliceArtifact, AddSliceArtifactError, AddSlicePlan, ArtifactError,
    CompilationRecord, CompileError, Compiler, Coverage, CoverageArtifact, CoverageDisposition,
    CoveragePlan, Disposition, IndexErasure, KernelRoot, SelectedCompileError, SelectedCompiler,
    Source, TYPE_NAME, TranslationCase, declare_hol_schema, least_closed_predicate,
};

#[test]
fn least_closed_predicate_builds_direct_hol_definition() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let least = least_closed_predicate(&mut kernel, bool_ty, predicate_ty, |kernel, _candidate| {
        kernel.bool(bool_ty, true)
    })
    .unwrap();

    assert_eq!(least.predicate_ty, predicate_ty);
    assert_eq!(
        kernel.arena().tag(least.predicate),
        Some(Tag::Tm(TmTag::Lam))
    );
    let value_term = kernel.tm_fv(100, value).unwrap();
    let proposition = kernel.app(least.predicate, value_term).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(proposition).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn least_closed_predicate_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let before = kernel.arena().len();

    assert!(
        least_closed_predicate(&mut kernel, bool_ty, predicate_ty, |kernel, candidate| {
            kernel.app(candidate, candidate)
        })
        .is_err()
    );
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn generic_hol_schema_declares_every_wasm3_signature() {
    let source = Source::wasm3().unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();

    assert_eq!(schema.policy(), IndexErasure::ValuePredicate);
    assert_eq!(schema.value(), value);
    assert_eq!(schema.bool_ty(), bool_ty);
    assert_eq!(schema.len(), 980);
    assert!(!schema.is_empty());
    for declaration in source.declarations() {
        let target = schema.declaration(declaration.id()).unwrap();
        assert_eq!(target.kind(), declaration.kind());
        kernel.classifier(target.reference()).unwrap();
    }
    let x = kernel.tm_fv(10_000, value).unwrap();
    let y = kernel.tm_fv(10_001, value).unwrap();
    let result = kernel.tm_fv(10_002, value).unwrap();
    let min = schema
        .declaration(DeclarationId::new(6, None).unwrap())
        .unwrap()
        .reference();
    let min_at_x = kernel.app(min, x).unwrap();
    let min_at_y = kernel.app(min_at_x, y).unwrap();
    let min_graph = kernel.app(min_at_y, result).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(min_graph).unwrap(), bool_ty)
            .unwrap()
    );

    let n_membership = schema
        .declaration(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .reference();
    let n_holds = kernel.app(n_membership, x).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(n_holds).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn generic_hol_schema_is_transactional_on_embedding_failure() {
    let source = Source::wasm3().unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let not_a_type = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().len();

    assert!(declare_hol_schema(&source, &mut kernel, not_a_type, bool_ty).is_err());
    assert_eq!(kernel.arena().len(), before);
}

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
fn add_slice_rejects_selected_rule_body_drift() {
    let original = Source::wasm3().unwrap();
    let mut bytes = covalence_data_spectec::WASM_3_AST_BYTES.to_vec();
    let rule = bytes
        .windows(b"\"binop-val\"".len())
        .position(|window| window == b"\"binop-val\"")
        .unwrap();
    let relative = bytes[rule..]
        .windows(b"\"binop_\"".len())
        .enumerate()
        .filter_map(|(position, window)| (window == b"\"binop_\"").then_some(position))
        .nth(1)
        .unwrap();
    let operation = rule + relative;
    bytes[operation + 4] = b'X';
    let il = IlDocument::parse(&bytes, Limits::default()).unwrap();
    let changed = Source::new(
        original.bundle(),
        original.ast(),
        original.release(),
        original.revision(),
        &il,
    )
    .unwrap();

    assert!(matches!(
        AddSlicePlan::build(&changed),
        Err(covalence_nucleus_spectec::AddSliceError::SemanticShape {
            case: TranslationCase::BinaryOperationValueRule,
            ..
        })
    ));
}

#[test]
fn generic_coverage_artifact_composes_without_add_policy() {
    let bundle = drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle");
    let ast = drisl::address(CidCodec::Raw, CidHash::Sha256, b"ast");
    let id = DeclarationId::new(1, None).unwrap();
    let plan = CoveragePlan::new(
        vec![Coverage {
            id,
            disposition: "handled",
        }],
        Vec::new(),
        Vec::new(),
    );
    let artifact = CoverageArtifact::new(bundle, ast, plan);

    assert_eq!(artifact.bundle(), bundle);
    assert_eq!(artifact.ast(), ast);
    assert_eq!(artifact.plan().declarations()[0].disposition, "handled");
    let (actual_bundle, actual_ast, plan) = artifact.into_parts();
    assert_eq!((actual_bundle, actual_ast), (bundle, ast));
    assert_eq!(plan.declarations()[0].id, id);
}

#[test]
fn selected_compiler_requires_every_generic_plan_case_once() {
    let declaration = DeclarationId::new(1, None).unwrap();
    let clause = ClauseId::new(declaration, [3]).unwrap();
    let plan = CoveragePlan::new(
        vec![
            Coverage {
                id: declaration,
                disposition: CoverageDisposition::Translate {
                    case: 1_u8,
                    source: (),
                },
            },
            Coverage {
                id: DeclarationId::new(2, None).unwrap(),
                disposition: CoverageDisposition::Reject("outside"),
            },
        ],
        vec![Coverage {
            id: clause,
            disposition: CoverageDisposition::Translate {
                case: 2_u8,
                source: (),
            },
        }],
        Vec::new(),
    );
    let mut compiler = SelectedCompiler::new(&plan, Kernel::new()).unwrap();
    assert_eq!(compiler.required(), 2);
    compiler
        .lower(1, |kernel| {
            Ok(vec![KernelRoot::new("carrier", kernel.star()?)])
        })
        .unwrap();
    let star = compiler.roots(1).unwrap()[0].reference();
    let rows = compiler.kernel().len();
    assert!(matches!(
        compiler.lower(1, |_| Ok(Vec::new())),
        Err(SelectedCompileError::AlreadyLowered { .. })
    ));
    assert_eq!(compiler.kernel().len(), rows);
    assert!(matches!(
        compiler.lower(9, |_| Ok(Vec::new())),
        Err(SelectedCompileError::UnknownCase { .. })
    ));
    assert_eq!(compiler.kernel().len(), rows);
    compiler
        .lower(2, |kernel| {
            Ok(vec![KernelRoot::new("type", kernel.bool_ty(star)?)])
        })
        .unwrap();
    let selected = compiler.finish().unwrap();
    assert_eq!(selected.roots(&1).unwrap()[0].role(), "carrier");
    assert_eq!(selected.roots(&2).unwrap()[0].role(), "type");

    let incomplete = SelectedCompiler::new(&plan, Kernel::new()).unwrap();
    assert!(matches!(
        incomplete.finish(),
        Err(SelectedCompileError::MissingCase { .. })
    ));
}

#[test]
fn add_slice_has_canonical_translation_cid() {
    let source = Source::wasm3().unwrap();
    let artifact = AddSliceArtifact::build(&source).unwrap();
    let bytes = artifact.encode().unwrap();
    assert_eq!(artifact.encode().unwrap(), bytes);
    assert_eq!(artifact.bundle(), source.bundle());
    assert_eq!(artifact.ast(), source.ast());
    assert_eq!(artifact.plan(), &AddSlicePlan::build(&source).unwrap());
    assert_eq!(
        artifact.cid().unwrap(),
        drisl::address(CidCodec::Drisl, CidHash::Sha256, &bytes)
    );
    assert_eq!(artifact.cid().unwrap().codec(), CidCodec::Drisl);
    assert_eq!(artifact.cid().unwrap().hash(), CidHash::Sha256);
    assert!(Policy::ATPROTO.accepts(artifact.cid().unwrap()));
    assert!(drisl::addresses(artifact.cid().unwrap(), &bytes));
    assert_eq!(
        ADD_SLICE_TYPE_NAME,
        "io.github.imbrem.nucleus.spectecAddSliceV1"
    );

    let decoded = AddSliceArtifact::decode(&bytes).unwrap();
    assert_eq!(decoded, artifact);
    assert_eq!(decoded.encode().unwrap(), bytes);
    decoded.verify_source(&source).unwrap();
    assert_eq!(
        AddSliceArtifact::decode_for_source(&bytes, &source).unwrap(),
        artifact
    );

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(matches!(
        AddSliceArtifact::decode(&trailing),
        Err(AddSliceArtifactError::RecordDecode { .. })
    ));

    let mut reordered_value = drisl::decode(Policy::ATPROTO, &bytes).unwrap();
    let covalence_data_cbor::drisl::Value::Map(fields) = &mut reordered_value else {
        panic!("artifact is a map");
    };
    let covalence_data_cbor::drisl::Value::Array(declarations) =
        fields.get_mut("declarations").unwrap()
    else {
        panic!("declarations is an array");
    };
    declarations.swap(0, 1);
    let reordered = drisl::encode(Policy::ATPROTO, &reordered_value).unwrap();
    let reordered = AddSliceArtifact::decode(&reordered).unwrap();
    assert!(matches!(
        reordered.verify_source(&source),
        Err(AddSliceArtifactError::SourceMismatch { .. })
    ));

    let mut value = drisl::decode(Policy::ATPROTO, &bytes).unwrap();
    let covalence_data_cbor::drisl::Value::Map(fields) = &mut value else {
        panic!("artifact is a map");
    };
    let covalence_data_cbor::drisl::Value::Array(declarations) =
        fields.get_mut("declarations").unwrap()
    else {
        panic!("declarations is an array");
    };
    declarations[1] = declarations[0].clone();
    let duplicate = drisl::encode(Policy::ATPROTO, &value).unwrap();
    assert!(matches!(
        AddSliceArtifact::decode(&duplicate),
        Err(AddSliceArtifactError::Schema { .. })
    ));
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
