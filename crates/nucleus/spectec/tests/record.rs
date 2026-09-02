use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy};
use covalence_data_spectec::{DeclarationId, IlDocument, Limits};
use covalence_logic_hol::Kernel;
use covalence_nucleus_spectec::{
    ADD_SLICE_TYPE_NAME, AddSliceArtifact, AddSliceArtifactError, AddSlicePlan, ArtifactError,
    CompilationRecord, CompileError, Compiler, Coverage, CoverageArtifact, CoveragePlan,
    Disposition, KernelRoot, ParameterInstruction, Program, ProgramError, Source, TYPE_NAME,
    TranslationCase, parameter_add_program, prove_parameter_add_agreement,
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
fn generic_program_schema_interprets_parameter_add() {
    let program = parameter_add_program();
    assert_eq!(
        program.instructions(),
        &[
            ParameterInstruction::LocalGet(0),
            ParameterInstruction::LocalGet(1),
            ParameterInstruction::Binary(covalence_nucleus_spectec::AddOperation::I32Add),
            ParameterInstruction::Return,
        ]
    );
    assert_eq!(
        program.evaluate(
            |index| Ok::<_, ()>([20_u32, 22][usize::try_from(index).unwrap()]),
            |_operation, left, right| Ok::<_, ()>(left + right),
        ),
        Ok(42)
    );

    let malformed = Program::new(vec![
        ParameterInstruction::LocalGet(0),
        ParameterInstruction::Binary(covalence_nucleus_spectec::AddOperation::I32Add),
        ParameterInstruction::Return,
    ]);
    assert!(matches!(
        malformed.evaluate(|_| Ok::<_, ()>(1_u32), |_, left, right| Ok(left + right)),
        Err(ProgramError::Evaluation(_))
    ));
}

#[test]
fn public_kernel_checks_direct_and_interpreted_add_agreement() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let word_ty = kernel.ty_fv(1, star).unwrap();
    let unary = kernel.ty_arr(word_ty, word_ty).unwrap();
    let binary = kernel.ty_arr(word_ty, unary).unwrap();
    let add = kernel.tm_fv(2, binary).unwrap();
    let left = kernel.tm_fv(3, word_ty).unwrap();
    let right = kernel.tm_fv(4, word_ty).unwrap();

    let before_theorems = kernel.thm().live_theorems().count();
    let agreement =
        prove_parameter_add_agreement(&mut kernel, bool_ty, word_ty, add, left, right).unwrap();

    assert_ne!(agreement.direct, agreement.interpreted);
    assert!(
        kernel
            .tm_eq(agreement.direct, agreement.interpreted)
            .unwrap()
    );
    let theorem = kernel.thm().get(agreement.theorem).unwrap();
    assert!(theorem.lhs.rows().next().is_none());
    let conclusions = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(conclusions.len(), 1);
    assert_eq!(conclusions[0].len(), 1);
    assert!(conclusions[0][0].is_positive());
    assert_eq!(
        conclusions[0][0].magnitude(),
        u32::try_from(agreement.proposition.get()).unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), before_theorems + 1);
    assert_eq!(kernel.classifier(agreement.proposition).unwrap(), bool_ty);
}

#[test]
fn checked_add_agreement_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let word_ty = kernel.ty_fv(1, star).unwrap();
    let left = kernel.tm_fv(2, word_ty).unwrap();
    let right = kernel.tm_fv(3, word_ty).unwrap();
    let wrong_add = kernel.tm_fv(4, word_ty).unwrap();
    let before_rows = kernel.len();
    let before_theorems = kernel.thm().live_theorems().count();

    assert!(
        prove_parameter_add_agreement(&mut kernel, bool_ty, word_ty, wrong_add, left, right)
            .is_err()
    );
    assert_eq!(kernel.len(), before_rows);
    assert_eq!(kernel.thm().live_theorems().count(), before_theorems);
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
