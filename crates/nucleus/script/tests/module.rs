use covalence_nucleus_script::{compile_module, delaborate_module};

const ZERO: &str = "!0000000000000000000000000000000000000000000000000000000000000000";

#[test]
fn nested_namespaces_resolve_lexically_without_entering_the_kernel() {
    let source = format!(
        r"
        (import prelude {ZERO} {ZERO})
        (define root () bool true)
        (namespace option
          (define local () bool root)
          (namespace laws
            (define same () bool local)))
        "
    );
    let module = compile_module(&source).expect("module");

    let root = module.namespace().get("root").expect("root");
    assert_eq!(module.namespace().get("option.local"), Some(root));
    assert_eq!(module.namespace().get("option.laws.same"), Some(root));
    assert_eq!(module.imports().len(), 1);
    assert_eq!(module.imports()[0].name(), "prelude");

    let without_import = compile_module(
        r"
        (define root () bool true)
        (namespace option
          (define local () bool root)
          (namespace laws
            (define same () bool local)))
        ",
    )
    .expect("module without import");
    assert_eq!(
        module.kernel().arena().addr(),
        without_import.kernel().arena().addr(),
        "import metadata must not mutate checked state"
    );
}

#[test]
fn dotted_definition_names_create_relative_namespace_paths() {
    let module = compile_module("(namespace logic (define and.comm () bool true))")
        .expect("dotted definition");
    assert!(module.namespace().get("logic.and.comm").is_some());
}

#[test]
fn delaborator_names_rows_and_marks_every_other_row_anonymous() {
    let module = compile_module(
        r"
        (namespace booleans
          (define truth () bool true))
        ",
    )
    .expect("module");
    let text = delaborate_module(module.kernel(), module.namespace(), module.imports());

    assert!(text.starts_with("(#kernel "));
    assert!(text.contains("(namespace booleans"));
    assert!(text.contains("(name truth %"));
    assert!(text.contains("(anonymous %1)"));
}

#[test]
fn malformed_import_hashes_and_reserved_names_are_rejected() {
    assert!(compile_module("(import bad nope nope)").is_err());
    assert!(
        compile_module(
            "(import bad 0000000000000000000000000000000000000000000000000000000000000000 \
             0000000000000000000000000000000000000000000000000000000000000000)"
        )
        .is_err(),
        "hexadecimal symbols must not be accepted as typed address atoms"
    );
    assert!(compile_module("(namespace bad.name)").is_err());
    assert!(compile_module("(define %1 () bool true)").is_err());
}
