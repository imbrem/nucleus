//! End-to-end coverage for the untrusted theory front end.

use covalence_logic_hol::{Sort, Tag, TmTag};
use covalence_logic_hol_script::{TheoryError, compile_theory};

const COPRODUCT: &str = r"
  ; The universal property, as an open schema rather than an assertion.
  (define IsCoprod ('a 'b 't)
    (exists inl (-> 'a 't)
      (exists inr (-> 'b 't)
        (ty.forall 'c
          (forall f (-> 'a 'c)
            (forall g (-> 'b 'c)
              (exists h (-> 't 'c)
                (and
                  (and
                    (forall x 'a (= (h (inl x)) (f x)))
                    (forall y 'b (= (h (inr y)) (g y))))
                  (forall k (-> 't 'c)
                    (imp
                      (and
                        (forall x 'a (= (k (inl x)) (f x)))
                        (forall y 'b (= (k (inr y)) (g y))))
                      (= k h)))))))))))
";

#[test]
fn coproduct_schema_compiles_to_a_checked_boolean_root() {
    let compiled = compile_theory(COPRODUCT).expect("coproduct schema");
    let root = compiled.get("IsCoprod").expect("public root");

    assert_eq!(
        compiled.kernel().category(root).expect("category"),
        Sort::Tm
    );
    let classifier = compiled.kernel().classifier(root).expect("classifier");
    assert_eq!(
        compiled.kernel().arena().tag(classifier),
        Some(Tag::Ty(covalence_logic_hol::TyTag::Bool))
    );
    assert_eq!(
        compiled.definitions().collect::<Vec<_>>(),
        [("IsCoprod", root)]
    );
    assert!(compiled.get("IsCoprod/'a").is_some());
    assert!(compiled.get("IsCoprod/'b").is_some());
    assert!(compiled.get("IsCoprod/'t").is_some());

    // The type universal sits beneath the existentially bound injections and
    // its body mentions them. This is the open-quantifier case from #991.
    let last = i32::try_from(compiled.kernel().arena().len()).expect("arena fits Ref");
    assert!((1..=last).any(|index| {
        covalence_logic_hol::Ref::new(index).is_some_and(|reference| {
            compiled.kernel().arena().tag(reference) == Some(Tag::Tm(TmTag::TyForall))
        })
    }));
}

#[test]
fn compilation_is_deterministic_but_names_are_external_metadata() {
    let left = compile_theory(COPRODUCT).expect("left");
    let right = compile_theory(COPRODUCT).expect("right");
    assert_eq!(left.kernel().arena().addr(), right.kernel().arena().addr());
    assert_eq!(
        left.definitions().collect::<Vec<_>>(),
        right.definitions().collect::<Vec<_>>()
    );
    assert_eq!(
        left.symbols().collect::<Vec<_>>(),
        right.symbols().collect::<Vec<_>>()
    );
}

#[test]
fn malformed_and_ill_typed_sources_never_escape_checked_construction() {
    assert!(matches!(
        compile_theory("(define P ('a) true"),
        Err(TheoryError::Read { .. })
    ));
    assert!(matches!(
        compile_theory("(define P ('a) missing)"),
        Err(TheoryError::Unknown { .. })
    ));
    assert!(matches!(
        compile_theory("(define P ('a) (true true))"),
        Err(TheoryError::Kernel { .. })
    ));
}

#[test]
fn nesting_is_bounded_before_elaboration() {
    let source = format!("{}true{}", "(".repeat(257), ")".repeat(257));
    assert!(matches!(
        compile_theory(&source),
        Err(TheoryError::Read { .. })
    ));
}
