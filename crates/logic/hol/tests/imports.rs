//! Imports, proxies, and the untrusted resolver boundary.

mod support;

use covalence_logic_hol::{
    AmbPred, Arena, Import, ImportId, Kernel, KernelError, Link, LinkFormat, Lit, LitVec,
    ResolveError, Sort, Table, Tag, TmTag, TyTag,
};
use support::{Always, Counting, Fix, Never, Offline, row_id};

/// An arena holding `kind.star`, `ty.bool`, `true`, and a `bool` variable.
fn imported() -> Kernel {
    let mut kernel = Kernel::new();
    let star = kernel.star().expect("star");
    let bool_ty = kernel.bool_ty(star).expect("bool type");
    kernel.bool(bool_ty, true).expect("literal");
    kernel.tm_fv(7, bool_ty).expect("variable");
    kernel
}

fn link_to(table: &Table) -> Link {
    Link {
        format: LinkFormat::Cbor,
        blake3: table.addr(),
    }
}

#[test]
fn a_literal_import_never_consults_the_resolver() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let source = fix
        .import_literal(imported().into_arena())
        .expect("literal import");
    let proxy = fix
        .tm_ref(&mut Never, source, row_id(3), bool_ty)
        .expect("proxy");

    assert_eq!(fix.arena().tag(proxy), Some(Tag::Tm(TmTag::Ref)));
    assert_eq!(fix.arena().foreign(proxy), Some((source, row_id(3))));
}

#[test]
fn a_link_import_is_answered_once_per_call_and_address_checked() {
    let table = Table::from_arena(imported().into_arena()).expect("encodes");
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let source = fix.import_link(link_to(&table)).expect("link import");
    let mut resolver = Counting {
        table: table.clone(),
        calls: 0,
    };

    fix.tm_ref(&mut resolver, source, row_id(3), bool_ty)
        .expect("proxy");
    fix.tm_ref(&mut resolver, source, row_id(4), bool_ty)
        .expect("proxy");
    assert_eq!(resolver.calls, 2, "the kernel caches nothing itself");
}

#[test]
fn a_resolver_answering_for_another_address_is_rejected() {
    let wanted = Table::from_arena(imported().into_arena()).expect("encodes");
    let other = Table::from_arena(Arena::empty()).expect("encodes");
    assert_ne!(wanted.addr(), other.addr());

    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let source = fix.import_link(link_to(&wanted)).expect("link import");
    let error = fix
        .tm_ref(&mut Always(other.clone()), source, row_id(3), bool_ty)
        .expect_err("wrong address");

    match error {
        KernelError::Resolve {
            source:
                ResolveError::WrongAddress {
                    requested,
                    returned,
                },
        } => {
            assert_eq!(requested, wanted.addr());
            assert_eq!(returned, other.addr());
        }
        other => panic!("expected an address mismatch, got {other:?}"),
    }
    assert!(
        fix.arena().ambient_context().rows().next().is_none(),
        "a rejected proxy must record no premise"
    );
}

#[test]
fn a_resolver_failure_reaches_the_caller_intact() {
    let table = Table::from_arena(imported().into_arena()).expect("encodes");
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let source = fix.import_link(link_to(&table)).expect("link import");

    let error = fix
        .tm_ref(&mut Offline, source, row_id(3), bool_ty)
        .expect_err("offline");
    assert!(matches!(
        error,
        KernelError::Resolve {
            source: ResolveError::Resolver { .. }
        }
    ));
}

#[test]
fn each_proxy_records_exactly_the_premise_it_relies_on() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let source = fix
        .import_literal(imported().into_arena())
        .expect("literal import");

    let kind = fix
        .kind_ref(&mut Never, source, row_id(1))
        .expect("kind proxy");
    let ty = fix
        .ty_ref(&mut Never, source, row_id(2), star)
        .expect("type proxy");
    let term = fix
        .tm_ref(&mut Never, source, row_id(3), bool_ty)
        .expect("term proxy");

    assert_eq!(
        fix.arena().ambient_predicates(),
        &[
            AmbPred::ArenaOk { src: source },
            AmbPred::HolSort {
                src: source,
                ix: row_id(2),
                sort: star,
            },
            AmbPred::HolSort {
                src: source,
                ix: row_id(3),
                sort: bool_ty,
            },
        ]
    );
    assert_eq!(
        fix.arena().ambient_context().to_rows(),
        vec![
            LitVec::from_slice(&[Lit::positive(1)]),
            LitVec::from_slice(&[Lit::positive(2)]),
            LitVec::from_slice(&[Lit::positive(3)]),
        ]
    );
    assert_eq!(fix.category(kind).expect("resident"), Sort::Kind);
    assert_eq!(fix.category(ty).expect("resident"), Sort::Ty);
    assert_eq!(fix.category(term).expect("resident"), Sort::Tm);
    assert_eq!(fix.classifier(term).expect("typed"), bool_ty);
}

#[test]
fn a_proxy_must_agree_with_the_category_of_its_target() {
    let mut fix = Fix::new();
    let star = fix.star;
    let bool_ty = fix.bool_ty;
    let source = fix
        .import_literal(imported().into_arena())
        .expect("literal import");

    // Row 3 is a term, row 2 a type, row 1 a kind.
    assert!(matches!(
        fix.kind_ref(&mut Never, source, row_id(3)),
        Err(KernelError::WrongCategory {
            expected: Sort::Kind,
            ..
        })
    ));
    assert!(matches!(
        fix.ty_ref(&mut Never, source, row_id(3), star),
        Err(KernelError::WrongCategory {
            expected: Sort::Ty,
            ..
        })
    ));
    assert!(matches!(
        fix.tm_ref(&mut Never, source, row_id(1), bool_ty),
        Err(KernelError::WrongCategory {
            expected: Sort::Tm,
            ..
        })
    ));
    assert!(
        fix.arena().ambient_context().rows().next().is_none(),
        "no premise survives a rejected proxy"
    );
}

#[test]
fn a_proxy_into_a_row_that_does_not_exist_is_rejected() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let source = fix
        .import_literal(imported().into_arena())
        .expect("literal import");

    assert!(matches!(
        fix.tm_ref(&mut Never, source, row_id(99), bool_ty),
        Err(KernelError::Resolve {
            source: ResolveError::MissingReference { .. }
        })
    ));
    let last = fix.import_literal(Arena::empty()).expect("literal import");
    let absent_source = ImportId::new(last.get() + 10).expect("nonzero");
    assert!(matches!(
        fix.tm_ref(&mut Never, absent_source, row_id(1), bool_ty),
        Err(KernelError::Resolve {
            source: ResolveError::MissingImport { .. }
        })
    ));
}

#[test]
fn a_null_import_is_a_hole_rather_than_an_empty_arena() {
    let mut arena = Arena::empty();
    let source = arena.push_import(Import::Null).expect("null import");
    assert!(matches!(
        arena.resolve_import(&mut Never, source),
        Err(ResolveError::NullImport { .. })
    ));
    assert!(matches!(
        arena.resolve_foreign(&mut Never, source, row_id(1)),
        Err(ResolveError::NullImport { .. })
    ));
}

#[test]
fn a_literal_import_resolves_to_the_canonical_table_for_its_content() {
    let inner = imported().into_arena();
    let expected = Table::from_arena(inner.clone()).expect("encodes");

    let mut arena = Arena::empty();
    let source = arena
        .push_import(Import::Literal(Box::new(inner.clone())))
        .expect("literal import");
    let resolved = arena
        .resolve_import(&mut Never, source)
        .expect("literal imports need no resolver");

    assert_eq!(resolved.addr(), expected.addr());
    assert_eq!(**resolved.arena(), inner);
}

#[test]
fn proxy_navigation_reads_one_row_without_rebuilding_a_tree() {
    let inner = imported().into_arena();
    let mut owner = Arena::empty();
    let source = owner
        .push_import(Import::Literal(Box::new(inner)))
        .expect("literal import");
    let proxy = owner.push_tm_ref(source, row_id(3)).expect("proxy row");
    let type_proxy = owner.push_ty_ref(source, row_id(2)).expect("proxy row");

    let target = owner
        .resolve_proxy(&mut Never, proxy)
        .expect("term proxy resolves");
    assert_eq!(target.tag(), Tag::Tm(TmTag::Bool));
    assert_eq!(target.bool_value(), Some(true));
    assert_eq!(target.reference(), row_id(3));
    assert_eq!(target.children().len(), 0);

    let target = owner
        .resolve_proxy(&mut Never, type_proxy)
        .expect("type proxy resolves");
    assert_eq!(target.tag(), Tag::Ty(TyTag::Bool));
    assert_eq!(target.name(), None);
}

#[test]
fn a_raw_proxy_whose_target_changed_category_is_rejected() {
    let inner = imported().into_arena();
    let mut owner = Arena::empty();
    let source = owner
        .push_import(Import::Literal(Box::new(inner)))
        .expect("literal import");
    // Row 3 is a term, but this raw row claims it is a type.
    let lying = owner.push_ty_ref(source, row_id(3)).expect("proxy row");

    assert!(matches!(
        owner.resolve_proxy(&mut Never, lying),
        Err(ResolveError::CategoryMismatch {
            expected: Sort::Ty,
            actual: Sort::Tm,
        })
    ));

    let ordinary = owner.push_bool_ty().expect("row");
    assert!(matches!(
        owner.resolve_proxy(&mut Never, ordinary),
        Err(ResolveError::NotProxy { .. })
    ));
    assert!(matches!(
        owner.resolve_proxy(&mut Never, row_id(50)),
        Err(ResolveError::MissingReference { .. })
    ));
}

#[test]
fn imports_nest_and_every_level_is_addressed_independently() {
    let inner = imported().into_arena();
    let inner_table = Table::from_arena(inner.clone()).expect("encodes");

    let mut middle = Arena::empty();
    middle
        .push_import(Import::Literal(Box::new(inner)))
        .expect("literal import");
    let middle_table = Table::from_arena(middle.clone()).expect("encodes");
    assert_ne!(middle_table.addr(), inner_table.addr());

    let mut outer = Arena::empty();
    let source = outer
        .push_import(Import::Link(link_to(&middle_table)))
        .expect("link import");
    let resolved = outer
        .resolve_import(&mut Always(middle_table.clone()), source)
        .expect("link resolves");
    assert_eq!(resolved.addr(), middle_table.addr());

    let nested = resolved
        .imports()
        .first()
        .expect("the middle arena keeps its own import");
    let Import::Literal(nested) = nested else {
        panic!("the nested import must stay literal")
    };
    assert_eq!(
        Table::from_arena((**nested).clone())
            .expect("encodes")
            .addr(),
        inner_table.addr()
    );
}
