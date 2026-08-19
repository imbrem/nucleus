//! Indexed, structurally checked arena syntax for `HolE`.
//!
//! This crate is part of the trusted computing base: its public constructors
//! and decoders must preserve their structural invariants on adversarial input.

#![forbid(unsafe_code)]

mod arena;
mod cbor;
mod relations;
mod tag;
mod theorem;

pub use arena::{
    Arena, ArenaError, EMPTY_STATIC_ARENA, Expr, Format, ImportTable, Ix, Link, LinkRef,
    ObjectKind, OwnedVec, Resolve, Segment, SharedArena, SharedImportTable, StaticArena, StaticVec,
    TrustedVec,
};
pub use cbor::{
    DecodeError, EncodeError, arena_from_value, arena_to_value, ctx_from_value, ctx_to_value,
    deserialize_cbor, from_value, import_table_address_from_value, import_table_from_value,
    import_table_to_value, seq_from_value, seq_to_value, serialize_cbor, to_value,
};
pub use covalence_lib_cbor::Value as CborValue;
pub use relations::{Ctx, InvalidSRef, Relation, SRef, SRefView};
pub use tag::{SurfaceTag, UnknownSurfaceTag};
pub use theorem::{Seq, SharedSeq};

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_lib_hash::O256;

    fn empty_imports() -> SharedImportTable {
        SharedImportTable::new(ImportTable::new()).unwrap()
    }

    fn sample_arena(imports: O256) -> Arena {
        let mut arena = Arena::new(Some(imports));
        let star = arena.push(Expr::KindStar).unwrap();
        let bool_ty = arena.push(Expr::TyBool).unwrap();
        arena
            .push(Expr::KindArr {
                domain: star,
                codomain: star,
            })
            .unwrap();
        arena
            .push(Expr::TyArr {
                domain: bool_ty,
                codomain: bool_ty,
            })
            .unwrap();
        arena
    }

    #[test]
    fn import_tables_deduplicate_addresses() {
        let address = O256::from_bytes(b"one imported object");
        let mut table = ImportTable::new();
        assert_eq!(table.push(address).unwrap(), 0);
        assert_eq!(table.push(address).unwrap(), 0);
        assert_eq!(table.iter().collect::<Vec<_>>(), vec![address]);
    }

    const STATIC_DEFS: &[Expr] = &[Expr::KindStar, Expr::TyBool];
    const STATIC_ARENA: StaticArena = StaticArena::new_const(None, &[], 1, STATIC_DEFS);

    #[test]
    fn static_arena_uses_the_owned_wire_format() {
        STATIC_ARENA.validate().unwrap();
        let owned = STATIC_ARENA.to_owned().unwrap();
        assert_eq!(
            serialize_cbor(&STATIC_ARENA).unwrap(),
            serialize_cbor(&owned).unwrap()
        );
        assert_eq!(
            deserialize_cbor::<Arena>(&serialize_cbor(&STATIC_ARENA).unwrap()).unwrap(),
            owned
        );
    }

    #[test]
    fn expression_wire_shape_has_uniform_children_and_variable_leaves() {
        let one = Ix::new(1).unwrap();
        let two = Ix::new(2).unwrap();
        assert_eq!(
            to_value(&Expr::TyApp {
                function: one,
                argument: two,
            })
            .unwrap(),
            CborValue::Map(vec![
                (
                    CborValue::Text("tag".into()),
                    CborValue::Text("TY_APP".into()),
                ),
                (
                    CborValue::Text("ix".into()),
                    CborValue::Array(vec![1_u64.into(), 2_u64.into()]),
                ),
            ])
        );
        assert_eq!(
            to_value(&Expr::TyBv { index: 9 }).unwrap(),
            CborValue::Map(vec![
                (
                    CborValue::Text("tag".into()),
                    CborValue::Text("TY_BV".into()),
                ),
                (CborValue::Text("ix".into()), CborValue::Array(vec![])),
                (CborValue::Text("var".into()), 9_u64.into()),
            ])
        );
    }

    #[test]
    fn expression_wire_validates_declared_payloads_before_using_the_tag() {
        let mut fields = vec![
            (
                CborValue::Text("tag".into()),
                CborValue::Text("KIND_STAR".into()),
            ),
            (CborValue::Text("ix".into()), CborValue::Array(vec![])),
        ];
        fields.push((CborValue::Text("var".into()), 9_u64.into()));
        assert_eq!(
            from_value::<Expr>(&CborValue::Map(fields.clone())).unwrap(),
            Expr::KindStar
        );

        let last = fields.last_mut().unwrap();
        last.1 = CborValue::Text("not an integer".into());
        assert!(from_value::<Expr>(&CborValue::Map(fields.clone())).is_err());

        fields.last_mut().unwrap().1 = 9_u64.into();
        fields.push((CborValue::Text("var".into()), 10_u64.into()));
        assert!(from_value::<Expr>(&CborValue::Map(fields)).is_err());
    }

    #[test]
    fn every_hol_e_empty_surface_constructor_round_trips() {
        let a = Ix::new(1).unwrap();
        let b = Ix::new(2).unwrap();
        let c = Ix::new(3).unwrap();
        let expressions = [
            Expr::KindStar,
            Expr::KindArr {
                domain: a,
                codomain: b,
            },
            Expr::TyBool,
            Expr::TyArr {
                domain: a,
                codomain: b,
            },
            Expr::TyApp {
                function: a,
                argument: b,
            },
            Expr::TyLam { domain: a, body: b },
            Expr::TyBv { index: 7 },
            Expr::TySub {
                carrier: a,
                predicate: b,
            },
            Expr::TyExists { predicate: a },
            Expr::TyModel { predicate: a },
            Expr::TmBv { index: 7 },
            Expr::TmFv { name: 8, ty: a },
            Expr::TmApp {
                function: a,
                argument: b,
            },
            Expr::TmLam { domain: a, body: b },
            Expr::TmBool { value: false },
            Expr::TmBool { value: true },
            Expr::TmEq { left: b, right: c },
            Expr::TmEps {
                ty: a,
                predicate: b,
            },
            Expr::TmAbs {
                carrier: a,
                predicate: b,
                value: c,
            },
            Expr::TmRep {
                carrier: a,
                predicate: b,
                value: c,
            },
            Expr::TmCast { term: a, target: b },
        ];

        for expression in expressions {
            let encoded = to_value(&expression).unwrap();
            assert_eq!(from_value::<Expr>(&encoded).unwrap(), expression);
        }
    }

    #[test]
    fn arena_cbor_round_trip_and_hash_are_stable() {
        let imports = empty_imports();
        let arena = sample_arena(imports.link());
        let value = arena_to_value(&arena).unwrap();
        let decoded = arena_from_value(&value).unwrap();
        assert_eq!(decoded, arena);

        let first = SharedArena::new(arena.clone()).unwrap();
        let second = SharedArena::new(arena).unwrap();
        assert_eq!(first.address(), second.address());
        assert_eq!(to_value(&first).unwrap(), to_value(&first.link()).unwrap());

        let no_imports: Arena = Arena::new(None);
        assert_eq!(
            arena_from_value(&arena_to_value(&no_imports).unwrap()).unwrap(),
            no_imports
        );
    }

    #[test]
    fn arena_segments_reject_the_wrong_object_kind() {
        let link = LinkRef {
            import: 0,
            format: Format::CborSparse,
            kind: ObjectKind::Sequent,
        };
        assert!(
            Segment::new(
                Ix::new(1).unwrap(),
                Ix::new(2).unwrap(),
                link,
                Ix::new(1).unwrap(),
            )
            .is_err()
        );
    }

    #[test]
    fn segment_deserialization_replays_checked_construction() {
        #[derive(serde::Serialize)]
        struct RawSegment {
            start: Ix,
            end: Ix,
            link: LinkRef,
            source_start: Ix,
        }

        let wrong_kind = RawSegment {
            start: Ix::new(1).unwrap(),
            end: Ix::new(2).unwrap(),
            link: LinkRef {
                import: 0,
                format: Format::CborSparse,
                kind: ObjectKind::Sequent,
            },
            source_start: Ix::new(1).unwrap(),
        };
        assert!(deserialize_cbor::<Segment>(&serialize_cbor(&wrong_kind).unwrap()).is_err());

        let overflowing_source = RawSegment {
            start: Ix::new(1).unwrap(),
            end: Ix::new(3).unwrap(),
            link: LinkRef {
                import: 0,
                format: Format::CborDense,
                kind: ObjectKind::Arena,
            },
            source_start: Ix::new(i32::MAX as u32).unwrap(),
        };
        assert!(
            deserialize_cbor::<Segment>(&serialize_cbor(&overflowing_source).unwrap()).is_err()
        );
    }

    #[test]
    fn imported_segments_resolve_lazily_through_one_table() {
        let imports_link = empty_imports();
        let imported = SharedArena::new(sample_arena(imports_link.link())).unwrap();
        let mut table = ImportTable::new();
        let import_id = table.push(imported.address()).unwrap();
        let mut arena = Arena::new(table);
        arena
            .add_segment(
                Segment::new(
                    Ix::new(1).unwrap(),
                    Ix::new(3).unwrap(),
                    LinkRef {
                        import: import_id,
                        format: Format::CborDense,
                        kind: ObjectKind::Arena,
                    },
                    Ix::new(1).unwrap(),
                )
                .unwrap(),
            )
            .unwrap();
        assert!(
            matches!(arena.resolve(Ix::new(1).unwrap()), Resolve::Lazy { index, .. } if index == Ix::new(1).unwrap())
        );
        assert!(matches!(
            arena.resolve(Ix::new(3).unwrap()),
            Resolve::Missing
        ));
    }

    #[test]
    fn sequents_keep_two_plain_relation_sides() {
        let one = SRef::pos(Ix::new(1).unwrap());
        let two = SRef::neg(Ix::new(2).unwrap());
        let mut sequent: Seq = Seq::new(None, None);
        sequent.insert_premise(Relation::Imp, one, two);
        sequent.insert_symmetric_conclusion(Relation::TyEq, one, two);
        assert!(sequent.contains_premise(Relation::Imp, one, two));
        assert!(sequent.contains_conclusion(Relation::TyEq, one, two));
        assert!(sequent.contains_conclusion(Relation::TyEq, two, one));
    }

    #[test]
    fn context_and_sequent_wire_shapes_are_directly_nested() {
        let empty_body = CborValue::Map(vec![
            (CborValue::Text("sequents".into()), CborValue::Array(vec![])),
            (CborValue::Text("relations".into()), CborValue::Map(vec![])),
        ]);
        let context: Ctx = Ctx::new(None, None);
        assert_eq!(
            ctx_to_value(&context).unwrap(),
            CborValue::Map(vec![
                (CborValue::Text("arena".into()), CborValue::Null),
                (CborValue::Text("imports".into()), CborValue::Null),
                (CborValue::Text("body".into()), empty_body.clone()),
            ])
        );
        let sequent: Seq = Seq::new(None, None);
        assert_eq!(
            seq_to_value(&sequent).unwrap(),
            CborValue::Map(vec![
                (CborValue::Text("arena".into()), CborValue::Null),
                (CborValue::Text("imports".into()), CborValue::Null),
                (CborValue::Text("premises".into()), empty_body.clone()),
                (CborValue::Text("conclusion".into()), empty_body),
            ])
        );
    }

    #[test]
    fn signed_references_have_one_semantic_view() {
        assert_eq!(SRef::from_raw(i32::MIN), Err(InvalidSRef));
        assert_eq!(SRef::from_raw(0).unwrap().view(), SRefView::Null);
        let max = Ix::new(i32::MAX.cast_unsigned()).unwrap();
        assert_eq!(SRef::pos(max).view(), SRefView::Pos(max));
        assert_eq!(SRef::neg(max).view(), SRefView::Neg(max));
    }

    #[test]
    fn sequent_cbor_round_trip_preserves_both_sides() {
        let imports = empty_imports();
        let arena = SharedArena::new(sample_arena(imports.link())).unwrap();
        let mut sequent_imports = ImportTable::new();
        sequent_imports.push(arena.address()).unwrap();
        let sequent_imports = SharedImportTable::new(sequent_imports).unwrap();
        let mut sequent = Seq::new(
            Some(LinkRef {
                import: 0,
                format: Format::CborDense,
                kind: ObjectKind::Arena,
            }),
            Some(sequent_imports.link()),
        );
        let imported = LinkRef {
            import: 7,
            format: Format::CborSparse,
            kind: ObjectKind::Sequent,
        };
        sequent.assume(imported);
        sequent.conclude(imported);
        let one = SRef::pos(Ix::new(1).unwrap());
        sequent.insert_conclusion(Relation::HasKind, one, one);
        let value = seq_to_value(&sequent).unwrap();
        assert_eq!(seq_from_value(&value).unwrap(), sequent);

        let premises = sequent.premises();
        let conclusion = sequent.conclusion();
        assert_eq!(premises.sequents().collect::<Vec<_>>(), [imported]);
        assert!(conclusion.contains(Relation::HasKind, one, one));
        assert_eq!(Seq::from_contexts(premises, conclusion), Some(sequent));
    }

    #[test]
    fn one_sided_sequents_do_not_require_cloneable_links() {
        #[derive(Debug, Eq, PartialEq)]
        struct Handle(u8);

        let mut premise = Ctx::new(Handle(1), Handle(2));
        let premise_link = LinkRef {
            import: 3,
            format: Format::CborSparse,
            kind: ObjectKind::Sequent,
        };
        premise.insert_sequent(premise_link);
        let sequent = Seq::from_premises(premise);
        assert_eq!(
            sequent.premise_sequents().collect::<Vec<_>>(),
            [premise_link]
        );
        assert_eq!(sequent.conclusion_sequents().count(), 0);

        let mut conclusion = Ctx::new(Handle(1), Handle(2));
        let conclusion_link = LinkRef {
            import: 4,
            format: Format::CborSparse,
            kind: ObjectKind::Sequent,
        };
        conclusion.insert_sequent(conclusion_link);
        let sequent = Seq::from_conclusion(conclusion);
        assert_eq!(sequent.premise_sequents().count(), 0);
        assert_eq!(
            sequent.conclusion_sequents().collect::<Vec<_>>(),
            [conclusion_link]
        );

        let no_indices: Seq = Seq::new(None, None);
        assert_eq!(
            seq_from_value(&seq_to_value(&no_indices).unwrap()).unwrap(),
            no_indices
        );
    }

    #[test]
    fn arenas_and_sequents_form_a_lazy_import_graph() {
        let mut root: Arena = Arena::new(None);
        root.push(Expr::KindStar).unwrap();
        let root = SharedArena::new(root).unwrap();

        let mut arena_imports = ImportTable::new();
        let root_id = arena_imports.push(root.address()).unwrap();
        let arena_imports = SharedImportTable::new(arena_imports).unwrap();
        let mut dependent = Arena::new(arena_imports.table().clone());
        dependent
            .add_segment(
                Segment::new(
                    Ix::new(1).unwrap(),
                    Ix::new(2).unwrap(),
                    LinkRef {
                        import: root_id,
                        format: Format::CborDense,
                        kind: ObjectKind::Arena,
                    },
                    Ix::new(1).unwrap(),
                )
                .unwrap(),
            )
            .unwrap();
        assert!(
            matches!(dependent.resolve(Ix::new(1).unwrap()), Resolve::Lazy { link, .. }
            if link.address() == root.address() && link.kind() == ObjectKind::Arena)
        );
        let dependent =
            SharedArena::new(dependent.map_imports(|_| Some(arena_imports.link()))).unwrap();

        let mut first_imports = ImportTable::new();
        first_imports.push(dependent.address()).unwrap();
        let first_imports = SharedImportTable::new(first_imports).unwrap();
        let first = SharedSeq::new(Seq::new(
            Some(LinkRef {
                import: 0,
                format: Format::CborDense,
                kind: ObjectKind::Arena,
            }),
            Some(first_imports.address()),
        ))
        .unwrap();

        let mut second_imports = ImportTable::new();
        second_imports.push(dependent.address()).unwrap();
        second_imports.push(first.address()).unwrap();
        let second_imports = SharedImportTable::new(second_imports).unwrap();
        let mut second = Seq::new(
            Some(LinkRef {
                import: 0,
                format: Format::CborDense,
                kind: ObjectKind::Arena,
            }),
            Some(second_imports.address()),
        );
        second.assume(LinkRef {
            import: 1,
            format: Format::CborSparse,
            kind: ObjectKind::Sequent,
        });
        let second = SharedSeq::new(second).unwrap();

        assert!(second.sequent().link_ref_is_sequent(
            second_imports.table(),
            LinkRef {
                import: 1,
                format: Format::CborSparse,
                kind: ObjectKind::Sequent,
            }
        ));
        assert_eq!(to_value(&root).unwrap(), to_value(&root.link()).unwrap());
        assert_eq!(to_value(&first).unwrap(), to_value(&first.link()).unwrap());
        assert_eq!(
            to_value(&second).unwrap(),
            to_value(&second.link()).unwrap()
        );
    }
}
