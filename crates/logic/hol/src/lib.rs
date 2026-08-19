//! Indexed, structurally checked arena syntax for `HolE`.
//!
//! This crate is part of the trusted computing base: its public constructors
//! and decoders must preserve their structural invariants on adversarial input.

#![forbid(unsafe_code)]

mod arena;
mod cbor;
mod tag;

pub use arena::{
    Arena, ArenaError, EMPTY_STATIC_ARENA, Expr, Format, ImportTable, Ix, Link, LinkRef,
    ObjectKind, OwnedVec, Resolve, Segment, SharedArena, SharedImportTable, StaticArena, StaticVec,
    TrustedVec,
};
pub use cbor::{
    DecodeError, EncodeError, arena_from_value, arena_to_value, deserialize_cbor, from_value,
    import_table_address_from_value, import_table_from_value, import_table_to_value,
    serialize_cbor, to_value,
};
pub use covalence_lib_cbor::Value as CborValue;
pub use tag::{SurfaceTag, UnknownSurfaceTag};

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
}
