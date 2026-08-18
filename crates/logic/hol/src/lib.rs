//! Indexed, structurally checked arena syntax for `HolE`.

mod arena;
mod cbor;
mod relations;
mod tag;
mod theorem;

pub use arena::{
    AnyLink, Arena, ArenaError, ArenaObject, BytesObject, Expr, Format, ImportTable,
    ImportTableObject, Ix, Link, LinkKindError, LinkTarget, ObjectKind, Resolve, Segment,
    SharedArena, SharedImportTable, TheoremObject,
};
pub use cbor::{
    DecodeError, EncodeError, arena_from_value, arena_to_value, deserialize_cbor, from_value,
    import_table_from_value, import_table_link_from_value, import_table_to_value, serialize_cbor,
    thm_from_value, thm_to_value, to_value,
};
pub use covalence_lib_cbor::Value as CborValue;
pub use relations::{ImportId, Prop, RelRef, RelRefView, Relation, Relations};
pub use tag::{SurfaceTag, UnknownSurfaceTag};
pub use theorem::Thm;

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_lib_hash::O256;

    fn empty_imports() -> SharedImportTable {
        SharedImportTable::new(ImportTable::new()).unwrap()
    }

    fn sample_arena(imports: Link<ImportTableObject>) -> Arena {
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
    fn typed_links_reject_the_wrong_object_kind() {
        let link = AnyLink {
            addr: O256::from_bytes(b"theorem"),
            format: Format::Cbor,
            kind: ObjectKind::Theorem,
        };
        assert!(Link::<ArenaObject>::try_from(link).is_err());
    }

    #[test]
    fn imported_segments_resolve_lazily_through_one_table() {
        let imports_link = empty_imports();
        let imported = SharedArena::new(sample_arena(imports_link.link())).unwrap();
        let mut table = ImportTable::new();
        let import_id = table.push(imported.link()).unwrap();
        let mut arena = Arena::new(table);
        arena
            .add_segment(
                Segment::new(
                    Ix::new(1).unwrap(),
                    Ix::new(3).unwrap(),
                    import_id,
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
    fn relations_colocate_premises_and_conclusions() {
        let one = RelRef::pos(Ix::new(1).unwrap());
        let two = RelRef::neg(Ix::new(2).unwrap());
        let mut relations = Relations::new();
        relations.insert_premise(Relation::Imp, one, two);
        relations.insert_symmetric_conclusion(Relation::TyEq, one, two);
        assert!(relations.contains_premise(Relation::Imp, one, two));
        assert!(relations.contains_conclusion(Relation::TyEq, one, two));
        assert!(relations.contains_conclusion(Relation::TyEq, two, one));
    }

    #[test]
    fn theorem_cbor_round_trip_preserves_both_sides() {
        let imports = empty_imports();
        let arena = SharedArena::new(sample_arena(imports.link())).unwrap();
        let mut theorem = Thm::new(Some(arena.link()), Some(imports.link()));
        theorem.assume(7);
        theorem.conclude(7);
        let one = RelRef::pos(Ix::new(1).unwrap());
        theorem
            .relations_mut()
            .insert_conclusion(Relation::HasKind, one, one);
        let value = thm_to_value(&theorem).unwrap();
        assert_eq!(thm_from_value(&value).unwrap(), theorem);

        let premises = theorem.premises();
        let conclusion = theorem.conclusion();
        assert_eq!(premises.theorems().collect::<Vec<_>>(), [7]);
        assert!(conclusion.contains(Relation::HasKind, one, one));
        assert_eq!(Thm::from_props(premises, conclusion), Some(theorem));
    }

    #[test]
    fn one_sided_theorems_do_not_require_cloneable_links() {
        #[derive(Debug, Eq, PartialEq)]
        struct Handle(u8);

        let mut premise = Prop::new(Handle(1), Handle(2));
        premise.insert_theorem(3);
        let theorem = Thm::from_premises(premise);
        assert_eq!(theorem.premise_theorems().collect::<Vec<_>>(), [3]);
        assert_eq!(theorem.conclusion_theorems().count(), 0);

        let mut conclusion = Prop::new(Handle(1), Handle(2));
        conclusion.insert_theorem(4);
        let theorem = Thm::from_conclusion(conclusion);
        assert_eq!(theorem.premise_theorems().count(), 0);
        assert_eq!(theorem.conclusion_theorems().collect::<Vec<_>>(), [4]);

        let no_indices: Thm = Thm::new(None, None);
        assert_eq!(
            thm_from_value(&thm_to_value(&no_indices).unwrap()).unwrap(),
            no_indices
        );
    }
}
