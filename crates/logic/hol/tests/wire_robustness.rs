//! Adversarial CBOR for the fact table: what the raw representation layer
//! promises, and what it deliberately leaves unvalidated.

mod support;

use covalence_lib_cbor::{Value, into_writer};
use covalence_lib_hash::O256;
use covalence_logic_cas::CasFact;
use covalence_logic_hol::{Arena, Import, Table, wire};
use support::{ArenaCbor, Fix, direct_slot, encode, fact_id, free_slot, int, map, text};

fn star_row() -> Value {
    map(vec![("tag", text("kind.star"))])
}

fn accepts(label: &str, arena: ArenaCbor) -> Arena {
    arena
        .decode()
        .unwrap_or_else(|error| panic!("{label} should decode: {error}"))
}

fn rejects(label: &str, arena: ArenaCbor) {
    assert!(arena.decode().is_err(), "{label} should have been rejected");
}

#[test]
fn a_fact_free_arena_stays_off_the_wire_entirely() {
    // Empty optional cache fields are absent from the canonical encoding.
    let canonical = ArenaCbor::new().bytes();
    let decoded = wire::deserialize(canonical.as_slice()).expect("canonical bytes decode");

    assert_eq!(decoded, Arena::empty());
    assert_eq!(
        encode(&decoded),
        canonical,
        "the encoder must not add the fields"
    );
    assert_eq!(O256::from_bytes(&canonical), Arena::empty().addr());
}

#[test]
fn dense_columns_are_sparse_canonical_and_row_external() {
    let noncanonical = ArenaCbor::new()
        .defs(vec![star_row(), star_row()])
        .eq(vec![int(1), Value::Null, Value::Null])
        .syn_eq(vec![int(1), Value::Null])
        .conv(vec![int(1)])
        .sort(vec![Value::Null, int(1)])
        .bytes();
    let arena = wire::deserialize(noncanonical.as_slice()).expect("sparse columns decode");

    assert_eq!(arena.eq(support::row_id(1)).unwrap().get(), 1);
    assert_eq!(arena.syn_eq(support::row_id(1)).unwrap().get(), 1);
    assert_eq!(arena.conv(support::row_id(1)).unwrap().get(), 1);
    assert_eq!(arena.sort(support::row_id(2)).unwrap().get(), 1);
    assert_ne!(encode(&arena), noncanonical, "trailing nulls are removed");

    let encoded: Value = covalence_lib_cbor::from_reader(encode(&arena).as_slice()).unwrap();
    let Value::Map(root) = encoded else {
        panic!("arena map")
    };
    let Value::Map(hol) = &root
        .iter()
        .find(|(key, _)| key == &text("hol"))
        .expect("hol")
        .1
    else {
        panic!("hol map")
    };
    let Value::Array(defs) = &hol
        .iter()
        .find(|(key, _)| key == &text("defs"))
        .expect("defs")
        .1
    else {
        panic!("defs array")
    };
    assert!(defs.iter().all(|row| {
        let Value::Map(fields) = row else {
            return false;
        };
        fields
            .iter()
            .all(|(key, _)| key != &text("eq") && key != &text("sort"))
    }));
}

#[test]
fn a_non_null_column_member_without_a_row_is_rejected() {
    rejects(
        "semantic equality past defs",
        ArenaCbor::new().eq(vec![int(1)]),
    );
    rejects(
        "syntactic conversion past defs",
        ArenaCbor::new().conv(vec![Value::Null, int(1)]),
    );
}

#[test]
fn raw_columns_may_name_dangling_values_but_not_dangling_cells() {
    // Arena decoding establishes representation only. A checked Kernel is the
    // layer that interprets column targets and therefore requires residency.
    let arena = accepts(
        "dangling raw column targets",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .eq(vec![int(900)])
            .syn_eq(vec![int(901)])
            .conv(vec![int(902)])
            .sort(vec![int(903)]),
    );
    assert_eq!(arena.eq(support::row_id(1)).unwrap().get(), 900);
    assert_eq!(arena.syn_eq(support::row_id(1)).unwrap().get(), 901);
    assert_eq!(arena.conv(support::row_id(1)).unwrap().get(), 902);
    assert_eq!(arena.sort(support::row_id(1)).unwrap().get(), 903);
}

#[test]
fn occupied_and_free_slots_round_trip() {
    let arena = accepts(
        "a mixed table",
        ArenaCbor::new()
            .defs(vec![star_row(), star_row()])
            .slots(vec![
                direct_slot("syn", 1, 2),
                free_slot(None),
                direct_slot("conv", 2, 2),
            ])
            .free(int(2)),
    );

    assert_eq!(arena.syn_fact_slot_count(), 3);
    assert!(arena.syn_fact(fact_id(1)).is_some());
    assert!(arena.syn_fact(fact_id(2)).is_none());
    assert!(arena.syn_fact(fact_id(3)).is_some());
    support::assert_round_trips(&arena);
}

#[test]
fn every_relation_tag_and_only_those_decode() {
    for rel in ["syn", "alpha", "conv"] {
        accepts(
            rel,
            ArenaCbor::new()
                .defs(vec![star_row()])
                .slots(vec![direct_slot(rel, 1, 1)]),
        );
    }
    for rel in ["beta", "eta", "Syn", "", "syntactic"] {
        rejects(
            rel,
            ArenaCbor::new()
                .defs(vec![star_row()])
                .slots(vec![direct_slot(rel, 1, 1)]),
        );
    }
}

#[test]
fn a_slot_is_either_a_fact_or_a_free_link_and_never_both() {
    rejects(
        "fact fields plus a free link",
        ArenaCbor::new().defs(vec![star_row()]).slots(vec![map(vec![
            ("rel", text("syn")),
            ("in", int(1)),
            ("out", int(1)),
            ("next", Value::Null),
        ])]),
    );
    rejects(
        "an unknown field on a fact",
        ArenaCbor::new().defs(vec![star_row()]).slots(vec![map(vec![
            ("rel", text("syn")),
            ("in", int(1)),
            ("out", int(1)),
            ("note", text("hello")),
        ])]),
    );
    rejects(
        "an unknown field on a free link",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![map(vec![("next", Value::Null), ("note", int(1))])]),
    );
    for missing in [
        vec![("in", int(1)), ("out", int(1))],
        vec![("rel", text("syn")), ("out", int(1))],
        vec![("rel", text("syn")), ("in", int(1))],
    ] {
        rejects(
            "a fact missing a required field",
            ArenaCbor::new()
                .defs(vec![star_row()])
                .slots(vec![map(missing)]),
        );
    }
}

#[test]
fn every_reference_on_a_slot_stays_one_based() {
    for field in ["in", "out", "var", "val"] {
        let mut fields = vec![
            ("rel", text("syn")),
            ("in", int(1)),
            ("out", int(1)),
            ("var", int(1)),
            ("val", int(1)),
        ];
        for entry in &mut fields {
            if entry.0 == field {
                entry.1 = int(0);
            }
        }
        rejects(
            field,
            ArenaCbor::new()
                .defs(vec![star_row()])
                .slots(vec![map(fields)]),
        );
    }
    rejects(
        "a zero free link",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![map(vec![("next", int(0))])])
            .free(int(1)),
    );
    rejects(
        "a zero free-list head",
        ArenaCbor::new().defs(vec![star_row()]).free(int(0)),
    );
}

#[test]
fn optional_slot_fields_accept_omission_and_an_explicit_null() {
    let omitted = accepts(
        "omitted substitution endpoints",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![direct_slot("syn", 1, 1)]),
    );
    let explicit = accepts(
        "explicitly null substitution endpoints",
        ArenaCbor::new().defs(vec![star_row()]).slots(vec![map(vec![
            ("rel", text("syn")),
            ("var", Value::Null),
            ("val", Value::Null),
            ("in", int(1)),
            ("out", int(1)),
        ])]),
    );
    assert_eq!(omitted, explicit);

    let null_head = accepts(
        "an explicitly null free-list head",
        ArenaCbor::new().defs(vec![star_row()]).free(Value::Null),
    );
    assert_eq!(
        null_head,
        accepts("no head at all", ArenaCbor::new().defs(vec![star_row()]))
    );
}

#[test]
fn an_omitted_free_link_is_a_second_spelling_of_the_same_slot() {
    // `{}` and `{"next": null}` decode alike but only the second is emitted, so
    // two distinct addresses name the same arena. The raw layer is not a
    // canonical form; `Table::from_arena` is.
    let terse = accepts(
        "an empty free slot",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![map(vec![])])
            .free(int(1)),
    );
    let explicit = accepts(
        "an explicit free slot",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![free_slot(None)])
            .free(int(1)),
    );
    assert_eq!(terse, explicit);

    let terse_bytes = ArenaCbor::new()
        .defs(vec![star_row()])
        .slots(vec![map(vec![])])
        .free(int(1))
        .bytes();
    assert_ne!(terse_bytes, encode(&terse));
    assert_ne!(O256::from_bytes(&terse_bytes), terse.addr());
}

#[test]
fn one_sided_substitution_endpoints_survive_verbatim() {
    // `var` alone is the universal form and `val` alone is reserved, but the
    // representation layer checks neither claim: both are preserved verbatim
    // rather than normalized away.
    for present in ["var", "val"] {
        let arena = accepts(
            present,
            ArenaCbor::new().defs(vec![star_row()]).slots(vec![map(vec![
                ("rel", text("syn")),
                (present, int(1)),
                ("in", int(1)),
                ("out", int(1)),
            ])]),
        );
        let fact = arena.syn_fact(fact_id(1)).expect("occupied slot");
        assert_eq!(fact.var().is_some(), present == "var");
        assert_eq!(fact.val().is_some(), present == "val");
        support::assert_round_trips(&arena);
    }
}

#[test]
fn a_malformed_free_list_decodes_but_hands_out_no_facts() {
    // Free-list structure is an allocator concern, not a representation
    // invariant: nothing here can be mistaken for a checked fact.
    let dangling = accepts(
        "a head past the end of the table",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![direct_slot("syn", 1, 1)])
            .free(int(9)),
    );
    assert!(dangling.syn_fact(fact_id(1)).is_some());
    assert!(dangling.syn_fact(fact_id(9)).is_none());
    support::assert_round_trips(&dangling);

    let occupied_head = accepts(
        "a head pointing at an occupied slot",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![direct_slot("syn", 1, 1)])
            .free(int(1)),
    );
    support::assert_round_trips(&occupied_head);

    let cyclic = accepts(
        "a free list that loops",
        ArenaCbor::new()
            .defs(vec![star_row()])
            .slots(vec![free_slot(Some(2)), free_slot(Some(1))])
            .free(int(1)),
    );
    assert!(cyclic.syn_fact(fact_id(1)).is_none());
    assert!(cyclic.syn_fact(fact_id(2)).is_none());
    support::assert_round_trips(&cyclic);
}

#[test]
fn slot_references_are_not_resolved_against_the_definition_table() {
    // Endpoints may name rows that do not exist. Only a `Kernel`, which starts
    // empty and mints every fact through a rule, promises otherwise.
    let arena = accepts(
        "endpoints past the end of `defs`",
        ArenaCbor::new().slots(vec![direct_slot("conv", 400, 900)]),
    );
    let fact = arena.syn_fact(fact_id(1)).expect("occupied slot");
    assert_eq!(fact.input().get(), 400);
    assert_eq!(arena.tag(fact.input()), None);
    support::assert_round_trips(&arena);
}

#[test]
fn the_arena_object_rejects_unknown_fields() {
    rejects(
        "an unknown arena field",
        ArenaCbor::new().extra("syn_cache", Value::Array(vec![])),
    );
    rejects(
        "a misspelled fact table",
        ArenaCbor::new().extra("synfacts", Value::Array(vec![])),
    );
}

#[test]
fn a_cache_survives_being_nested_as_a_literal_import() {
    let mut fix = Fix::new();
    let star = fix.star;
    fix.syn_refl(None, covalence_logic_hol::SynRel::Conv, star)
        .expect("reflexivity");
    let inner = fix.kernel.into_arena();

    let mut outer = Arena::empty();
    outer
        .push_import(covalence_logic_hol::Import::Literal(Box::new(
            inner.clone(),
        )))
        .expect("literal import");
    support::assert_round_trips(&outer);

    let decoded = wire::deserialize(encode(&outer).as_slice()).expect("nested bytes decode");
    let covalence_logic_hol::Import::Literal(nested) = &decoded.imports()[0] else {
        panic!("the import must stay literal")
    };
    assert_eq!(**nested, inner);
}

fn nested_literal_imports(depth: usize) -> Arena {
    let mut arena = Arena::empty();
    for _ in 0..depth {
        let mut outer = Arena::empty();
        outer
            .push_import(Import::Literal(Box::new(arena)))
            .expect("one import remains addressable");
        arena = outer;
    }
    arena
}

#[test]
fn literal_import_byte_depth_boundary_is_representation_not_canonicity() {
    let supported = nested_literal_imports(126);
    let supported_bytes = encode(&supported);
    assert_eq!(
        wire::deserialize(supported_bytes.as_slice()).unwrap(),
        supported
    );

    // Rust arenas remain structurally valid and serializable past the byte
    // decoder's current 127-container recursion budget.  The limitation is a
    // property of that decoder, not of arena canonicity or the reference space.
    let deeper = nested_literal_imports(127);
    let deeper_bytes = encode(&deeper);
    assert!(wire::deserialize(deeper_bytes.as_slice()).is_err());
}

#[test]
fn a_decoded_table_keeps_the_address_of_the_bytes_it_came_from() {
    // `axs` and `ctx` are sets, so non-canonical input re-encodes differently.
    // `Table::addr` reports where the bytes came from, not where they would go.
    let bytes = ArenaCbor::new()
        .defs(vec![star_row()])
        .axs(vec![text("ax.z"), text("ax.a"), text("ax.z")])
        .ctx(vec![int(1), int(1)])
        .bytes();
    let table = Table::try_from(CasFact::from_bytes(bytes.clone())).expect("valid arena");

    assert_eq!(table.addr(), O256::from_bytes(&bytes));
    assert_ne!(
        table.addr(),
        table.as_ref().addr(),
        "the decoded content has a different canonical address"
    );
    assert_eq!(table.axioms().collect::<Vec<_>>(), ["ax.a", "ax.z"]);
    assert_eq!(table.context().len(), 1);
}

#[test]
fn bytes_that_are_not_an_arena_never_become_a_table() {
    for payload in [
        Value::Null,
        Value::Bool(true),
        int(7),
        Value::Array(vec![]),
        Value::Map(vec![]),
        text("arena"),
    ] {
        let mut bytes = Vec::new();
        into_writer(&payload, &mut bytes).expect("CBOR encodes");
        assert!(
            Table::try_from(CasFact::from_bytes(bytes.clone())).is_err(),
            "{payload:?} must not decode to an arena"
        );
        assert!(wire::deserialize(bytes.as_slice()).is_err());
    }
    assert!(Table::try_from(CasFact::from_bytes(&b""[..])).is_err());
    assert!(wire::deserialize(&b"not an arena"[..]).is_err());
}

#[test]
fn decoding_is_whole_object() {
    // `Table::try_from` promises that the *complete* fact bytes encode an
    // arena. Ignoring a suffix would give one arena unlimited addresses, which
    // is malleability in a content-addressed store.
    let canonical = ArenaCbor::new().defs(vec![star_row()]).bytes();
    assert!(wire::deserialize(canonical.as_slice()).is_ok());

    let mut padded = canonical.clone();
    padded.extend_from_slice(&[0xff, 0xff, 0xff]);
    assert!(wire::deserialize(padded.as_slice()).is_err());
    assert!(Table::try_from(CasFact::from_bytes(padded)).is_err());

    // A second complete arena is still a suffix, not a second object.
    let mut doubled = canonical.clone();
    doubled.extend_from_slice(&canonical);
    assert!(wire::deserialize(doubled.as_slice()).is_err());
}
