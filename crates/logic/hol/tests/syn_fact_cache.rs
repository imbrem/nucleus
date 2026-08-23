//! Slot allocator, free list, truncation, and content addressing for the
//! syntactic-fact cache, driven entirely through the public kernel surface.

mod support;

use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, SynRel, wire};
use support::{Fix, Lcg, encode, fact_id, slots};

fn refl(fix: &mut Fix, rel: SynRel) -> SynFactId {
    let star = fix.star;
    fix.syn_refl(None, rel, star).expect("reflexivity")
}

fn refls(fix: &mut Fix, count: usize) -> Vec<SynFactId> {
    (0..count).map(|_| refl(fix, SynRel::Syn)).collect()
}

#[test]
fn slots_are_one_based_and_dense_until_something_is_removed() {
    let mut fix = Fix::new();
    assert_eq!(fix.syn_fact_len(), 0);
    let ids = refls(&mut fix, 4);
    assert_eq!(
        ids.iter().map(|id| id.get()).collect::<Vec<_>>(),
        [1, 2, 3, 4]
    );
    assert_eq!(fix.syn_fact_len(), 4);
    assert!(slots(&fix).iter().all(Option::is_some));
}

#[test]
fn a_removed_slot_is_absent_to_every_reader() {
    let mut fix = Fix::new();
    let id = refl(&mut fix, SynRel::Syn);
    assert!(fix.syn_fact(id).is_ok());
    assert!(fix.remove_syn_fact(id));

    assert!(matches!(
        fix.syn_fact(id),
        Err(KernelError::MissingSynFact { id: missing }) if missing == id
    ));
    assert!(fix.arena().syn_fact(id).is_none());
    // The slot is still allocated: removal is not truncation.
    assert_eq!(fix.syn_fact_len(), 1);
    assert_eq!(fix.arena().syn_fact_slot_count(), 1);
}

#[test]
fn removal_is_idempotent_and_bounded() {
    let mut fix = Fix::new();
    let id = refl(&mut fix, SynRel::Syn);
    assert!(fix.remove_syn_fact(id));
    assert!(
        !fix.remove_syn_fact(id),
        "double removal must report failure"
    );
    assert!(
        !fix.remove_syn_fact(fact_id(2)),
        "slot 2 was never allocated"
    );
    assert!(!fix.remove_syn_fact(SynFactId::new(u64::MAX).expect("nonzero")));
    assert_eq!(fix.syn_fact_len(), 1);
}

#[test]
fn the_free_list_hands_slots_back_in_reverse_removal_order() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 3);
    assert!(fix.remove_syn_fact(ids[0]));
    assert!(fix.remove_syn_fact(ids[2]));

    assert_eq!(refl(&mut fix, SynRel::Alpha), ids[2]);
    assert_eq!(refl(&mut fix, SynRel::Alpha), ids[0]);
    // The list is exhausted, so the next allocation extends the table.
    assert_eq!(refl(&mut fix, SynRel::Alpha).get(), 4);
    assert_eq!(fix.syn_fact_len(), 4);
}

#[test]
fn reuse_rewrites_the_slot_rather_than_merging_with_it() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let id = refl(&mut fix, SynRel::Syn);
    assert!(fix.remove_syn_fact(id));

    let reused = fix
        .syn_refl(None, SynRel::Conv, bool_ty)
        .expect("reflexivity");
    assert_eq!(reused, id);
    let fact = fix.syn_fact(id).expect("reused slot");
    assert_eq!(fact.rel(), SynRel::Conv);
    assert_eq!(fact.input(), bool_ty);
}

#[test]
fn replacing_a_removed_slot_fails_without_disturbing_the_free_list() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 3);
    assert!(fix.remove_syn_fact(ids[1]));
    let before = fix.arena().addr();

    let star = fix.star;
    assert!(matches!(
        fix.syn_refl(Some(ids[1]), SynRel::Conv, star),
        Err(KernelError::MissingSynFact { id }) if id == ids[1]
    ));
    assert_eq!(
        fix.arena().addr(),
        before,
        "a rejected replacement must not mutate the arena"
    );
    // The slot is still on the free list, so it is still the next one out.
    assert_eq!(refl(&mut fix, SynRel::Syn), ids[1]);
}

#[test]
fn replacing_an_absent_slot_fails() {
    let mut fix = Fix::new();
    let star = fix.star;
    assert!(matches!(
        fix.syn_refl(Some(fact_id(1)), SynRel::Syn, star),
        Err(KernelError::MissingSynFact { .. })
    ));
    assert_eq!(fix.syn_fact_len(), 0);
}

#[test]
fn replacement_keeps_the_handle_and_swaps_the_payload() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let ids = refls(&mut fix, 2);
    let replaced = fix
        .syn_refl(Some(ids[0]), SynRel::Conv, bool_ty)
        .expect("replacement");

    assert_eq!(replaced, ids[0]);
    assert_eq!(fix.syn_fact_len(), 2);
    let fact = fix.syn_fact(ids[0]).expect("replaced slot");
    assert_eq!(fact.rel(), SynRel::Conv);
    assert_eq!(fact.input(), bool_ty);
    assert_eq!(fix.syn_fact(ids[1]).expect("untouched").input(), fix.star);
}

#[test]
fn truncation_drops_a_suffix_and_invalidates_its_handles() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 5);
    fix.truncate_syn_facts(2);

    assert_eq!(fix.syn_fact_len(), 2);
    assert!(fix.syn_fact(ids[0]).is_ok());
    assert!(fix.syn_fact(ids[1]).is_ok());
    for stale in &ids[2..] {
        assert!(
            fix.syn_fact(*stale).is_err(),
            "{stale:?} survived truncation"
        );
    }
}

#[test]
fn truncation_beyond_the_table_changes_nothing_observable() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 3);
    fix.truncate_syn_facts(usize::MAX);

    assert_eq!(fix.syn_fact_len(), 3);
    assert!(ids.iter().all(|id| fix.syn_fact(*id).is_ok()));
}

#[test]
fn truncated_slots_are_reissued_to_unrelated_facts() {
    let mut fix = Fix::new();
    let bool_ty = fix.bool_ty;
    let ids = refls(&mut fix, 3);
    fix.truncate_syn_facts(1);

    let reissued = fix
        .syn_refl(None, SynRel::Conv, bool_ty)
        .expect("reflexivity");
    assert_eq!(
        reissued, ids[1],
        "IDs are ephemeral cache handles, so truncation reissues them"
    );
    // A userspace index that kept `ids[1]` now reads a fact it never proved.
    let fact = fix.syn_fact(ids[1]).expect("reissued slot");
    assert_eq!(fact.input(), bool_ty);
    assert_eq!(fact.rel(), SynRel::Conv);
}

#[test]
fn truncation_normalizes_the_free_list_into_ascending_order() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 5);
    assert!(fix.remove_syn_fact(ids[1]));
    assert!(fix.remove_syn_fact(ids[3]));
    // Reverse-removal order would hand slot 4 back first.
    let length = fix.syn_fact_len();
    fix.truncate_syn_facts(length);

    assert_eq!(refl(&mut fix, SynRel::Syn), ids[1]);
    assert_eq!(refl(&mut fix, SynRel::Syn), ids[3]);
}

#[test]
fn a_length_preserving_truncation_still_rewrites_the_encoding() {
    // `truncate_syn_facts` is documented as retaining a prefix, but it also
    // rebuilds the free list, so a length-preserving call is not a no-op on
    // the content address. It is idempotent from the second call on.
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 4);
    assert!(fix.remove_syn_fact(ids[1]));
    assert!(fix.remove_syn_fact(ids[3]));

    let before = fix.arena().addr();
    let length = fix.syn_fact_len();
    fix.truncate_syn_facts(length);
    let once = fix.arena().addr();
    fix.truncate_syn_facts(length);

    assert_ne!(before, once, "the free-list order is part of the encoding");
    assert_eq!(once, fix.arena().addr(), "normalization is idempotent");
}

#[test]
fn removal_order_leaks_into_the_content_address() {
    // Two arenas with identical occupied facts and identical free slots hash
    // differently when the removals happened in a different order, because the
    // free list is stored as a spine rather than as a set.
    let build = |first: usize, second: usize| {
        let mut fix = Fix::new();
        let ids = refls(&mut fix, 4);
        assert!(fix.remove_syn_fact(ids[first]));
        assert!(fix.remove_syn_fact(ids[second]));
        (fix.arena().addr(), slots(&fix))
    };
    let (forward_addr, forward_slots) = build(1, 3);
    let (reverse_addr, reverse_slots) = build(3, 1);

    assert_eq!(forward_slots, reverse_slots, "same observable fact table");
    assert_ne!(forward_addr, reverse_addr, "different content address");
}

#[test]
fn clearing_the_cache_restores_the_pre_cache_address() {
    let mut fix = Fix::new();
    let empty = fix.arena().addr();
    let ids = refls(&mut fix, 3);
    assert_ne!(fix.arena().addr(), empty, "caching changes the address");

    assert!(fix.remove_syn_fact(ids[0]));
    fix.truncate_syn_facts(0);
    assert_eq!(
        fix.arena().addr(),
        empty,
        "an emptied cache must encode like one that never existed"
    );
}

#[test]
fn a_cache_free_arena_encodes_exactly_as_it_did_before_the_cache_existed() {
    let mut fix = Fix::new();
    let with_rows = encode(fix.arena());
    let id = refl(&mut fix, SynRel::Syn);
    assert!(fix.remove_syn_fact(id));
    fix.truncate_syn_facts(0);

    assert_eq!(
        encode(fix.arena()),
        with_rows,
        "`syn_facts` and `syn_free` must stay off the wire when unused"
    );
}

#[test]
fn the_free_list_survives_a_wire_round_trip() {
    let mut fix = Fix::new();
    let ids = refls(&mut fix, 5);
    assert!(fix.remove_syn_fact(ids[0]));
    assert!(fix.remove_syn_fact(ids[4]));
    assert!(fix.remove_syn_fact(ids[2]));

    let bytes = encode(fix.arena());
    let decoded = wire::deserialize(bytes.as_slice()).expect("canonical bytes decode");
    assert_eq!(&decoded, fix.arena());
    assert_eq!(encode(&decoded), bytes);
    for (position, expected) in slots(&fix).into_iter().enumerate() {
        assert_eq!(decoded.syn_fact(fact_id(position + 1)), expected);
    }
}

/// The reference model: one entry per allocated slot, `None` once removed.
type Model = Vec<Option<(SynRel, Ref)>>;

fn check(kernel: &Kernel, model: &Model) {
    assert_eq!(kernel.syn_fact_len(), model.len(), "slot count diverged");
    for (position, expected) in model.iter().enumerate() {
        let id = fact_id(position + 1);
        match (kernel.syn_fact(id), expected) {
            (Ok(fact), Some((rel, reference))) => {
                assert_eq!(fact.rel(), *rel, "{id:?} relation");
                assert_eq!(fact.input(), *reference, "{id:?} input");
                assert_eq!(fact.output(), *reference, "{id:?} output");
                assert_eq!(fact.var(), None, "{id:?} must stay direct");
                assert_eq!(fact.val(), None, "{id:?} must stay direct");
            }
            (Err(_), None) => {}
            (actual, expected) => {
                panic!(
                    "{id:?}: kernel says {:?}, model says {expected:?}",
                    actual.is_ok()
                )
            }
        }
    }
    let bytes = encode(kernel.arena());
    let decoded = wire::deserialize(bytes.as_slice()).expect("canonical bytes decode");
    assert_eq!(&decoded, kernel.arena(), "round trip changed the arena");
}

#[test]
fn randomized_allocator_traffic_matches_a_reference_model() {
    const RELATIONS: [SynRel; 3] = [SynRel::Syn, SynRel::Alpha, SynRel::Conv];

    for seed in 0..24u64 {
        let mut random = Lcg::new(seed);
        let mut fix = Fix::new();
        let pool = [fix.star, fix.bool_ty, fix.var(1), fix.lit(true)];
        let mut model: Model = Vec::new();

        for _ in 0..160 {
            let rel = RELATIONS[random.below(RELATIONS.len())];
            let reference = pool[random.below(pool.len())];
            let bound = model.len() + 2;
            match random.below(10) {
                0..=3 => {
                    let id = fix.syn_refl(None, rel, reference).expect("allocation");
                    let position = usize::try_from(id.get() - 1).expect("slot index");
                    assert!(
                        position <= model.len(),
                        "allocation skipped past the end of the table"
                    );
                    assert!(
                        model.get(position).copied().flatten().is_none(),
                        "allocation aliased an occupied slot"
                    );
                    if position == model.len() {
                        model.push(Some((rel, reference)));
                    } else {
                        model[position] = Some((rel, reference));
                    }
                }
                4..=5 => {
                    let position = random.below(bound);
                    let id = fact_id(position + 1);
                    let occupied = model.get(position).copied().flatten().is_some();
                    let result = fix.syn_refl(Some(id), rel, reference);
                    assert_eq!(result.is_ok(), occupied, "replacement of {id:?}");
                    if occupied {
                        model[position] = Some((rel, reference));
                    }
                }
                6..=7 => {
                    let position = random.below(bound);
                    let id = fact_id(position + 1);
                    let occupied = model.get(position).copied().flatten().is_some();
                    assert_eq!(fix.remove_syn_fact(id), occupied, "removal of {id:?}");
                    if occupied {
                        model[position] = None;
                    }
                }
                _ => {
                    let length = random.below(bound);
                    fix.truncate_syn_facts(length);
                    model.truncate(length);
                }
            }
            check(&fix.kernel, &model);
        }
    }
}
