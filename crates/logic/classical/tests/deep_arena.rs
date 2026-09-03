//! Depth is a property of untrusted bytes, so nothing may recurse on it.
//!
//! `covalence_data_classical::decode_checked` hands whatever arrived over the
//! wire to `Checked::check`. When validation, decoding, or destruction
//! recursed once per nesting level, a small blob of deeply nested words could
//! exhaust the stack -- and a destructor cannot report that, or be skipped.
//! This file builds such an arena directly from words, so no recursive
//! constructor runs before the code under test does.

use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use covalence_logic_classical::tagged::{Arena, Checked, Formula, Ref, Word};

/// A left-nested chain of `depth` unary `AND` nodes over one literal.
///
/// Every node is a smallest-class block: one metadata word, one child
/// reference, then the zero terminator and one word of padding. The chain
/// tiles storage exactly, so the arena is valid and the whole of it is
/// reachable from the single root.
fn nested_chain(depth: usize) -> Arena {
    let mut words = vec![Word::ZERO; 4];
    let leaf = Word::literal(1, false).expect("literal fits");
    for level in 0..depth {
        let base = 4 + 4 * level;
        let child = if level + 1 == depth {
            leaf
        } else {
            let next = u64::try_from(base + 4).expect("address fits");
            Word::pointer(next, 0, false).expect("pointer fits")
        };
        words.extend([Word::natural(0).expect("size class fits"), child]);
        words.extend([Word::ZERO, Word::ZERO]);
    }
    let root = Ref::new(Word::pointer(4, 0, false).expect("pointer fits")).expect("root is a ref");
    let conclusion = Ref::new(leaf).expect("literal is a ref");
    Arena::new(words, Word::ZERO, vec![(root, conclusion)])
}

fn chain_depth(formula: &Formula) -> usize {
    let mut depth = 0;
    let mut current = formula;
    while let Formula::And { children, .. } = current {
        depth += 1;
        match children.as_slice() {
            [only] => current = only,
            _ => break,
        }
    }
    depth
}

#[test]
fn a_shallow_chain_validates_and_decodes() {
    let checked = Checked::check(nested_chain(64)).expect("valid arena");
    let table = checked.decode_sequents().expect("decodes");
    assert_eq!(table.len(), 1);
    assert_eq!(chain_depth(&table[0].premise), 64);
}

#[test]
fn validation_decoding_and_destruction_survive_an_arena_too_deep_to_recurse() {
    // 200_000 levels is 6.4 MB of words. The former validator recursed once
    // per level and aborted the process well below this; so did the derived
    // destructor for the syntax it produced.
    let depth = 200_000;
    let checked = Checked::check(nested_chain(depth)).expect("valid arena");
    let table = checked.decode_sequents().expect("decodes");
    assert_eq!(chain_depth(&table[0].premise), depth);
    // Structural equality and hashing walk the words, not the tree, so they
    // are safe at this depth too.
    assert_eq!(checked, Checked::check(nested_chain(depth)).expect("valid"));
    let mut digest = DefaultHasher::new();
    checked.hash(&mut digest);
    std::hint::black_box(digest.finish());
    drop(table);
    drop(checked);
}

#[test]
fn a_chain_that_does_not_tile_storage_is_rejected() {
    // Coverage is the conjunct the running total decides. One extra word at
    // the end belongs to no block, so the arena must not validate.
    let (mut words, free_root, roots) = nested_chain(1_000).into_parts();
    words.push(Word::ZERO);
    assert!(Checked::check(Arena::new(words, free_root, roots)).is_err());
}

#[test]
fn a_chain_that_revisits_a_block_is_rejected() {
    // Aliasing is the conjunct the claim decides: pointing the last node back
    // at the first makes one block reachable twice.
    let (mut words, free_root, roots) = nested_chain(1_000).into_parts();
    let last = 4 + 4 * 999;
    words[last + 1] = Word::pointer(4, 0, false).expect("pointer fits");
    assert!(Checked::check(Arena::new(words, free_root, roots)).is_err());
}
