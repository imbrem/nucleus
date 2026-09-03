use super::*;

#[cfg(test)]
mod mutation_tests {
    use super::*;

    fn empty_sequent() -> Sequent {
        Sequent {
            premise: Formula::And {
                negative: false,
                children: Vec::new(),
            },
            conclusion: Formula::Or {
                negative: false,
                children: Vec::new(),
            },
        }
    }

    #[test]
    fn root_pushes_relocate_logarithmically_and_preserve_allocator_invariants() {
        let mut checked = pack(&[empty_sequent()]).unwrap();
        let mut base = checked.root(0, Side::Left).unwrap().word().base();
        let mut relocations = 0_usize;
        let mut copied = 0_usize;
        for atom in 0..1_000_u32 {
            let before_words = checked.arena.words.len();
            checked
                .push_root(
                    0,
                    Side::Left,
                    &Formula::Literal {
                        atom,
                        negative: false,
                    },
                )
                .unwrap();
            let next = checked.root(0, Side::Left).unwrap().word().base();
            if next == base {
                assert_eq!(checked.arena.words.len(), before_words);
            } else {
                relocations += 1;
                copied += usize::try_from(atom).unwrap();
                base = next;
            }
            Checked::check(checked.arena.clone()).unwrap();
        }
        assert!(relocations <= 10);
        assert!(copied < 2_000);
    }

    #[test]
    fn pop_zeros_the_removed_slot() {
        let mut checked = pack(&[empty_sequent()]).unwrap();
        checked
            .push_root(
                0,
                Side::Left,
                &Formula::Literal {
                    atom: 1,
                    negative: false,
                },
            )
            .unwrap();
        let block = checked
            .arena
            .live_block(checked.root(0, Side::Left).unwrap().word().base())
            .unwrap();
        let removed = checked.pop_root(0, Side::Left).unwrap();
        assert_eq!(removed.word(), Word::literal(1, false).unwrap());
        assert_eq!(checked.arena.words[block.base + 1], Word::ZERO);
        Checked::check(checked.arena.clone()).unwrap();
    }

    #[test]
    fn trailing_slack_belongs_to_its_live_block_and_growth_promotes_the_free_root() {
        let mut checked = pack(&[empty_sequent()]).unwrap();
        let original = checked.root(0, Side::Left).unwrap().word().base();
        for atom in 1..=2 {
            checked
                .push_root(
                    0,
                    Side::Left,
                    &Formula::Literal {
                        atom,
                        negative: false,
                    },
                )
                .unwrap();
            assert_eq!(checked.root(0, Side::Left).unwrap().word().base(), original);
        }
        checked
            .push_root(
                0,
                Side::Left,
                &Formula::Literal {
                    atom: 3,
                    negative: false,
                },
            )
            .unwrap();
        assert_ne!(checked.root(0, Side::Left).unwrap().word().base(), original);
        assert_eq!(
            checked.free_blocks(),
            vec![Block {
                base: usize::try_from(original).unwrap(),
                size_class: 0
            }]
        );

        for atom in 4..=7 {
            checked
                .push_root(
                    0,
                    Side::Left,
                    &Formula::Literal {
                        atom,
                        negative: false,
                    },
                )
                .unwrap();
        }
        let root = Arena::pointer(checked.arena.free_root).unwrap();
        assert_eq!(checked.arena.header(root).unwrap().block.size_class, 1);
        assert!(matches!(
            checked
                .arena
                .directory_head(checked.arena.header(root).unwrap(), 0),
            Some(NullablePointer::Address(_))
        ));
        Checked::check(checked.arena.clone()).unwrap();
    }

    #[test]
    fn promotion_preserves_every_member_of_the_old_largest_ring() {
        let mut arena = Arena::new(vec![Word::ZERO; RESERVED_WORDS], Word::ZERO, Vec::new());
        let first = arena.append_live(0).unwrap();
        let second = arena.append_live(0).unwrap();
        let larger = arena.append_live(1).unwrap();
        arena.free(first).unwrap();
        arena.free(second).unwrap();
        arena.free(larger).unwrap();
        let checked = Checked::check(arena).unwrap();
        let free = checked.free_blocks();
        assert_eq!(free.len(), 3);
        assert_eq!(free.iter().filter(|block| block.size_class == 0).count(), 2);
        assert_eq!(free.iter().filter(|block| block.size_class == 1).count(), 1);
    }

    #[test]
    fn shared_roots_validate_and_mutation_copies_before_write() {
        let pointer = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let mut checked = Checked::check(Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, 2).unwrap(),
                Word::literal(1, false).unwrap(),
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            vec![(pointer, pointer)],
        ))
        .unwrap();
        checked
            .push_root(
                0,
                Side::Left,
                &Formula::Literal {
                    atom: 2,
                    negative: false,
                },
            )
            .unwrap();
        let view = checked.view(0).unwrap();
        assert_eq!(view.premise.len(), 2);
        assert_eq!(view.conclusion.len(), 1);
        Checked::check(checked.arena.clone()).unwrap();
    }

    #[test]
    fn refcount_overflow_is_typed_and_nonmutating() {
        let pointer = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let mut arena = Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, REFCOUNT_MAX).unwrap(),
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            Vec::new(),
        );
        let before = arena.clone();
        let block = arena.live_block(4).unwrap();
        assert_eq!(arena.live_refcount(block), Some(REFCOUNT_MAX));
        assert_eq!(
            arena.increment(pointer),
            Err(RuntimeError::RefcountOverflow)
        );
        assert_eq!(arena, before);
    }

    #[test]
    fn cow_aggregates_duplicate_increments_before_mutating() {
        let parent = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let child = Ref::new(Word::pointer(8, false).unwrap()).unwrap();
        let literal = Ref::new(Word::literal(1, false).unwrap()).unwrap();
        let arena = Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, 2).unwrap(),
                child.word(),
                child.word(),
                Word::ZERO,
                Arena::live_metadata(0, 0, REFCOUNT_MAX).unwrap(),
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            vec![(parent, literal)],
        );
        let mut checked = Checked::check(arena).unwrap();
        let before = checked.arena.clone();
        assert_eq!(
            checked.push_root(
                0,
                Side::Left,
                &Formula::Literal {
                    atom: 2,
                    negative: false,
                },
            ),
            Err(RuntimeError::RefcountOverflow)
        );
        assert_eq!(checked.arena, before);
        Checked::check(checked.arena.clone()).unwrap();
    }

    #[test]
    fn validator_accepts_safe_refcount_overestimates() {
        let root = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let literal = Ref::new(Word::literal(1, false).unwrap()).unwrap();
        Checked::check(Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, REFCOUNT_MAX).unwrap(),
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            vec![(root, literal)],
        ))
        .unwrap();
    }

    #[test]
    fn conservative_overcount_leaks_unreachable_storage_without_reuse() {
        let root = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let child = Ref::new(Word::pointer(8, false).unwrap()).unwrap();
        let literal = Ref::new(Word::literal(1, false).unwrap()).unwrap();
        let mut checked = Checked::check(Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, 1).unwrap(),
                child.word(),
                Word::ZERO,
                Word::ZERO,
                Arena::live_metadata(0, 0, 2).unwrap(),
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            vec![(root, literal)],
        ))
        .unwrap();
        let removed = checked.pop_root(0, Side::Left).unwrap();
        checked.reclaim(removed).unwrap();
        Checked::check(checked.arena.clone()).unwrap();
        assert_eq!(
            checked.arena.live_refcount(Block {
                base: 8,
                size_class: 0
            }),
            Some(1)
        );
        checked
            .push_root(
                0,
                Side::Left,
                &Formula::And {
                    negative: false,
                    children: Vec::new(),
                },
            )
            .unwrap();
        assert_eq!(
            checked.arena.live_refcount(Block {
                base: 8,
                size_class: 0
            }),
            Some(1)
        );
        assert!(checked.arena.words.len() >= 16);
        Checked::check(checked.arena.clone()).unwrap();
    }

    #[test]
    fn malformed_live_headers_and_refcounts_are_rejected() {
        let checked = pack(&[empty_sequent()]).unwrap();
        let (words, free, roots) = checked.arena.clone().into_parts();
        let left = usize::try_from(roots[0].0.word().base()).unwrap();
        for header in [0, (1 << 7) | 3, (1 << 7) | (30 << 2)] {
            let mut malformed = words.clone();
            malformed[left] = Word::from_raw(header);
            assert!(Checked::check(Arena::new(malformed, free, roots.clone())).is_err());
        }
    }

    #[test]
    fn non_pointer_low_bits_are_rejected() {
        assert!(Ref::new(Word::from_raw(5)).is_err());
        assert!(Ref::new(Word::from_raw(6)).is_err());
    }

    #[test]
    fn wide_mutation_and_views_never_rescan_zero_padding() {
        let mut checked = pack(&[empty_sequent()]).unwrap();
        Arena::reset_payload_scans();
        for atom in 1..=4_096 {
            checked
                .push_root(
                    0,
                    Side::Left,
                    &Formula::Literal {
                        atom,
                        negative: false,
                    },
                )
                .unwrap();
        }
        let premise = checked.view(0).unwrap().premise;
        assert_eq!(premise.len(), 4_096);
        for index in 0..premise.len() {
            assert_eq!(
                premise.child(index).unwrap().atom(),
                Some(u32::try_from(index).unwrap() + 1)
            );
        }
        for _ in 0..4_096 {
            checked.pop_root(0, Side::Left).unwrap();
        }
        assert_eq!(Arena::payload_scans(), 0);
    }

    #[test]
    fn owned_build_reserves_words_and_length_index_before_committing() {
        let mut checked = pack(&[]).unwrap();
        let formula = Formula::And {
            negative: false,
            children: (1..=128)
                .map(|atom| Formula::Or {
                    negative: false,
                    children: vec![Formula::Literal {
                        atom,
                        negative: false,
                    }],
                })
                .collect(),
        };
        checked.prepare_owned(&formula).unwrap();
        let word_capacity = checked.arena.words.capacity();
        let length_capacity = checked.arena.lengths.capacity();
        checked.build_owned(&formula).unwrap();
        assert_eq!(checked.arena.words.capacity(), word_capacity);
        assert_eq!(checked.arena.lengths.capacity(), length_capacity);
    }
}
