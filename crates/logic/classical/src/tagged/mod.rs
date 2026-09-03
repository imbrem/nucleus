//! Tagged formula storage and theorem rules.
//!
//! Validation uses an explicit worklist and a bitmap for ownership. A checked
//! value stores only words and roots; decoded syntax is never retained beside
//! it.

mod kernel;
mod runtime;
mod syntax;
mod word;

#[cfg(test)]
mod cost_tests;
#[cfg(test)]
mod deep_arena_tests;
#[cfg(test)]
mod validator_tests;

pub use kernel::{EditError, Theorem};
#[cfg(test)]
pub(crate) use runtime::Arena;
pub use runtime::{Checked, RuntimeError, pack};
pub use syntax::{Formula, Sequent, Side};
pub use word::WordError;
pub(crate) use word::{Ref, Word};

#[cfg(test)]
mod tests {
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
    };

    use super::{Arena, Checked, Formula, Ref, Sequent, Theorem, Word, pack};

    #[derive(Default)]
    struct TraceHasher(Vec<u64>);

    impl Hasher for TraceHasher {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _bytes: &[u8]) {
            panic!("tagged structural hashing must use typed integer writes")
        }

        fn write_u8(&mut self, value: u8) {
            self.0.push(u64::from(value));
        }

        fn write_u32(&mut self, value: u32) {
            self.0.push(u64::from(value));
        }

        fn write_usize(&mut self, value: usize) {
            self.0
                .push(u64::try_from(value).expect("test trace length fits u64"));
        }
    }

    fn literal(atom: u32) -> Formula {
        Formula::Literal {
            atom,
            negative: false,
        }
    }

    fn pointer(base: u32) -> Word {
        Word::pointer(base, 0, false).expect("test pointer must fit")
    }

    #[test]
    fn machine_words_are_exact_sign_magnitude_values() {
        let positive = Word::literal(7, false).unwrap();
        let negative = positive.negated();
        assert_eq!(positive.raw(), 31);
        assert_eq!(negative.raw(), (1_u32 << 31) | 31);
        assert_eq!(Word::from_raw(negative.raw()), negative);
        assert_eq!(negative.tag(), 3);
        assert_eq!(negative.base(), 28);
        assert_eq!(Ref::new(negative).unwrap().negated().word(), positive);
        assert!(Ref::new(Word::ZERO).is_err());
        assert!(Word::literal(1 << 29, false).is_err());
    }

    #[test]
    fn canonical_packer_round_trips_nested_tagged_syntax() {
        let input = vec![Sequent {
            premise: Formula::And {
                negative: false,
                children: vec![
                    literal(1),
                    Formula::Sat {
                        negative: true,
                        children: vec![literal(2), literal(3)],
                    },
                ],
            },
            conclusion: Formula::Or {
                negative: false,
                children: vec![literal(4)],
            },
        }];
        let checked = pack(&input).unwrap();
        assert_eq!(checked.decode_sequents().unwrap(), input);
        assert_eq!(&checked.arena().words()[..4], [Word::ZERO; 4]);
        assert_eq!(checked.arena().free_root(), Word::ZERO);
        assert!(checked.free_blocks().is_empty());
        assert_eq!(Checked::check(checked.arena().clone()).unwrap(), checked);
    }

    #[test]
    fn intrusive_two_class_directory_validates() {
        let words = vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(4),
            pointer(4),
            Word::natural(1).unwrap(),
            pointer(12),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(12),
            pointer(12),
            Word::ZERO,
        ];
        let checked = Checked::check(Arena::new(words, pointer(4), vec![])).unwrap();
        assert!(checked.decode_sequents().unwrap().is_empty());
        assert_eq!(checked.free_blocks().len(), 2);
        assert_eq!(checked.free_blocks()[0].base(), 12);
        assert_eq!(checked.free_blocks()[0].size_class(), 0);
        assert_eq!(checked.free_blocks()[1].base(), 4);
        assert_eq!(checked.free_blocks()[1].size_class(), 1);
    }

    #[test]
    fn malformed_intrusive_backlinks_and_padding_are_rejected() {
        let bad_backlink = vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(4),
            pointer(4),
            Word::natural(1).unwrap(),
            pointer(12),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(12),
            pointer(4),
            Word::ZERO,
        ];
        assert!(Checked::check(Arena::new(bad_backlink, pointer(4), vec![])).is_err());

        let mut bad_padding = vec![
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(12),
            pointer(12),
            Word::natural(1).unwrap(),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            pointer(4),
            pointer(4),
            Word::natural(1).unwrap(),
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
            Word::ZERO,
        ];
        assert!(Checked::check(Arena::new(bad_padding.clone(), pointer(4), vec![])).is_ok());
        bad_padding[16] = Word::natural(1).unwrap();
        assert!(Checked::check(Arena::new(bad_padding, pointer(4), vec![])).is_err());
    }

    #[test]
    fn checked_equality_and_hash_ignore_allocator_layout() {
        let canonical = pack(&[Sequent {
            premise: literal(1),
            conclusion: literal(1),
        }])
        .unwrap();
        let (mut words, _, roots) = canonical.arena().clone().into_parts();
        let base = u32::try_from(words.len()).unwrap();
        let free = pointer(base);
        words.extend([Word::ZERO, free, free, Word::ZERO]);
        let with_free = Checked::check(Arena::new(words, free, roots)).unwrap();

        assert_ne!(canonical.arena(), with_free.arena());
        assert_eq!(canonical, with_free);
        let (words, _, roots) = with_free.arena().clone().into_parts();
        assert!(
            Checked::from_snapshot(
                words.into_iter().map(Word::raw).collect(),
                roots
                    .into_iter()
                    .map(|(left, right)| (left.word().raw(), right.word().raw()))
                    .collect(),
            )
            .is_err()
        );
        let snapshot = canonical.snapshot();
        assert_eq!(
            Checked::from_snapshot(snapshot.0, snapshot.1).unwrap(),
            canonical
        );
        let mut canonical_hash = DefaultHasher::new();
        canonical.hash(&mut canonical_hash);
        let mut with_free_hash = DefaultHasher::new();
        with_free.hash(&mut with_free_hash);
        assert_eq!(canonical_hash.finish(), with_free_hash.finish());
    }

    #[test]
    fn hash_feed_is_the_exact_lean_hash_trace() {
        let checked = pack(&[Sequent {
            premise: Formula::And {
                negative: false,
                children: vec![
                    literal(1),
                    Formula::Sat {
                        negative: true,
                        children: vec![Formula::Literal {
                            atom: 2,
                            negative: true,
                        }],
                    },
                ],
            },
            conclusion: Formula::Or {
                negative: false,
                children: Vec::new(),
            },
        }])
        .unwrap();
        let mut trace = TraceHasher::default();
        checked.hash(&mut trace);
        assert_eq!(trace.0, [1, 0, 0, 2, 3, 0, 1, 2, 1, 1, 3, 1, 2, 1, 0, 0]);
    }

    #[test]
    fn identity_proves_a_formula_from_itself() {
        // Mutation testing found nothing pinned this: `identity` could be made
        // to conclude the negation of its premise and every test still passed.
        for formula in [
            literal(1),
            Formula::Literal {
                negative: true,
                atom: 7,
            },
            Formula::And {
                negative: false,
                children: vec![literal(1), literal(2)],
            },
            Formula::Or {
                negative: true,
                children: vec![literal(3)],
            },
        ] {
            let table = Theorem::identity(formula.clone())
                .expect("identity")
                .checked()
                .decode_sequents()
                .expect("decode");
            assert_eq!(table.len(), 1);
            assert_eq!(table[0].premise, formula, "premise is the formula itself");
            assert_eq!(
                table[0].conclusion, formula,
                "conclusion is the same formula, with the same polarity"
            );
        }
    }

    #[test]
    fn identity_append_and_canonical_edits_remain_sealed() {
        let p = literal(1);
        let q = literal(2);
        let formula = Formula::And {
            negative: false,
            children: vec![q.clone(), p.clone(), p.clone()],
        };
        let identity = Theorem::identity(formula).unwrap();
        let sorted = identity
            .canonical_sort_root_by_key(0, super::Side::Left, |formula| match formula {
                Formula::Literal { atom, .. } => *atom,
                _ => u32::MAX,
            })
            .unwrap();
        let deduped = sorted.canonical_dedupe_root(0, super::Side::Left).unwrap();
        let weakened = deduped.weaken(0, super::Side::Left, q.clone()).unwrap();
        let combined = weakened
            .append(&Theorem::identity(q.clone()).unwrap())
            .unwrap();
        let table = combined.checked().decode_sequents().unwrap();
        assert_eq!(table.len(), 2);
        let Formula::And { children, .. } = &table[0].premise else {
            panic!("edited premise must remain an AND")
        };
        assert_eq!(children, &[p, q.clone(), q]);
    }
}
