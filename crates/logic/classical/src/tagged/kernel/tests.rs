use super::*;

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(atom: u32) -> Formula {
        Formula::Literal {
            atom,
            negative: false,
        }
    }

    #[test]
    fn canonical_cross_moves_and_complements_the_final_owned_formula() {
        let p = literal(1);
        let checked = pack(&[Sequent {
            premise: Formula::And {
                negative: false,
                children: vec![p.clone()],
            },
            conclusion: Formula::Or {
                negative: false,
                children: vec![p.clone()],
            },
        }])
        .unwrap();
        // This private test sequent is the valid implication `p -> p` in the
        // selected positive-root presentation. Production callers cannot use
        // this constructor.
        let theorem = Theorem { checked };
        let mut crossed = theorem;
        crossed.cross_root_mut(0, Side::Left).unwrap();
        let table = crossed.checked().decode_sequents().unwrap();
        let sequent = &table[0];
        assert_eq!(
            sequent.premise,
            Formula::And {
                negative: false,
                children: vec![]
            }
        );
        assert_eq!(
            sequent.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p.clone(), p.negated()]
            }
        );
    }

    #[test]
    fn cut_and_resolve_remove_first_structural_pivots() {
        let p = literal(1);
        let not_p = p.clone().negated();
        let positive = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![p.clone()],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![p.clone(), p.clone()],
                },
            }])
            .unwrap(),
        };
        let negative = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![not_p.clone()],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![not_p.clone()],
                },
            }])
            .unwrap(),
        };

        let cut = positive.cut(0, &positive, 0, &p).unwrap();
        let cut_table = cut.checked().decode_sequents().unwrap();
        let cut_result = &cut_table[0];
        assert_eq!(
            cut_result.premise,
            Formula::And {
                negative: false,
                children: vec![p.clone()]
            }
        );
        assert_eq!(
            cut_result.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p.clone(), p.clone(), p.clone()]
            }
        );

        let resolved = positive.resolve(0, &negative, 0, &p).unwrap();
        let resolved_table = resolved.checked().decode_sequents().unwrap();
        let resolved_result = &resolved_table[0];
        assert_eq!(
            resolved_result.premise,
            Formula::And {
                negative: false,
                children: vec![p.clone(), not_p]
            }
        );
        assert_eq!(
            resolved_result.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p]
            }
        );
    }

    #[test]
    fn failed_mutation_leaves_theorem_unchanged() {
        let mut theorem = Theorem::identity(literal(1)).unwrap();
        let before = theorem.clone();
        assert!(theorem.weaken_mut(0, Side::Left, &literal(2)).is_err());
        assert_eq!(theorem, before);
        assert!(theorem.cross_root_mut(1, Side::Left).is_err());
        assert_eq!(theorem, before);
    }

    #[test]
    fn public_refcount_overflow_is_recoverable_and_nonmutating() {
        use crate::tagged::{Arena, Ref, Word};

        const REFCOUNT_MAX: u32 = (1 << 25) - 1;
        let parent = Ref::new(Word::pointer(4, false).unwrap()).unwrap();
        let child = Ref::new(Word::pointer(8, false).unwrap()).unwrap();
        let arena = Arena::new(
            vec![
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
                Word::from_raw(2 << 7),
                child.word(),
                child.word(),
                Word::ZERO,
                Word::from_raw(REFCOUNT_MAX << 7),
                Word::ZERO,
                Word::ZERO,
                Word::ZERO,
            ],
            Word::ZERO,
            vec![(parent, parent)],
        );
        let mut theorem = Theorem {
            checked: Checked::check(arena).unwrap(),
        };
        let before = theorem.clone();

        assert_eq!(
            theorem.weaken_mut(0, Side::Left, &literal(1)),
            Err(EditError::Runtime {
                source: RuntimeError::RefcountOverflow,
            })
        );
        assert_eq!(theorem, before);
        Checked::check(theorem.checked.arena().clone()).unwrap();
    }

    #[test]
    fn refutation_bridge_produces_empty_disjunction() {
        let clause = Formula::Or {
            negative: false,
            children: vec![literal(1)],
        };
        let theorem = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: Vec::new(),
                },
                conclusion: Formula::Sat {
                    negative: true,
                    children: vec![clause.clone()],
                },
            }])
            .unwrap(),
        };
        let result = theorem.refutation_to_false(0).unwrap();
        assert_eq!(
            result.checked.decode_sequents().unwrap(),
            [Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![clause]
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: Vec::new()
                },
            }]
        );
    }

    #[test]
    fn path_rewrites_are_checked_and_transactional() {
        let p = literal(1);
        let not_p = p.clone().negated();
        let formula = Formula::And {
            negative: false,
            children: vec![Formula::Or {
                negative: true,
                children: vec![p.clone(), not_p.clone()],
            }],
        };
        let theorem = Theorem::identity(formula).unwrap();
        let nested = FormulaPath::new(0, Side::Left, vec![0]);
        let demorgan = theorem.demorgan(&nested).unwrap();
        let selected = &demorgan.checked.decode_sequents().unwrap()[0].premise;
        assert!(matches!(selected, Formula::And { children, .. }
            if matches!(&children[0], Formula::And { negative: false, children }
                if children == &vec![not_p, p])));
        let before = theorem.clone();
        assert!(
            theorem
                .demorgan(&FormulaPath::new(0, Side::Left, vec![4]))
                .is_err()
        );
        assert_eq!(theorem, before);
    }

    #[test]
    fn contradiction_flatten_permute_and_dedup_preserve_equivalence() {
        let p = literal(1);
        let q = literal(2);
        let target = Formula::And {
            negative: false,
            children: vec![
                p.clone(),
                Formula::And {
                    negative: false,
                    children: vec![q.clone(), q.clone()],
                },
                p.clone().negated(),
            ],
        };
        let theorem = Theorem::identity(target).unwrap();
        let root = FormulaPath::new(0, Side::Left, Vec::new());
        let flattened = theorem.flatten(&root, 1).unwrap();
        let deduped = flattened.dedup_local(&root, 2, 1).unwrap();
        let permuted = deduped.permute(&root, &[2, 1, 0]).unwrap();
        let mut contradiction = permuted;
        contradiction.contradiction_mut(&root, 0, 2).unwrap();
        assert_eq!(
            contradiction.checked.decode_sequents().unwrap()[0].premise,
            Formula::Or {
                negative: false,
                children: Vec::new()
            }
        );

        let mut packed = theorem.clone();
        packed.flatten_mut(&root, 1).unwrap();
        packed.dedup_local_mut(&root, 2, 1).unwrap();
        packed.permute_mut(&root, &[2, 1, 0]).unwrap();
        packed.contradiction_mut(&root, 0, 2).unwrap();
        assert_eq!(
            packed.checked.decode_sequents().unwrap()[0].premise,
            Formula::Or {
                negative: false,
                children: Vec::new()
            }
        );

        for formula in [
            Formula::Or {
                negative: true,
                children: vec![p.clone(), p.clone().negated()],
            },
            Formula::And {
                negative: true,
                children: vec![p.clone(), p.clone().negated()],
            },
            Formula::Sat {
                negative: true,
                children: vec![p.clone(), p.clone().negated()],
            },
        ] {
            let theorem = Theorem::identity(formula).unwrap();
            let mut result = theorem;
            result.contradiction_mut(&root, 0, 1).unwrap();
            let premise = &result.checked.decode_sequents().unwrap()[0].premise;
            assert!(matches!(premise,
                Formula::And { negative: true, children } | Formula::Or { negative: true, children }
                if children.is_empty()));
        }
    }

    #[test]
    fn bidirectional_theorems_authorize_path_rewrite() {
        let p = literal(1);
        let q = literal(2);
        let forward = Theorem {
            checked: pack(&[Sequent {
                premise: p.clone(),
                conclusion: q.clone(),
            }])
            .unwrap(),
        };
        let backward = Theorem {
            checked: pack(&[Sequent {
                premise: q.clone(),
                conclusion: p.clone(),
            }])
            .unwrap(),
        };
        let target = Theorem::identity(Formula::And {
            negative: false,
            children: vec![p],
        })
        .unwrap();
        let rewritten = target
            .rewrite_equivalent(
                &FormulaPath::new(0, Side::Left, vec![0]),
                &forward,
                &backward,
            )
            .unwrap();
        let table = rewritten.checked.decode_sequents().unwrap();
        assert!(matches!(&table[0].premise, Formula::And { children, .. } if children == &vec![q]));
    }

    #[test]
    fn model_witness_is_checked_before_sat_authority() {
        let p = literal(1);
        let not_q = literal(2).negated();
        let witness = ModelWitness::check(vec![p.clone(), not_q.clone()], [1]).unwrap();
        let theorem = Theorem::prove_sat(&witness).unwrap();
        let table = theorem.checked.decode_sequents().unwrap();
        assert_eq!(
            table[0],
            Sequent {
                premise: Formula::And {
                    negative: false,
                    children: Vec::new()
                },
                conclusion: Formula::Sat {
                    negative: false,
                    children: vec![p.clone(), not_q]
                },
            }
        );
        assert_eq!(
            ModelWitness::check(vec![p], []),
            Err(EditError::InvalidModel)
        );
        assert_eq!(
            ModelWitness::check(
                vec![Formula::Sat {
                    negative: false,
                    children: Vec::new()
                }],
                [],
            ),
            Err(EditError::NestedSat)
        );
    }

    #[test]
    fn public_mutation_builds_deep_formulas_without_recursion() {
        let mut deep = literal(1);
        for _ in 0..20_000 {
            deep = Formula::And {
                negative: false,
                children: vec![deep],
            };
        }
        let mut theorem = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: Vec::new(),
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: Vec::new(),
                },
            }])
            .unwrap(),
        };
        theorem.weaken_mut(0, Side::Left, &deep).unwrap();
        assert_eq!(theorem.checked.view(0).unwrap().premise.len(), 1);
        let clone = deep.clone();
        assert_eq!(deep, clone);
        let mut digest = std::collections::hash_map::DefaultHasher::new();
        deep.hash(&mut digest);
        std::hint::black_box(digest.finish());
        let identity = Theorem::identity(deep).unwrap();
        assert_eq!(identity.checked.len(), 1);
    }
}
