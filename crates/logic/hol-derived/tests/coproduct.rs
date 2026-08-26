use covalence_logic_hol::{AX_SUB, Kernel, Sort};
use covalence_logic_hol_derived::{
    CoproductCandidate, CoproductCandidateLaws, CoproductExt, forall_elim, join_same_syntax,
};

#[test]
fn guarded_coproduct_has_checked_carrier_type_and_injections() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();

    let coproduct = kernel.coproduct(bool_ty, bool_ty, right).unwrap();

    assert_eq!(kernel.category(coproduct.ty).unwrap(), Sort::Ty);
    assert_eq!(kernel.classifier(coproduct.inl).unwrap(), coproduct.inl_ty);
    assert_eq!(kernel.classifier(coproduct.inr).unwrap(), coproduct.inr_ty);
    assert_eq!(coproduct.subtype.sub, coproduct.ty);
    assert!(coproduct.subtype.theorem().is_some());
}

#[test]
fn coproduct_terms_need_no_capability_and_failure_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();

    let terms = kernel.coproduct_terms(bool_ty, bool_ty, bool_ty).unwrap();
    assert!(terms.subtype.theorem().is_none());

    let truth = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().clone();
    assert!(kernel.coproduct(bool_ty, truth, bool_ty).is_err());
    assert_eq!(*kernel.arena(), before);
}

#[test]
fn eliminator_is_checked_at_each_requested_codomain() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let codomain = kernel.ty_arr(bool_ty, bool_ty).unwrap();

    let eliminator = coproduct.eliminator(&mut kernel, codomain).unwrap();

    assert_eq!(
        kernel.classifier(eliminator.function).unwrap(),
        eliminator.function_ty
    );
    let left = kernel.tm_fv(100, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(101, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(102, coproduct.ty).unwrap();
    let applied = kernel.app(eliminator.function, left).unwrap();
    let applied = kernel.app(applied, right).unwrap();
    let applied = kernel.app(applied, value).unwrap();
    assert_eq!(kernel.classifier(applied).unwrap(), codomain);
}

#[test]
fn left_computation_is_an_exact_premise_free_theorem() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(200, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(201, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(202, coproduct.left).unwrap();
    let injected = kernel.app(coproduct.inl, value).unwrap();
    let direct = kernel.app(eliminator.function, left).unwrap();
    let direct = kernel.app(direct, right).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(left, value).unwrap();
    let expected_proposition = kernel.eq(bool_ty, direct, expected).unwrap();

    let computation = coproduct
        .prove_case_inl(&mut kernel, eliminator, left, right, value)
        .unwrap();

    let theorem = kernel.thm().get(computation.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    let rows = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0],
        &[covalence_logic_hol::Lit::positive(
            computation.proposition.get()
        )]
    );
    join_same_syntax(&mut kernel, computation.proposition, expected_proposition).unwrap();
}

#[test]
fn right_computation_is_an_exact_premise_free_theorem() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(300, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(301, eliminator.right_map_ty).unwrap();
    let value = kernel.tm_fv(302, coproduct.right).unwrap();
    let injected = kernel.app(coproduct.inr, value).unwrap();
    let direct = kernel.app(eliminator.function, left).unwrap();
    let direct = kernel.app(direct, right).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(right, value).unwrap();
    let expected_proposition = kernel.eq(bool_ty, direct, expected).unwrap();

    let computation = coproduct
        .prove_case_inr(&mut kernel, eliminator, left, right, value)
        .unwrap();

    let theorem = kernel.thm().get(computation.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    let rows = theorem.rhs.rows().collect::<Vec<_>>();
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0],
        &[covalence_logic_hol::Lit::positive(
            computation.proposition.get()
        )]
    );
    join_same_syntax(&mut kernel, computation.proposition, expected_proposition).unwrap();
}

#[test]
fn computation_rejection_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, bool_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, bool_ty).unwrap();
    let left = kernel.tm_fv(400, eliminator.left_map_ty).unwrap();
    let right = kernel.tm_fv(401, eliminator.right_map_ty).unwrap();
    let wrong_value = kernel.tm_fv(402, eliminator.left_map_ty).unwrap();
    let before = kernel.arena().clone();

    assert!(
        coproduct
            .prove_case_inl(&mut kernel, eliminator, left, right, wrong_value)
            .is_err()
    );
    assert_eq!(*kernel.arena(), before);
}

#[test]
fn mediator_laws_are_universal_and_premise_free() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let codomain = right_ty;
    let eliminator = coproduct.eliminator(&mut kernel, codomain).unwrap();
    let left_map = kernel.tm_fv(500, eliminator.left_map_ty).unwrap();
    let right_map = kernel.tm_fv(501, eliminator.right_map_ty).unwrap();

    let laws = coproduct
        .prove_case_laws(&mut kernel, eliminator, left_map, right_map)
        .unwrap();

    let theorem = kernel.thm().get(laws.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[covalence_logic_hol::Lit::positive(laws.conjunction.get())][..]]
    );

    let left_value = kernel.tm_fv(502, coproduct.left).unwrap();
    let specialized = forall_elim(&mut kernel, laws.left_theorem, left_value).unwrap();
    let injected = kernel.app(coproduct.inl, left_value).unwrap();
    let direct = kernel.app(laws.eliminator.function, left_map).unwrap();
    let direct = kernel.app(direct, right_map).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(left_map, left_value).unwrap();
    let expected = kernel.eq(bool_ty, direct, expected).unwrap();
    join_same_syntax(&mut kernel, specialized.proposition, expected).unwrap();

    let right_value = kernel.tm_fv(503, coproduct.right).unwrap();
    let specialized = forall_elim(&mut kernel, laws.right_theorem, right_value).unwrap();
    let injected = kernel.app(coproduct.inr, right_value).unwrap();
    let direct = kernel.app(laws.eliminator.function, left_map).unwrap();
    let direct = kernel.app(direct, right_map).unwrap();
    let direct = kernel.app(direct, injected).unwrap();
    let expected = kernel.app(right_map, right_value).unwrap();
    let expected = kernel.eq(bool_ty, direct, expected).unwrap();
    join_same_syntax(&mut kernel, specialized.proposition, expected).unwrap();
}

#[test]
fn every_coproduct_representation_is_in_an_injection_image() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();

    let exhaustive = coproduct.prove_exhaustiveness(&mut kernel).unwrap();

    for (theorem, proposition) in [
        (exhaustive.inhabited_theorem, exhaustive.inhabited),
        (exhaustive.theorem, exhaustive.image_of_rep),
    ] {
        let theorem = kernel.thm().get(theorem).unwrap();
        assert_eq!(theorem.lhs.rows().count(), 0);
        assert_eq!(
            theorem.rhs.rows().collect::<Vec<_>>(),
            vec![&[covalence_logic_hol::Lit::positive(proposition.get())][..]]
        );
    }

    let value = kernel.tm_fv(600, coproduct.ty).unwrap();
    let specialized = forall_elim(&mut kernel, exhaustive.theorem, value).unwrap();
    let represented = kernel.app(coproduct.subtype.rep, value).unwrap();
    let expected = kernel.app(coproduct.predicate, represented).unwrap();
    join_same_syntax(&mut kernel, specialized.proposition, expected).unwrap();

    let cases = coproduct.cases(&mut kernel, exhaustive, value).unwrap();
    let theorem = kernel.thm().get(cases.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[covalence_logic_hol::Lit::positive(cases.disjunction.get())][..]]
    );
    assert_eq!(
        kernel.arena().op2(cases.disjunction),
        Some(covalence_logic_hol::builtin::Op2::Or)
    );

    let opened = coproduct.open_cases(&mut kernel, cases).unwrap();
    for (branch, premise, injection, summand) in [
        (opened.left, cases.left, coproduct.inl, coproduct.left),
        (opened.right, cases.right, coproduct.inr, coproduct.right),
    ] {
        assert_eq!(kernel.classifier(branch.witness).unwrap(), summand);
        let expected_injected = kernel.app(injection, branch.witness).unwrap();
        join_same_syntax(&mut kernel, branch.injected, expected_injected).unwrap();
        let expected_equality = kernel.eq(bool_ty, value, expected_injected).unwrap();
        join_same_syntax(&mut kernel, branch.value_equality, expected_equality).unwrap();
        let theorem = kernel.thm().get(branch.theorem).unwrap();
        assert_eq!(
            theorem.lhs.rows().collect::<Vec<_>>(),
            vec![&[covalence_logic_hol::Lit::positive(premise.get())][..]]
        );
        assert_eq!(
            theorem.rhs.rows().collect::<Vec<_>>(),
            vec![
                &[covalence_logic_hol::Lit::positive(
                    branch.value_equality.get()
                )][..]
            ]
        );
    }
    let eliminated = coproduct
        .eliminate_cases(
            &mut kernel,
            cases,
            opened.left.theorem,
            opened.right.theorem,
        )
        .unwrap();
    let theorem = kernel.thm().get(eliminated).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    assert_eq!(theorem.rhs.rows().count(), 2);
}

#[test]
fn every_mediator_with_the_computation_laws_is_extensionally_unique() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let right_ty = kernel.ty_arr(bool_ty, bool_ty).unwrap();
    kernel.add_axiom(AX_SUB).unwrap();
    let coproduct = kernel.coproduct(bool_ty, bool_ty, right_ty).unwrap();
    let eliminator = coproduct.eliminator(&mut kernel, right_ty).unwrap();
    let left_map = kernel.tm_fv(700, eliminator.left_map_ty).unwrap();
    let right_map = kernel.tm_fv(701, eliminator.right_map_ty).unwrap();
    let laws = coproduct
        .prove_case_laws(&mut kernel, eliminator, left_map, right_map)
        .unwrap();
    let partial = kernel.app(eliminator.function, left_map).unwrap();
    let candidate_function = kernel.app(partial, right_map).unwrap();
    let candidate = CoproductCandidateLaws {
        function: candidate_function,
        left: laws.left,
        left_theorem: laws.left_theorem,
        right: laws.right,
        right_theorem: laws.right_theorem,
    };

    let before = kernel.arena().clone();
    let malformed = CoproductCandidateLaws {
        right: laws.left,
        right_theorem: laws.left_theorem,
        ..candidate
    };
    assert!(
        coproduct
            .prove_unique_mediator(&mut kernel, eliminator, left_map, right_map, malformed)
            .is_err()
    );
    assert_eq!(*kernel.arena(), before);

    let unique = coproduct
        .prove_unique_mediator(&mut kernel, eliminator, left_map, right_map, candidate)
        .unwrap();

    let theorem = kernel.thm().get(unique.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![&[covalence_logic_hol::Lit::positive(unique.equality.get())][..]]
    );
    let expected = kernel
        .eq(bool_ty, candidate_function, unique.canonical)
        .unwrap();
    join_same_syntax(&mut kernel, unique.equality, expected).unwrap();

    let arbitrary = kernel.tm_fv(702, eliminator.value_map_ty).unwrap();
    let left_value = kernel.tm_fv(703, coproduct.left).unwrap();
    let left_injected = kernel.app(coproduct.inl, left_value).unwrap();
    let arbitrary_left = kernel.app(arbitrary, left_injected).unwrap();
    let expected_left = kernel.app(left_map, left_value).unwrap();
    let left_law = kernel.eq(bool_ty, arbitrary_left, expected_left).unwrap();
    let left_law = kernel.forall_tm(bool_ty, left_value, left_law).unwrap();
    let right_value = kernel.tm_fv(704, coproduct.right).unwrap();
    let right_injected = kernel.app(coproduct.inr, right_value).unwrap();
    let arbitrary_right = kernel.app(arbitrary, right_injected).unwrap();
    let expected_right = kernel.app(right_map, right_value).unwrap();
    let right_law = kernel.eq(bool_ty, arbitrary_right, expected_right).unwrap();
    let right_law = kernel.forall_tm(bool_ty, right_value, right_law).unwrap();
    let universal = coproduct
        .prove_universal_mediator(
            &mut kernel,
            eliminator,
            left_map,
            right_map,
            CoproductCandidate {
                function: arbitrary,
                left: left_law,
                right: right_law,
            },
        )
        .unwrap();
    let theorem = kernel.thm().get(universal.theorem).unwrap();
    assert_eq!(theorem.lhs.rows().count(), 0);
    assert_eq!(
        theorem.rhs.rows().collect::<Vec<_>>(),
        vec![
            &[covalence_logic_hol::Lit::positive(
                universal.universal.get()
            )][..]
        ]
    );
}
