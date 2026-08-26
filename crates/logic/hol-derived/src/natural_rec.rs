//! Primitive recursion derived from the userspace inductive-graph schema.
//!
//! This module knows the logical shape of `NatRecGraph`, but knows nothing
//! about its source language.  A caller supplies ordinary checked rows for the
//! two type parameters and the open schema.  Every specialization and proof
//! step is then checked by [`Kernel`].

use covalence_logic_hol::{Kernel, Ref, SynFactId, SynRel, Tag, ThmId, TmTag, builtin::Op2};

use crate::{NaturalError, Naturals, forall_elim, join_same_syntax, substitute};

/// A specialized recursion graph and the introduction laws proved so far.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRecGraph {
    /// Binary predicate `nat → codomain → bool`.
    pub graph: Ref,
    /// `graph zero base`.
    pub base: Ref,
    /// Exact premise-free theorem `⊢ graph zero base`.
    pub base_theorem: ThmId,
    /// `∀n y. graph n y → graph (succ n) (step n y)`.
    pub step: Ref,
    /// Exact premise-free theorem `⊢ step`.
    pub step_theorem: ThmId,
    /// `∀n. ∃y. graph n y` in the kernel's equality/choice encoding.
    pub total: Ref,
    /// Exact premise-free theorem `⊢ total`.
    pub total_theorem: ThmId,
    /// Structural zero/successor shape predicate used for graph inversion.
    pub shape: Ref,
    /// `∀n y. graph n y → shape n y`.
    pub has_shape: Ref,
    /// Exact premise-free theorem `⊢ has_shape`.
    pub has_shape_theorem: ThmId,
}

/// Userspace primitive-recursion construction over a checked kernel.
pub trait NaturalRecExt {
    /// Specializes the open `NatRecGraph` schema and proves its base law.
    ///
    /// The schema is supplied as checked syntax rather than imported from the
    /// S-expression crate. Consequently this derived layer and the kernel are
    /// independent of parsing, names, and source-language representation.
    ///
    /// # Errors
    ///
    /// Returns an error unless the parameters name the two free types in the
    /// supplied schema, the specialized arguments have the expected checked
    /// types, the schema has the documented inductive-graph shape, and every
    /// checked substitution and Gentzen step succeeds.
    #[allow(clippy::too_many_arguments)]
    fn natural_rec_graph_from_schema(
        &mut self,
        naturals: &Naturals,
        natural_parameter: Ref,
        codomain_parameter: Ref,
        graph_schema: Ref,
        codomain: Ref,
        base: Ref,
        step: Ref,
    ) -> Result<NaturalRecGraph, NaturalError>;
}

impl NaturalRecExt for Kernel {
    fn natural_rec_graph_from_schema(
        &mut self,
        naturals: &Naturals,
        natural_parameter: Ref,
        codomain_parameter: Ref,
        graph_schema: Ref,
        codomain: Ref,
        base: Ref,
        step: Ref,
    ) -> Result<NaturalRecGraph, NaturalError> {
        let natural = substitute(self, natural_parameter, naturals.ty, graph_schema)?.output;
        let specialized = substitute(self, codomain_parameter, codomain, natural)?.output;
        let graph = instantiate_lambdas(
            self,
            specialized,
            &[naturals.zero, naturals.succ, base, step],
        )?;
        let (base_proposition, base_theorem) = prove_graph_base(self, graph, naturals.zero, base)?;
        let (step_proposition, step_theorem) =
            prove_graph_step(self, graph, naturals.succ, step, codomain)?;
        let (total, total_theorem) = prove_graph_total(
            self,
            naturals,
            graph,
            base,
            step,
            base_theorem,
            step_theorem,
            codomain,
        )?;
        let (shape, has_shape, has_shape_theorem) = prove_graph_has_shape(
            self,
            naturals,
            graph,
            base,
            step,
            base_theorem,
            step_theorem,
            codomain,
        )?;
        Ok(NaturalRecGraph {
            graph,
            base: base_proposition,
            base_theorem,
            step: step_proposition,
            step_theorem,
            total,
            total_theorem,
            shape,
            has_shape,
            has_shape_theorem,
        })
    }
}

fn instantiate_lambdas(
    kernel: &mut Kernel,
    mut function: Ref,
    arguments: &[Ref],
) -> Result<Ref, NaturalError> {
    for &argument in arguments {
        let [binder, body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
        let expected = kernel.classifier(binder)?;
        let actual = kernel.classifier(argument)?;
        join_same_syntax(kernel, expected, actual)?;
        function = substitute(kernel, binder, argument, body)?.output;
    }
    Ok(function)
}

fn prove_graph_base(
    kernel: &mut Kernel,
    graph: Ref,
    zero: Ref,
    base: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let (graph_base, universal) = expand_graph_application(kernel, graph, zero, base)?;

    let [_bool_ty, predicate_function, truth_function] =
        exact_children(kernel, universal, Tag::Tm(TmTag::Eq))?;
    let [relation, implication] = exact_children(kernel, predicate_function, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth_function, Tag::Tm(TmTag::Lam))?;
    if truth_binder != relation || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the recursion graph relation universal",
        });
    }
    let [premises, consequence] = exact_op2(kernel, implication, Op2::Imp)?;
    let [base_case, closure] = exact_op2(kernel, premises, Op2::And)?;
    join_same_syntax(kernel, base_case, consequence)?;
    let theorem = kernel.identity(positive(base_case))?;
    kernel.convert_conclusions(theorem, base_case, consequence)?;
    kernel.weaken(theorem, &[positive(closure)], &[])?;
    let theorem = kernel.and_left(theorem, positive(premises))?;
    let theorem = kernel.imp_right(theorem, positive(implication))?;
    let theorem = kernel.forall_intro_at(theorem, relation, universal)?;
    kernel.convert_theorem(theorem, universal, graph_base)?;
    Ok((graph_base, theorem))
}

#[allow(clippy::too_many_lines)]
fn prove_graph_step(
    kernel: &mut Kernel,
    graph: Ref,
    successor: Ref,
    recursion_step: Ref,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let natural_type = kernel
        .arena()
        .children(kernel.classifier(successor)?)
        .and_then(|mut children| children.next())
        .ok_or(NaturalError::WrongForm {
            expected: "the natural successor type",
        })?;
    let natural = kernel.tm_fv(kernel.fresh_name(&[graph, successor])?, natural_type)?;
    let value = kernel.tm_fv(kernel.fresh_name(&[natural])?, codomain)?;
    let graph_at_value = apply2(kernel, graph, natural, value)?;
    let next_natural = kernel.app(successor, natural)?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let next_value = kernel.app(step_at_natural, value)?;
    let graph_at_next = apply2(kernel, graph, next_natural, next_value)?;
    let implication = kernel.op2(Op2::Imp, graph_at_value, graph_at_next)?;

    let (expanded_next_application, expanded_next) =
        expand_graph_application(kernel, graph, next_natural, next_value)?;
    join_same_syntax(kernel, expanded_next_application, graph_at_next)?;
    let [_bool_ty, predicate_function, truth_function] =
        exact_children(kernel, expanded_next, Tag::Tm(TmTag::Eq))?;
    let [relation, target_implication] =
        exact_children(kernel, predicate_function, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth_function, Tag::Tm(TmTag::Lam))?;
    if truth_binder != relation || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the recursion graph relation universal",
        });
    }
    let [target_premises, target_consequence] = exact_op2(kernel, target_implication, Op2::Imp)?;

    let assumed_graph = kernel.identity(positive(graph_at_value))?;
    let (expanded_value_application, expanded_value) =
        expand_graph_application(kernel, graph, natural, value)?;
    join_same_syntax(kernel, expanded_value_application, graph_at_value)?;
    kernel.convert_conclusions(assumed_graph, graph_at_value, expanded_value)?;
    let specialized =
        forall_elim(kernel, assumed_graph, relation).map_err(|_| NaturalError::WrongForm {
            expected: "the recursion graph specialized at a relation",
        })?;
    let [source_premises, relation_at_value] =
        exact_op2(kernel, specialized.proposition, Op2::Imp)?;
    join_same_syntax(kernel, source_premises, target_premises)?;
    let premises_theorem = kernel.identity(positive(target_premises))?;
    kernel.convert_conclusions(premises_theorem, target_premises, source_premises)?;
    let relation_at_value_theorem = modus_ponens(
        kernel,
        specialized.theorem,
        premises_theorem,
        specialized.proposition,
    )?;

    let closure_theorem = project_and_right(kernel, target_premises)?;
    let closure_at_natural =
        forall_elim(kernel, closure_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "the recursion graph closure at a natural",
        })?;
    let closure_at_value =
        forall_elim(kernel, closure_at_natural.theorem, value).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the recursion graph closure at a value",
            }
        })?;
    let [closure_source, closure_target] =
        exact_op2(kernel, closure_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, relation_at_value, closure_source)?;
    join_same_syntax(kernel, closure_target, target_consequence)?;
    kernel.convert_conclusions(relation_at_value_theorem, relation_at_value, closure_source)?;
    let target_theorem = modus_ponens(
        kernel,
        closure_at_value.theorem,
        relation_at_value_theorem,
        closure_at_value.proposition,
    )?;
    kernel.convert_conclusions(target_theorem, closure_target, target_consequence)?;
    kernel.contract_theorem(target_theorem)?;
    let relation_theorem = kernel.imp_right(target_theorem, positive(target_implication))?;
    kernel.contract_theorem(relation_theorem)?;
    let universal_theorem = kernel.forall_intro_at(relation_theorem, relation, expanded_next)?;
    kernel.convert_theorem(universal_theorem, expanded_next, graph_at_next)?;
    let implication_theorem = kernel.imp_right(universal_theorem, positive(implication))?;
    let value_universal = kernel.forall_intro(implication_theorem, value)?;
    let natural_universal = kernel.forall_intro(value_universal.theorem, natural)?;
    Ok((natural_universal.universal, natural_universal.theorem))
}

#[derive(Clone, Copy)]
struct ShapePredicates {
    shape: Ref,
    guarded: Ref,
}

#[derive(Clone, Copy)]
struct GuardedGraphUse {
    natural: Ref,
    value: Ref,
    graph_at: Ref,
    expanded_graph: Ref,
    theorem: ThmId,
    proposition: Ref,
    premises: Ref,
    base: Ref,
    step: Ref,
    guarded_at: Ref,
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_graph_has_shape(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    base: Ref,
    recursion_step: Ref,
    graph_base_theorem: ThmId,
    graph_step_theorem: ThmId,
    codomain: Ref,
) -> Result<(Ref, Ref, ThmId), NaturalError> {
    let predicates =
        build_shape_predicates(kernel, naturals, graph, base, recursion_step, codomain)?;
    let graph_use =
        guarded_graph_targets(kernel, graph, predicates.guarded, naturals.ty, codomain)?;
    let (guarded_base, guarded_base_theorem) =
        prove_guarded_shape_base(kernel, predicates, naturals.zero, base, graph_base_theorem)?;
    join_same_syntax(kernel, guarded_base, graph_use.base)?;
    kernel.convert_conclusions(guarded_base_theorem, guarded_base, graph_use.base)?;
    let (guarded_step, guarded_step_theorem) = prove_guarded_shape_step(
        kernel,
        naturals,
        predicates,
        recursion_step,
        graph_step_theorem,
        graph_use.step,
    )?;
    let (has_shape, has_shape_theorem) = specialize_graph_to_guarded_shape(
        kernel,
        predicates,
        graph_use,
        guarded_base_theorem,
        guarded_step,
        guarded_step_theorem,
    )?;
    Ok((predicates.shape, has_shape, has_shape_theorem))
}

fn guarded_graph_targets(
    kernel: &mut Kernel,
    graph: Ref,
    guarded: Ref,
    natural_type: Ref,
    codomain: Ref,
) -> Result<GuardedGraphUse, NaturalError> {
    let natural = kernel.tm_fv(kernel.fresh_name(&[graph, guarded])?, natural_type)?;
    let value = kernel.tm_fv(kernel.fresh_name(&[natural])?, codomain)?;
    let graph_at = apply2(kernel, graph, natural, value)?;
    let theorem = kernel.identity(positive(graph_at))?;
    let (application, expanded) = expand_graph_application(kernel, graph, natural, value)?;
    join_same_syntax(kernel, graph_at, application)?;
    kernel.convert_conclusions(theorem, graph_at, expanded)?;
    let [_bool, function, _truth] = exact_children(kernel, expanded, Tag::Tm(TmTag::Eq))?;
    let [relation, _body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let expected = kernel.classifier(relation)?;
    let actual = kernel.classifier(guarded)?;
    join_same_syntax(kernel, expected, actual)?;
    let specialized =
        forall_elim(kernel, theorem, guarded).map_err(|_| NaturalError::WrongForm {
            expected: "the graph guarded-shape premises",
        })?;
    let [premises, guarded_at] = exact_op2(kernel, specialized.proposition, Op2::Imp)?;
    let [base, step] = exact_op2(kernel, premises, Op2::And)?;
    Ok(GuardedGraphUse {
        natural,
        value,
        graph_at,
        expanded_graph: expanded,
        theorem: specialized.theorem,
        proposition: specialized.proposition,
        premises,
        base,
        step,
        guarded_at,
    })
}

fn build_shape_predicates(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    base: Ref,
    recursion_step: Ref,
    codomain: Ref,
) -> Result<ShapePredicates, NaturalError> {
    let natural = kernel.tm_fv(kernel.fresh_name(&[graph, base])?, naturals.ty)?;
    let value = kernel.tm_fv(kernel.fresh_name(&[natural])?, codomain)?;
    let graph_at_value = apply2(kernel, graph, natural, value)?;
    let bool_ty = kernel.classifier(graph_at_value)?;
    let at_zero = kernel.eq(bool_ty, natural, naturals.zero)?;
    let at_base = kernel.eq(bool_ty, value, base)?;
    let base_case = kernel.op2(Op2::And, at_zero, at_base)?;

    let predecessor = kernel.tm_fv(kernel.fresh_name(&[value])?, naturals.ty)?;
    let predecessor_value = kernel.tm_fv(kernel.fresh_name(&[predecessor])?, codomain)?;
    let predecessor_graph = apply2(kernel, graph, predecessor, predecessor_value)?;
    let successor_predecessor = kernel.app(naturals.succ, predecessor)?;
    let successor_index = kernel.eq(bool_ty, natural, successor_predecessor)?;
    let step_at_predecessor = kernel.app(recursion_step, predecessor)?;
    let successor_value = kernel.app(step_at_predecessor, predecessor_value)?;
    let step_value = kernel.eq(bool_ty, value, successor_value)?;
    let equalities = kernel.op2(Op2::And, successor_index, step_value)?;
    let successor_data = kernel.op2(Op2::And, predecessor_graph, equalities)?;
    let has_value = kernel.exists_tm(predecessor_value, successor_data)?;
    let successor_case = kernel.exists_tm(predecessor, has_value)?;
    let shape_body = kernel.op2(Op2::Or, base_case, successor_case)?;
    let at_value = kernel.lam(value, shape_body)?;
    let shape = kernel.lam(natural, at_value)?;

    let probe_natural = kernel.tm_fv(kernel.fresh_name(&[shape])?, naturals.ty)?;
    let probe_value = kernel.tm_fv(kernel.fresh_name(&[probe_natural])?, codomain)?;
    let (_probe, expanded_graph) =
        expand_graph_application(kernel, graph, probe_natural, probe_value)?;
    let [_graph_bool, graph_function, _graph_truth] =
        exact_children(kernel, expanded_graph, Tag::Tm(TmTag::Eq))?;
    let [graph_relation, _graph_body] =
        exact_children(kernel, graph_function, Tag::Tm(TmTag::Lam))?;
    let relation_type = kernel.classifier(graph_relation)?;
    let [guarded_natural_type, guarded_value_function] = exact_children(
        kernel,
        relation_type,
        Tag::Ty(covalence_logic_hol::TyTag::Arr),
    )?;
    let [guarded_codomain, _guarded_bool] = exact_children(
        kernel,
        guarded_value_function,
        Tag::Ty(covalence_logic_hol::TyTag::Arr),
    )?;
    join_same_syntax(kernel, guarded_natural_type, naturals.ty)?;
    join_same_syntax(kernel, guarded_codomain, codomain)?;
    let guarded_natural = kernel.tm_fv(kernel.fresh_name(&[shape])?, guarded_natural_type)?;
    let guarded_value = kernel.tm_fv(kernel.fresh_name(&[guarded_natural])?, guarded_codomain)?;
    let graph_at = apply2(kernel, graph, guarded_natural, guarded_value)?;
    let shape_at = apply2(kernel, shape, guarded_natural, guarded_value)?;
    let guarded_body = kernel.op2(Op2::And, graph_at, shape_at)?;
    let guarded_at_value = kernel.lam_at(guarded_value_function, guarded_value, guarded_body)?;
    let guarded = kernel.lam_at(relation_type, guarded_natural, guarded_at_value)?;
    Ok(ShapePredicates { shape, guarded })
}

fn prove_guarded_shape_base(
    kernel: &mut Kernel,
    predicates: ShapePredicates,
    zero: Ref,
    base: Ref,
    graph_base_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let (shape_at_base, shape_body) =
        expand_graph_application(kernel, predicates.shape, zero, base)?;
    let [base_case, successor_case] = exact_op2(kernel, shape_body, Op2::Or)?;
    let [zero_equality, base_equality] = exact_op2(kernel, base_case, Op2::And)?;
    let bool_ty = kernel.classifier(zero_equality)?;
    let zero_refl = kernel.refl(bool_ty, zero)?;
    join_same_syntax(kernel, zero_refl.equality, zero_equality)?;
    kernel.convert_conclusions(zero_refl.theorem, zero_refl.equality, zero_equality)?;
    let base_refl = kernel.refl(bool_ty, base)?;
    join_same_syntax(kernel, base_refl.equality, base_equality)?;
    kernel.convert_conclusions(base_refl.theorem, base_refl.equality, base_equality)?;
    let base_case_theorem =
        kernel.and_right(zero_refl.theorem, base_refl.theorem, positive(base_case))?;
    kernel.weaken(base_case_theorem, &[], &[positive(successor_case)])?;
    let shape_theorem = kernel.or_right(base_case_theorem, positive(shape_body))?;
    kernel.convert_conclusions(shape_theorem, shape_body, shape_at_base)?;

    let (guarded_base, guarded_body) =
        expand_graph_application(kernel, predicates.guarded, zero, base)?;
    let [guarded_graph, guarded_shape] = exact_op2(kernel, guarded_body, Op2::And)?;
    let graph_theorem = kernel.copy_theorem(graph_base_theorem)?;
    let graph_conclusion = sole_conclusion(kernel, graph_theorem)?;
    join_same_syntax(kernel, graph_conclusion, guarded_graph)?;
    join_same_syntax(kernel, shape_at_base, guarded_shape)?;
    kernel.convert_conclusions(graph_theorem, graph_conclusion, guarded_graph)?;
    kernel.convert_conclusions(shape_theorem, shape_at_base, guarded_shape)?;
    let theorem = kernel.and_right(graph_theorem, shape_theorem, positive(guarded_body))?;
    kernel.convert_conclusions(theorem, guarded_body, guarded_base)?;
    Ok((guarded_base, theorem))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_guarded_shape_step(
    kernel: &mut Kernel,
    naturals: &Naturals,
    predicates: ShapePredicates,
    recursion_step: Ref,
    graph_step_theorem: ThmId,
    target_step: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let [_outer_bool, outer_function, outer_truth] =
        exact_children(kernel, target_step, Tag::Tm(TmTag::Eq))?;
    let [natural, inner_universal] = exact_children(kernel, outer_function, Tag::Tm(TmTag::Lam))?;
    let [outer_truth_binder, outer_truth_body] =
        exact_children(kernel, outer_truth, Tag::Tm(TmTag::Lam))?;
    if outer_truth_binder != natural || kernel.arena().bool_value(outer_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the guarded graph outer closure universal",
        });
    }
    let [_inner_bool, inner_function, inner_truth] =
        exact_children(kernel, inner_universal, Tag::Tm(TmTag::Eq))?;
    let [value, implication] = exact_children(kernel, inner_function, Tag::Tm(TmTag::Lam))?;
    let [inner_truth_binder, inner_truth_body] =
        exact_children(kernel, inner_truth, Tag::Tm(TmTag::Lam))?;
    if inner_truth_binder != value || kernel.arena().bool_value(inner_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the guarded graph inner closure universal",
        });
    }
    let [guarded_at, guarded_next] = exact_op2(kernel, implication, Op2::Imp)?;
    let next_natural = kernel.app(naturals.succ, natural)?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let next_value = kernel.app(step_at_natural, value)?;

    let (expanded_at_application, expanded_at) =
        expand_graph_application(kernel, predicates.guarded, natural, value)?;
    join_same_syntax(kernel, guarded_at, expanded_at_application)?;
    let [source_graph, _source_shape] = exact_op2(kernel, expanded_at, Op2::And)?;
    let graph_theorem = project_and_left(kernel, expanded_at)?;

    let graph_step_at_natural =
        forall_elim(kernel, graph_step_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "the graph shape closure at a natural",
        })?;
    let graph_step_at_value =
        forall_elim(kernel, graph_step_at_natural.theorem, value).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the graph shape closure at a value",
            }
        })?;
    let [step_source, step_target] = exact_op2(kernel, graph_step_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, source_graph, step_source)?;
    kernel.convert_conclusions(graph_theorem, source_graph, step_source)?;
    let next_graph = modus_ponens(
        kernel,
        graph_step_at_value.theorem,
        graph_theorem,
        graph_step_at_value.proposition,
    )?;

    let shape_source = project_and_left(kernel, expanded_at)?;
    let shape_next = prove_successor_shape(
        kernel,
        predicates.shape,
        natural,
        value,
        next_natural,
        next_value,
        source_graph,
        shape_source,
    )?;
    let (expanded_next_application, expanded_next) =
        expand_graph_application(kernel, predicates.guarded, next_natural, next_value)?;
    join_same_syntax(kernel, guarded_next, expanded_next_application)?;
    let [target_graph, target_shape] = exact_op2(kernel, expanded_next, Op2::And)?;
    join_same_syntax(kernel, step_target, target_graph)?;
    let shape_conclusion = sole_conclusion(kernel, shape_next)?;
    join_same_syntax(kernel, shape_conclusion, target_shape)?;
    kernel.convert_conclusions(next_graph, step_target, target_graph)?;
    kernel.convert_conclusions(shape_next, shape_conclusion, target_shape)?;
    let next = kernel.and_right(next_graph, shape_next, positive(expanded_next))?;
    kernel.convert_conclusions(next, expanded_next, guarded_next)?;
    kernel.convert_theorem(next, expanded_at, guarded_at)?;
    kernel.contract_theorem(next)?;
    let implication_theorem = kernel.imp_right(next, positive(implication))?;
    let at_value = kernel.forall_intro_at(implication_theorem, value, inner_universal)?;
    let generalized = kernel.forall_intro_at(at_value, natural, target_step)?;
    Ok((target_step, generalized))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_successor_shape(
    kernel: &mut Kernel,
    shape: Ref,
    predecessor: Ref,
    predecessor_value: Ref,
    successor: Ref,
    successor_value: Ref,
    graph_at_predecessor: Ref,
    graph_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let (shape_application, shape_body) =
        expand_graph_application(kernel, shape, successor, successor_value)?;
    let [base_case, successor_case] = exact_op2(kernel, shape_body, Op2::Or)?;
    let [predecessor_predicate, _predecessor_choice] =
        exact_children(kernel, successor_case, Tag::Tm(TmTag::App))?;
    let (outer_witness_application, inner_exists, outer_beta) =
        beta_apply(kernel, predecessor_predicate, predecessor)?;
    kernel.union_syn_fact(outer_beta)?;
    let [value_predicate, _value_choice] =
        exact_children(kernel, inner_exists, Tag::Tm(TmTag::App))?;
    let (inner_witness_application, successor_data, inner_beta) =
        beta_apply(kernel, value_predicate, predecessor_value)?;
    kernel.union_syn_fact(inner_beta)?;
    let [target_graph, equalities] = exact_op2(kernel, successor_data, Op2::And)?;
    let [index_equality, value_equality] = exact_op2(kernel, equalities, Op2::And)?;
    let bool_ty = kernel.classifier(index_equality)?;

    join_same_syntax(kernel, graph_at_predecessor, target_graph)?;
    kernel.convert_conclusions(graph_theorem, graph_at_predecessor, target_graph)?;
    let index_refl = kernel.refl(bool_ty, successor)?;
    join_same_syntax(kernel, index_refl.equality, index_equality)?;
    kernel.convert_conclusions(index_refl.theorem, index_refl.equality, index_equality)?;
    let value_refl = kernel.refl(bool_ty, successor_value)?;
    join_same_syntax(kernel, value_refl.equality, value_equality)?;
    kernel.convert_conclusions(value_refl.theorem, value_refl.equality, value_equality)?;
    let equalities_theorem =
        kernel.and_right(index_refl.theorem, value_refl.theorem, positive(equalities))?;
    let data_theorem =
        kernel.and_right(graph_theorem, equalities_theorem, positive(successor_data))?;
    kernel.convert_conclusions(data_theorem, successor_data, inner_witness_application)?;
    let inner_theorem = kernel.choice_intro_at(data_theorem, inner_exists)?;
    kernel.convert_conclusions(inner_theorem, inner_exists, outer_witness_application)?;
    let outer_theorem = kernel.choice_intro_at(inner_theorem, successor_case)?;
    kernel.weaken(outer_theorem, &[], &[positive(base_case)])?;
    let shape_theorem = kernel.or_right(outer_theorem, positive(shape_body))?;
    kernel.convert_conclusions(shape_theorem, shape_body, shape_application)?;
    Ok(shape_theorem)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn specialize_graph_to_guarded_shape(
    kernel: &mut Kernel,
    predicates: ShapePredicates,
    graph_use: GuardedGraphUse,
    guarded_base_theorem: ThmId,
    guarded_step: Ref,
    guarded_step_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    join_same_syntax(kernel, guarded_step, graph_use.step)?;
    let base_theorem = kernel.copy_theorem(guarded_base_theorem)?;
    let step_theorem = kernel.copy_theorem(guarded_step_theorem)?;
    kernel.convert_conclusions(step_theorem, guarded_step, graph_use.step)?;
    let premises_theorem =
        kernel.and_right(base_theorem, step_theorem, positive(graph_use.premises))?;
    let guarded_theorem = modus_ponens(
        kernel,
        graph_use.theorem,
        premises_theorem,
        graph_use.proposition,
    )?;

    let (expanded_guarded_application, expanded_guarded) = expand_graph_application(
        kernel,
        predicates.guarded,
        graph_use.natural,
        graph_use.value,
    )?;
    join_same_syntax(kernel, graph_use.guarded_at, expanded_guarded_application)?;
    kernel.convert_conclusions(guarded_theorem, graph_use.guarded_at, expanded_guarded)?;
    let [_guarded_graph, guarded_shape] = exact_op2(kernel, expanded_guarded, Op2::And)?;
    let shape_projection = project_and_right(kernel, expanded_guarded)?;
    let shape_theorem = kernel.cut(
        guarded_theorem,
        shape_projection,
        positive(expanded_guarded),
    )?;
    let shape_at = apply2(kernel, predicates.shape, graph_use.natural, graph_use.value)?;
    join_same_syntax(kernel, guarded_shape, shape_at)?;
    kernel.convert_conclusions(shape_theorem, guarded_shape, shape_at)?;
    kernel.convert_theorem(shape_theorem, graph_use.expanded_graph, graph_use.graph_at)?;
    let implication = kernel.op2(Op2::Imp, graph_use.graph_at, shape_at)?;
    let implication_theorem = kernel.imp_right(shape_theorem, positive(implication))?;
    kernel.contract_theorem(implication_theorem)?;
    let at_value = kernel.forall_intro(implication_theorem, graph_use.value)?;
    let generalized = kernel.forall_intro(at_value.theorem, graph_use.natural)?;
    Ok((generalized.universal, generalized.theorem))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_graph_total(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    base: Ref,
    recursion_step: Ref,
    graph_base_theorem: ThmId,
    graph_step_theorem: ThmId,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let predicate_natural =
        kernel.tm_fv(kernel.fresh_name(&[graph, recursion_step])?, naturals.ty)?;
    let value = kernel.tm_fv(kernel.fresh_name(&[predicate_natural])?, codomain)?;
    let graph_at_value = apply2(kernel, graph, predicate_natural, value)?;
    let exists_value = kernel.exists_tm(value, graph_at_value)?;
    let total_predicate = kernel.lam(predicate_natural, exists_value)?;

    let [_induction_bool, induction_function, _induction_truth] =
        exact_children(kernel, naturals.induction, Tag::Tm(TmTag::Eq))?;
    let [induction_predicate, _induction_body] =
        exact_children(kernel, induction_function, Tag::Tm(TmTag::Lam))?;
    let expected_predicate_type = kernel.classifier(induction_predicate)?;
    let actual_predicate_type = kernel.classifier(total_predicate)?;
    join_same_syntax(kernel, expected_predicate_type, actual_predicate_type)?;
    let induction_at_predicate = forall_elim(kernel, naturals.induction_theorem, total_predicate)
        .map_err(|_| NaturalError::WrongForm {
        expected: "natural induction at graph totality",
    })?;
    let [induction_premises, induction_total] =
        exact_op2(kernel, induction_at_predicate.proposition, Op2::Imp)?;
    let [induction_base, induction_step] = exact_op2(kernel, induction_premises, Op2::And)?;

    let (at_zero, expanded_zero, zero_beta) = beta_apply(kernel, total_predicate, naturals.zero)?;
    kernel.union_syn_fact(zero_beta)?;
    let [zero_predicate, _zero_choice] =
        exact_children(kernel, expanded_zero, Tag::Tm(TmTag::App))?;
    let zero_witness = kernel.app(zero_predicate, base)?;
    let (zero_witness_application, zero_graph, zero_witness_beta) =
        beta_apply(kernel, zero_predicate, base)?;
    join_same_syntax(kernel, zero_witness, zero_witness_application)?;
    kernel.union_syn_fact(zero_witness_beta)?;
    let base_theorem = kernel.copy_theorem(graph_base_theorem)?;
    let base_conclusion = sole_conclusion(kernel, base_theorem)?;
    join_same_syntax(kernel, base_conclusion, zero_graph)?;
    kernel.convert_conclusions(base_theorem, base_conclusion, zero_graph)?;
    kernel.convert_conclusions(base_theorem, zero_graph, zero_witness)?;
    let zero_exists = kernel.choice_intro_at(base_theorem, expanded_zero)?;
    kernel.convert_conclusions(zero_exists, expanded_zero, at_zero)?;
    join_same_syntax(kernel, at_zero, induction_base)?;
    kernel.convert_conclusions(zero_exists, at_zero, induction_base)?;

    let [_step_bool, step_function, step_truth] =
        exact_children(kernel, induction_step, Tag::Tm(TmTag::Eq))?;
    let [natural, step_implication] = exact_children(kernel, step_function, Tag::Tm(TmTag::Lam))?;
    let [step_truth_binder, step_truth_body] =
        exact_children(kernel, step_truth, Tag::Tm(TmTag::Lam))?;
    if step_truth_binder != natural || kernel.arena().bool_value(step_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the totality induction step universal",
        });
    }
    let [at_natural, at_next] = exact_op2(kernel, step_implication, Op2::Imp)?;
    let next_natural = kernel.app(naturals.succ, natural)?;
    let assumed = kernel.identity(positive(at_natural))?;
    let (at_natural_application, expanded_at_natural, at_natural_beta) =
        beta_apply(kernel, total_predicate, natural)?;
    join_same_syntax(kernel, at_natural, at_natural_application)?;
    kernel.union_syn_fact(at_natural_beta)?;
    kernel.convert_conclusions(assumed, at_natural, expanded_at_natural)?;
    let [predecessor_predicate, predecessor_choice] =
        exact_children(kernel, expanded_at_natural, Tag::Tm(TmTag::App))?;
    let (choice_application, graph_at_choice, choice_beta) =
        beta_apply(kernel, predecessor_predicate, predecessor_choice)?;
    join_same_syntax(kernel, choice_application, expanded_at_natural)?;
    kernel.union_syn_fact(choice_beta)?;
    kernel.convert_conclusions(assumed, expanded_at_natural, graph_at_choice)?;

    let graph_step_at_natural =
        forall_elim(kernel, graph_step_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "the graph step theorem at a natural",
        })?;
    let graph_step_at_choice =
        forall_elim(kernel, graph_step_at_natural.theorem, predecessor_choice).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the graph step theorem at its chosen value",
            }
        })?;
    let [step_source, step_target] = exact_op2(kernel, graph_step_at_choice.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_at_choice, step_source)?;
    kernel.convert_conclusions(assumed, graph_at_choice, step_source)?;
    let next_graph = modus_ponens(
        kernel,
        graph_step_at_choice.theorem,
        assumed,
        graph_step_at_choice.proposition,
    )?;

    let (at_next_application, expanded_at_next, at_next_beta) =
        beta_apply(kernel, total_predicate, next_natural)?;
    join_same_syntax(kernel, at_next, at_next_application)?;
    kernel.union_syn_fact(at_next_beta)?;
    let [successor_predicate, _successor_choice] =
        exact_children(kernel, expanded_at_next, Tag::Tm(TmTag::App))?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let next_value = kernel.app(step_at_natural, predecessor_choice)?;
    let witness_application = kernel.app(successor_predicate, next_value)?;
    let (witness_beta_application, witness_graph, witness_beta) =
        beta_apply(kernel, successor_predicate, next_value)?;
    join_same_syntax(kernel, witness_application, witness_beta_application)?;
    kernel.union_syn_fact(witness_beta)?;
    join_same_syntax(kernel, step_target, witness_graph)?;
    kernel.convert_conclusions(next_graph, step_target, witness_graph)?;
    kernel.convert_conclusions(next_graph, witness_graph, witness_application)?;
    let successor_exists = kernel.choice_intro_at(next_graph, expanded_at_next)?;
    kernel.convert_conclusions(successor_exists, expanded_at_next, at_next)?;
    let total_step = kernel.imp_right(successor_exists, positive(step_implication))?;
    let total_step = kernel.forall_intro_at(total_step, natural, induction_step)?;
    let premises = kernel.and_right(zero_exists, total_step, positive(induction_premises))?;
    let total = modus_ponens(
        kernel,
        induction_at_predicate.theorem,
        premises,
        induction_at_predicate.proposition,
    )?;
    Ok((induction_total, total))
}

fn expand_graph_application(
    kernel: &mut Kernel,
    graph: Ref,
    natural: Ref,
    value: Ref,
) -> Result<(Ref, Ref), NaturalError> {
    let (at_natural, after_natural, natural_beta) = beta_apply(kernel, graph, natural)?;
    let (expanded_application, expanded, value_beta) = beta_apply(kernel, after_natural, value)?;
    let application = kernel.app(at_natural, value)?;
    let argument = kernel.syn_refl(None, SynRel::Syn, value)?;
    let lifted = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        application,
        expanded_application,
        &[natural_beta, argument],
    )?;
    let beta = kernel.syn_trans(None, lifted, value_beta)?;
    kernel.union_syn_fact(beta)?;
    Ok((application, expanded))
}

fn apply2(kernel: &mut Kernel, function: Ref, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
    let at_left = kernel.app(function, left)?;
    Ok(kernel.app(at_left, right)?)
}

fn modus_ponens(
    kernel: &mut Kernel,
    implication_theorem: ThmId,
    antecedent_theorem: ThmId,
    implication: Ref,
) -> Result<ThmId, NaturalError> {
    let [_antecedent, consequent] = exact_op2(kernel, implication, Op2::Imp)?;
    let consequence = kernel.identity(positive(consequent))?;
    let use_implication =
        kernel.imp_left(antecedent_theorem, consequence, positive(implication))?;
    Ok(kernel.cut(implication_theorem, use_implication, positive(implication))?)
}

fn project_and_right(kernel: &mut Kernel, conjunction: Ref) -> Result<ThmId, NaturalError> {
    let [left, right] = exact_op2(kernel, conjunction, Op2::And)?;
    let theorem = kernel.identity(positive(right))?;
    kernel.weaken(theorem, &[positive(left)], &[])?;
    Ok(kernel.and_left(theorem, positive(conjunction))?)
}

fn project_and_left(kernel: &mut Kernel, conjunction: Ref) -> Result<ThmId, NaturalError> {
    let [left, right] = exact_op2(kernel, conjunction, Op2::And)?;
    let theorem = kernel.identity(positive(left))?;
    kernel.weaken(theorem, &[positive(right)], &[])?;
    Ok(kernel.and_left(theorem, positive(conjunction))?)
}

fn beta_apply(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<(Ref, Ref, SynFactId), NaturalError> {
    let application = kernel.app(function, argument)?;
    let [binder, body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let substitution = substitute(kernel, binder, argument, body)?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    Ok((application, substitution.output, beta))
}

fn positive(reference: Ref) -> covalence_logic_hol::Lit {
    covalence_logic_hol::Lit::positive(reference.get())
}

fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, NaturalError> {
    let theorem = kernel.thm().get(theorem).ok_or(NaturalError::WrongForm {
        expected: "a resident graph theorem",
    })?;
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(NaturalError::WrongForm {
        expected: "one graph theorem conclusion",
    })?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(NaturalError::WrongForm {
            expected: "one positive graph theorem conclusion",
        });
    }
    Ref::new(
        i32::try_from(row[0].magnitude()).map_err(|_| NaturalError::WrongForm {
            expected: "a local graph proposition",
        })?,
    )
    .ok_or(NaturalError::WrongForm {
        expected: "a nonzero graph proposition",
    })
}

fn exact_op2(kernel: &Kernel, reference: Ref, op: Op2) -> Result<[Ref; 2], NaturalError> {
    if kernel.arena().op2(reference) != Some(op) {
        return Err(NaturalError::WrongForm {
            expected: "a compact logical opcode",
        });
    }
    exact_children(kernel, reference, Tag::Tm(TmTag::Op2))
}

fn exact_children<const N: usize>(
    kernel: &Kernel,
    reference: Ref,
    tag: Tag,
) -> Result<[Ref; N], NaturalError> {
    if kernel.arena().tag(reference) != Some(tag) {
        return Err(NaturalError::WrongForm {
            expected: "the recursion graph schema shape",
        });
    }
    kernel
        .arena()
        .children(reference)
        .ok_or(NaturalError::WrongForm {
            expected: "the recursion graph schema children",
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| NaturalError::WrongForm {
            expected: "the recursion graph schema arity",
        })
}
