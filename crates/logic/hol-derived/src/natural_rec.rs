//! Primitive recursion derived from the userspace inductive-graph schema.
//!
//! This module knows the logical shape of `NatRecGraph`, but knows nothing
//! about its source language.  A caller supplies ordinary checked rows for the
//! two type parameters and the open schema.  Every specialization and proof
//! step is then checked by [`Kernel`].

use covalence_logic_hol::{Kernel, Ref, SynFactId, SynRel, Tag, ThmId, TmTag, builtin::Op2};

use crate::{
    NaturalError, Naturals, equality_symmetry, equality_transitivity, forall_elim,
    join_same_syntax, substitute,
};

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
    /// `∀y. graph zero y → y = base`.
    pub zero_value: Ref,
    /// Exact premise-free theorem `⊢ zero_value`.
    pub zero_value_theorem: ThmId,
    /// `∀n y. graph (succ n) y → ∃z. graph n z ∧ y = step n z`.
    pub successor_value: Ref,
    /// Exact premise-free theorem `⊢ successor_value`.
    pub successor_value_theorem: ThmId,
    /// `∀y z. graph zero y → graph zero z → y = z`.
    pub zero_functional: Ref,
    /// Exact premise-free theorem `⊢ zero_functional`.
    pub zero_functional_theorem: ThmId,
    /// `∀n y z. graph n y → graph n z → y = z`.
    pub functional: Ref,
    /// Exact premise-free theorem `⊢ functional`.
    pub functional_theorem: ThmId,
    /// Selected primitive recursor `nat → codomain`.
    pub rec: Ref,
    /// `∀n. graph n (rec n)`.
    pub rec_graph: Ref,
    /// Exact premise-free theorem `⊢ rec_graph`.
    pub rec_graph_theorem: ThmId,
    /// `rec zero = base`.
    pub rec_zero: Ref,
    /// Exact premise-free theorem `⊢ rec_zero`.
    pub rec_zero_theorem: ThmId,
    /// `∀n. rec (succ n) = step n (rec n)`.
    pub rec_successor: Ref,
    /// Exact premise-free theorem `⊢ rec_successor`.
    pub rec_successor_theorem: ThmId,
}

/// A selected primitive recursor together with its specification and universal
/// property, all derived from caller-supplied open syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRecursor {
    /// The total, functional graph from which the recursor was selected.
    pub graph: NaturalRecGraph,
    /// Specialized predicate `(nat → codomain) → bool` from `NatRecSpec`.
    pub specification_predicate: Ref,
    /// The zero/successor specification specialized to [`NaturalRecGraph::rec`].
    pub specification: Ref,
    /// Exact premise-free theorem `⊢ specification`.
    pub specification_theorem: ThmId,
    /// Every function satisfying the specification agrees pointwise with `rec`.
    pub unique: Ref,
    /// Exact premise-free theorem `⊢ unique`.
    pub unique_theorem: ThmId,
}

/// Checked roots of the two open recursion schemata and their independent
/// type-parameter rows.
///
/// Names remain userspace metadata: an S-expression compiler can assemble
/// this descriptor from its dictionary, while another frontend can supply the
/// same six checked rows without depending on that language.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalRecSchemas {
    /// Open `NatRecGraph` definition.
    pub graph: Ref,
    /// Natural-carrier parameter occurring in [`graph`](Self::graph).
    pub graph_natural: Ref,
    /// Codomain parameter occurring in [`graph`](Self::graph).
    pub graph_codomain: Ref,
    /// Open `NatRecSpec` definition.
    pub specification: Ref,
    /// Natural-carrier parameter occurring in [`specification`](Self::specification).
    pub specification_natural: Ref,
    /// Codomain parameter occurring in [`specification`](Self::specification).
    pub specification_codomain: Ref,
}

/// Userspace primitive-recursion construction over a checked kernel.
pub trait NaturalRecExt {
    /// Specializes the open `NatRecGraph` schema and derives its complete
    /// total, functional graph package plus the selected recursor laws.
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

    /// Builds the full primitive-recursion package from the independent open
    /// `NatRecGraph` and `NatRecSpec` schemata.
    ///
    /// # Errors
    ///
    /// Returns an error if either schema has the wrong checked shape or any
    /// userspace-derived proof step is rejected by the kernel.
    #[allow(clippy::too_many_arguments)]
    fn natural_rec_from_schemata(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
        codomain: Ref,
        base: Ref,
        step: Ref,
    ) -> Result<NaturalRecursor, NaturalError>;
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
        let (zero_value, zero_value_theorem) =
            prove_graph_zero_value(self, naturals, graph, shape, has_shape_theorem, codomain)?;
        let (successor_value, successor_value_theorem) = prove_graph_successor_value(
            self,
            naturals,
            graph,
            shape,
            has_shape_theorem,
            step,
            codomain,
        )?;
        let (zero_functional, zero_functional_theorem) =
            prove_zero_functionality(self, naturals, graph, zero_value_theorem, codomain)?;
        let (functional, functional_theorem) = prove_graph_functionality(
            self,
            naturals,
            graph,
            step,
            successor_value_theorem,
            zero_functional_theorem,
            codomain,
        )?;
        let (rec, rec_graph, rec_graph_theorem) =
            select_graph_function(self, naturals, graph, total, total_theorem)?;
        let (rec_zero, rec_zero_theorem) =
            prove_rec_zero(self, naturals, rec, rec_graph_theorem, zero_value_theorem)?;
        let (rec_successor, rec_successor_theorem) = prove_rec_successor(
            self,
            naturals,
            rec,
            step,
            rec_graph_theorem,
            step_theorem,
            functional_theorem,
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
            zero_value,
            zero_value_theorem,
            successor_value,
            successor_value_theorem,
            zero_functional,
            zero_functional_theorem,
            functional,
            functional_theorem,
            rec,
            rec_graph,
            rec_graph_theorem,
            rec_zero,
            rec_zero_theorem,
            rec_successor,
            rec_successor_theorem,
        })
    }

    fn natural_rec_from_schemata(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
        codomain: Ref,
        base: Ref,
        step: Ref,
    ) -> Result<NaturalRecursor, NaturalError> {
        let graph = self.natural_rec_graph_from_schema(
            naturals,
            schemas.graph_natural,
            schemas.graph_codomain,
            schemas.graph,
            codomain,
            base,
            step,
        )?;
        let natural = substitute(
            self,
            schemas.specification_natural,
            naturals.ty,
            schemas.specification,
        )?
        .output;
        let specialized =
            substitute(self, schemas.specification_codomain, codomain, natural)?.output;
        let specification_predicate = instantiate_lambdas(
            self,
            specialized,
            &[naturals.zero, naturals.succ, base, step],
        )?;
        let (specification, specification_theorem) =
            prove_rec_specification(self, specification_predicate, &graph)?;
        let (unique, unique_theorem) = prove_rec_uniqueness(
            self,
            naturals,
            specification_predicate,
            &graph,
            base,
            step,
            codomain,
        )?;
        Ok(NaturalRecursor {
            graph,
            specification_predicate,
            specification,
            specification_theorem,
            unique,
            unique_theorem,
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
    let natural = kernel.tm_fv(fresh_global_name(kernel)?, natural_type)?;
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
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
    let natural = kernel.tm_fv(fresh_global_name(kernel)?, natural_type)?;
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
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
    let natural = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let graph_at_value = apply2(kernel, graph, natural, value)?;
    let bool_ty = kernel.classifier(graph_at_value)?;
    let at_zero = kernel.eq(bool_ty, natural, naturals.zero)?;
    let at_base = kernel.eq(bool_ty, value, base)?;
    let base_case = kernel.op2(Op2::And, at_zero, at_base)?;

    let predecessor = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let predecessor_value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
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

    let probe_natural = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let probe_value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
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
    let guarded_natural = kernel.tm_fv(fresh_global_name(kernel)?, guarded_natural_type)?;
    let guarded_value = kernel.tm_fv(fresh_global_name(kernel)?, guarded_codomain)?;
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
fn prove_graph_zero_value(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    shape: Ref,
    has_shape_theorem: ThmId,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let graph_at_zero = apply2(kernel, graph, naturals.zero, value)?;
    let shape_at_zero = apply2(kernel, shape, naturals.zero, value)?;
    let assumed = kernel.identity(positive(graph_at_zero))?;
    let shape_at_index = forall_elim(kernel, has_shape_theorem, naturals.zero).map_err(|_| {
        NaturalError::WrongForm {
            expected: "graph shape inversion at zero",
        }
    })?;
    let shape_at_value = forall_elim(kernel, shape_at_index.theorem, value).map_err(|_| {
        NaturalError::WrongForm {
            expected: "graph shape inversion at the zero value",
        }
    })?;
    let [shape_source, shape_target] = exact_op2(kernel, shape_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_at_zero, shape_source)?;
    join_same_syntax(kernel, shape_at_zero, shape_target)?;
    kernel.convert_conclusions(assumed, graph_at_zero, shape_source)?;
    let shape_theorem = modus_ponens(
        kernel,
        shape_at_value.theorem,
        assumed,
        shape_at_value.proposition,
    )?;
    kernel.convert_conclusions(shape_theorem, shape_target, shape_at_zero)?;
    let (shape_application, shape_body) =
        expand_graph_application(kernel, shape, naturals.zero, value)?;
    join_same_syntax(kernel, shape_at_zero, shape_application)?;
    kernel.convert_conclusions(shape_theorem, shape_at_zero, shape_body)?;
    let [base_case, successor_case] = exact_op2(kernel, shape_body, Op2::Or)?;
    let [_zero_equality, value_equality] = exact_op2(kernel, base_case, Op2::And)?;
    let base_branch = project_and_right(kernel, base_case)?;

    let successor_branch =
        successor_shape_contradiction(kernel, naturals, successor_case, positive(value_equality))?;
    let cases = kernel.or_left(base_branch, successor_branch, positive(shape_body))?;
    let value_theorem = kernel.cut(shape_theorem, cases, positive(shape_body))?;
    kernel.contract_theorem(value_theorem)?;
    let implication = kernel.op2(Op2::Imp, graph_at_zero, value_equality)?;
    let implication_theorem = kernel.imp_right(value_theorem, positive(implication))?;
    let generalized = kernel.forall_intro(implication_theorem, value)?;
    Ok((generalized.universal, generalized.theorem))
}

fn successor_shape_contradiction(
    kernel: &mut Kernel,
    naturals: &Naturals,
    successor_case: Ref,
    conclusion: covalence_logic_hol::Lit,
) -> Result<ThmId, NaturalError> {
    let [predecessor_predicate, predecessor] =
        exact_children(kernel, successor_case, Tag::Tm(TmTag::App))?;
    let (outer_application, inner_exists, outer_beta) =
        beta_apply(kernel, predecessor_predicate, predecessor)?;
    join_same_syntax(kernel, successor_case, outer_application)?;
    kernel.union_syn_fact(outer_beta)?;
    let [value_predicate, predecessor_value] =
        exact_children(kernel, inner_exists, Tag::Tm(TmTag::App))?;
    let (inner_application, successor_data, inner_beta) =
        beta_apply(kernel, value_predicate, predecessor_value)?;
    join_same_syntax(kernel, inner_exists, inner_application)?;
    kernel.union_syn_fact(inner_beta)?;
    let [_predecessor_graph, equalities] = exact_op2(kernel, successor_data, Op2::And)?;
    let [zero_is_successor, _value_equality] = exact_op2(kernel, equalities, Op2::And)?;

    let equalities_theorem = project_and_right(kernel, successor_data)?;
    let index_theorem = project_and_left(kernel, equalities)?;
    let index_theorem = kernel.cut(equalities_theorem, index_theorem, positive(equalities))?;
    kernel.convert_theorem(index_theorem, successor_data, successor_case)?;

    let separation =
        forall_elim(kernel, naturals.zero_ne_succ_theorem, predecessor).map_err(|_| {
            NaturalError::WrongForm {
                expected: "zero-successor separation at the shape predecessor",
            }
        })?;
    let [separated_equality] = exact_op1(
        kernel,
        separation.proposition,
        covalence_logic_hol::builtin::Op1::Not,
    )?;
    join_same_syntax(kernel, zero_is_successor, separated_equality)?;
    kernel.convert_conclusions(index_theorem, zero_is_successor, separated_equality)?;
    let negative =
        kernel.expand_conclusion(separation.theorem, positive(separation.proposition), None)?;
    let contradiction = kernel.resolve(index_theorem, negative, positive(separated_equality))?;
    kernel.weaken(contradiction, &[], &[conclusion])?;
    Ok(contradiction)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_graph_successor_value(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    shape: Ref,
    has_shape_theorem: ThmId,
    recursion_step: Ref,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let natural = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let witness = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let successor = kernel.app(naturals.succ, natural)?;
    let graph_at_successor = apply2(kernel, graph, successor, value)?;
    let graph_at_witness = apply2(kernel, graph, natural, witness)?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let expected_value = kernel.app(step_at_natural, witness)?;
    let bool_ty = kernel.classifier(graph_at_successor)?;
    let value_equality = kernel.eq(bool_ty, value, expected_value)?;
    let witness_body = kernel.op2(Op2::And, graph_at_witness, value_equality)?;
    let exists_witness = kernel.exists_tm(witness, witness_body)?;
    let implication = kernel.op2(Op2::Imp, graph_at_successor, exists_witness)?;

    let shape_at_successor = apply2(kernel, shape, successor, value)?;
    let assumed = kernel.identity(positive(graph_at_successor))?;
    let shape_at_index =
        forall_elim(kernel, has_shape_theorem, successor).map_err(|_| NaturalError::WrongForm {
            expected: "graph shape inversion at a successor",
        })?;
    let shape_at_value = forall_elim(kernel, shape_at_index.theorem, value).map_err(|_| {
        NaturalError::WrongForm {
            expected: "graph shape inversion at a successor value",
        }
    })?;
    let [shape_source, shape_target] = exact_op2(kernel, shape_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_at_successor, shape_source)?;
    join_same_syntax(kernel, shape_at_successor, shape_target)?;
    kernel.convert_conclusions(assumed, graph_at_successor, shape_source)?;
    let shape_theorem = modus_ponens(
        kernel,
        shape_at_value.theorem,
        assumed,
        shape_at_value.proposition,
    )?;
    kernel.convert_conclusions(shape_theorem, shape_target, shape_at_successor)?;
    let (shape_application, shape_body) =
        expand_graph_application(kernel, shape, successor, value)?;
    join_same_syntax(kernel, shape_at_successor, shape_application)?;
    kernel.convert_conclusions(shape_theorem, shape_at_successor, shape_body)?;
    let [base_case, successor_case] = exact_op2(kernel, shape_body, Op2::Or)?;

    let base_branch = successor_base_contradiction(
        kernel,
        naturals,
        natural,
        base_case,
        positive(exists_witness),
    )?;
    let successor_branch = successor_shape_witness(
        kernel,
        naturals,
        graph,
        recursion_step,
        natural,
        value,
        successor_case,
        exists_witness,
        bool_ty,
    )?;
    let cases = kernel.or_left(base_branch, successor_branch, positive(shape_body))?;
    let witness_theorem = kernel.cut(shape_theorem, cases, positive(shape_body))?;
    kernel.contract_theorem(witness_theorem)?;
    let implication_theorem = kernel.imp_right(witness_theorem, positive(implication))?;
    let at_value = kernel.forall_intro(implication_theorem, value)?;
    let generalized = kernel.forall_intro(at_value.theorem, natural)?;
    Ok((generalized.universal, generalized.theorem))
}

fn successor_base_contradiction(
    kernel: &mut Kernel,
    naturals: &Naturals,
    natural: Ref,
    base_case: Ref,
    conclusion: covalence_logic_hol::Lit,
) -> Result<ThmId, NaturalError> {
    let [successor_is_zero, _value_is_base] = exact_op2(kernel, base_case, Op2::And)?;
    let successor_equality = project_and_left(kernel, base_case)?;
    let bool_ty = kernel.classifier(successor_is_zero)?;
    let reversed = equality_symmetry(kernel, bool_ty, successor_equality)?;
    let separation = forall_elim(kernel, naturals.zero_ne_succ_theorem, natural).map_err(|_| {
        NaturalError::WrongForm {
            expected: "zero-successor separation at the inverted successor",
        }
    })?;
    let [separated_equality] = exact_op1(
        kernel,
        separation.proposition,
        covalence_logic_hol::builtin::Op1::Not,
    )?;
    join_same_syntax(kernel, reversed.equality, separated_equality)?;
    kernel.convert_conclusions(reversed.theorem, reversed.equality, separated_equality)?;
    let negative =
        kernel.expand_conclusion(separation.theorem, positive(separation.proposition), None)?;
    let contradiction = kernel.resolve(reversed.theorem, negative, positive(separated_equality))?;
    kernel.weaken(contradiction, &[], &[conclusion])?;
    Ok(contradiction)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn successor_shape_witness(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    recursion_step: Ref,
    natural: Ref,
    value: Ref,
    successor_case: Ref,
    target_exists: Ref,
    bool_ty: Ref,
) -> Result<ThmId, NaturalError> {
    let [predecessor_predicate, predecessor] =
        exact_children(kernel, successor_case, Tag::Tm(TmTag::App))?;
    let (outer_application, inner_exists, outer_beta) =
        beta_apply(kernel, predecessor_predicate, predecessor)?;
    join_same_syntax(kernel, successor_case, outer_application)?;
    kernel.union_syn_fact(outer_beta)?;
    let [value_predicate, predecessor_value] =
        exact_children(kernel, inner_exists, Tag::Tm(TmTag::App))?;
    let (inner_application, successor_data, inner_beta) =
        beta_apply(kernel, value_predicate, predecessor_value)?;
    join_same_syntax(kernel, inner_exists, inner_application)?;
    kernel.union_syn_fact(inner_beta)?;
    let [predecessor_graph, equalities] = exact_op2(kernel, successor_data, Op2::And)?;
    let [successor_equality, predecessor_value_equality] = exact_op2(kernel, equalities, Op2::And)?;

    let graph_data = project_and_left(kernel, successor_data)?;
    let equalities_data = project_and_right(kernel, successor_data)?;
    let successor_data_theorem = project_and_left(kernel, equalities)?;
    let successor_data_theorem = kernel.cut(
        equalities_data,
        successor_data_theorem,
        positive(equalities),
    )?;
    let value_data_theorem = project_and_right(kernel, equalities)?;
    let value_data_theorem =
        kernel.cut(equalities_data, value_data_theorem, positive(equalities))?;

    let injective_at_natural = forall_elim(kernel, naturals.succ_injective_theorem, natural)
        .map_err(|_| NaturalError::WrongForm {
            expected: "successor injectivity at the target predecessor",
        })?;
    let injective_at_predecessor = forall_elim(kernel, injective_at_natural.theorem, predecessor)
        .map_err(|_| NaturalError::WrongForm {
        expected: "successor injectivity at the shape predecessor",
    })?;
    let [injective_source, _index_equality] =
        exact_op2(kernel, injective_at_predecessor.proposition, Op2::Imp)?;
    join_same_syntax(kernel, successor_equality, injective_source)?;
    kernel.convert_conclusions(successor_data_theorem, successor_equality, injective_source)?;
    let equal_predecessors = modus_ponens(
        kernel,
        injective_at_predecessor.theorem,
        successor_data_theorem,
        injective_at_predecessor.proposition,
    )?;

    let graph_binder = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let graph_body = apply2(kernel, graph, graph_binder, predecessor_value)?;
    let graph_predicate = kernel.lam(graph_binder, graph_body)?;
    let target_graph = apply2(kernel, graph, natural, predecessor_value)?;
    let transported_graph = transport_right_to_left(
        kernel,
        bool_ty,
        equal_predecessors,
        graph_predicate,
        target_graph,
        predecessor_graph,
        graph_data,
    )?;

    let value_binder = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let step_at_binder = kernel.app(recursion_step, value_binder)?;
    let stepped_value = kernel.app(step_at_binder, predecessor_value)?;
    let equality_body = kernel.eq(bool_ty, value, stepped_value)?;
    let equality_predicate = kernel.lam(value_binder, equality_body)?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let target_step_value = kernel.app(step_at_natural, predecessor_value)?;
    let target_value_equality = kernel.eq(bool_ty, value, target_step_value)?;
    let transported_value = transport_right_to_left(
        kernel,
        bool_ty,
        equal_predecessors,
        equality_predicate,
        target_value_equality,
        predecessor_value_equality,
        value_data_theorem,
    )?;

    let [target_predicate, _target_choice] =
        exact_children(kernel, target_exists, Tag::Tm(TmTag::App))?;
    let (witness_application, target_body, witness_beta) =
        beta_apply(kernel, target_predicate, predecessor_value)?;
    kernel.union_syn_fact(witness_beta)?;
    let [target_graph_body, target_value_body] = exact_op2(kernel, target_body, Op2::And)?;
    join_same_syntax(kernel, target_graph, target_graph_body)?;
    join_same_syntax(kernel, target_value_equality, target_value_body)?;
    kernel.convert_conclusions(transported_graph, target_graph, target_graph_body)?;
    kernel.convert_conclusions(transported_value, target_value_equality, target_value_body)?;
    let body_theorem =
        kernel.and_right(transported_graph, transported_value, positive(target_body))?;
    kernel.contract_theorem(body_theorem)?;
    kernel.convert_conclusions(body_theorem, target_body, witness_application)?;
    let witness_theorem = kernel.choice_intro_at(body_theorem, target_exists)?;
    kernel.convert_theorem(witness_theorem, successor_data, successor_case)?;
    Ok(witness_theorem)
}

#[allow(clippy::too_many_arguments)]
fn transport_right_to_left(
    kernel: &mut Kernel,
    bool_ty: Ref,
    index_equality: ThmId,
    predicate: Ref,
    left_target: Ref,
    right_source: Ref,
    source_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let index = sole_conclusion(kernel, index_equality)?;
    let [_domain, left, right] = exact_children(kernel, index, Tag::Tm(TmTag::Eq))?;
    let lifted = kernel.ap_term(index_equality, predicate)?;
    let (left_application, left_output, left_beta) = beta_apply(kernel, predicate, left)?;
    let (right_application, right_output, right_beta) = beta_apply(kernel, predicate, right)?;
    join_same_syntax(kernel, lifted.left, left_application)?;
    join_same_syntax(kernel, lifted.right, right_application)?;
    join_same_syntax(kernel, left_output, left_target)?;
    join_same_syntax(kernel, right_output, right_source)?;
    kernel.union_syn_fact(left_beta)?;
    kernel.union_syn_fact(right_beta)?;
    let source = kernel.copy_theorem(source_theorem)?;
    kernel.convert_conclusions(source, right_source, lifted.right)?;
    let reversed = equality_symmetry(kernel, bool_ty, lifted.theorem)?;
    let result = kernel.eq_mp(reversed.theorem, source)?;
    kernel.convert_conclusions(result, lifted.left, left_target)?;
    Ok(result)
}

fn prove_zero_functionality(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    zero_value_theorem: ThmId,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let left = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let right = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let graph_left = apply2(kernel, graph, naturals.zero, left)?;
    let graph_right = apply2(kernel, graph, naturals.zero, right)?;
    let bool_ty = kernel.classifier(graph_left)?;
    let equality = kernel.eq(bool_ty, left, right)?;
    let inner_implication = kernel.op2(Op2::Imp, graph_right, equality)?;
    let outer_implication = kernel.op2(Op2::Imp, graph_left, inner_implication)?;

    let left_assumption = kernel.identity(positive(graph_left))?;
    let right_assumption = kernel.identity(positive(graph_right))?;
    let zero_at_left =
        forall_elim(kernel, zero_value_theorem, left).map_err(|_| NaturalError::WrongForm {
            expected: "zero graph inversion at the left value",
        })?;
    let zero_at_right =
        forall_elim(kernel, zero_value_theorem, right).map_err(|_| NaturalError::WrongForm {
            expected: "zero graph inversion at the right value",
        })?;
    let [left_source, _left_equality] = exact_op2(kernel, zero_at_left.proposition, Op2::Imp)?;
    let [right_source, _right_equality] = exact_op2(kernel, zero_at_right.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_left, left_source)?;
    join_same_syntax(kernel, graph_right, right_source)?;
    kernel.convert_conclusions(left_assumption, graph_left, left_source)?;
    kernel.convert_conclusions(right_assumption, graph_right, right_source)?;
    let left_to_base = modus_ponens(
        kernel,
        zero_at_left.theorem,
        left_assumption,
        zero_at_left.proposition,
    )?;
    let right_to_base = modus_ponens(
        kernel,
        zero_at_right.theorem,
        right_assumption,
        zero_at_right.proposition,
    )?;
    let base_to_right = equality_symmetry(kernel, bool_ty, right_to_base)?;
    let result = equality_transitivity(kernel, bool_ty, left_to_base, base_to_right.theorem)?;
    join_same_syntax(kernel, result.equality, equality)?;
    kernel.convert_conclusions(result.theorem, result.equality, equality)?;
    let inner = kernel.imp_right(result.theorem, positive(inner_implication))?;
    let outer = kernel.imp_right(inner, positive(outer_implication))?;
    let at_right = kernel.forall_intro(outer, right)?;
    let generalized = kernel.forall_intro(at_right.theorem, left)?;
    Ok((generalized.universal, generalized.theorem))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_graph_functionality(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    recursion_step: Ref,
    successor_value_theorem: ThmId,
    zero_functional_theorem: ThmId,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let index = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let left = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let right = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
    let graph_left = apply2(kernel, graph, index, left)?;
    let graph_right = apply2(kernel, graph, index, right)?;
    let bool_ty = kernel.classifier(graph_left)?;
    let equality = kernel.eq(bool_ty, left, right)?;
    let inner_implication = kernel.op2(Op2::Imp, graph_right, equality)?;
    let outer_implication = kernel.op2(Op2::Imp, graph_left, inner_implication)?;
    let at_right = kernel.forall_tm(bool_ty, right, outer_implication)?;
    let at_left = kernel.forall_tm(bool_ty, left, at_right)?;
    let predicate = kernel.lam(index, at_left)?;

    let [_induction_bool, induction_function, _induction_truth] =
        exact_children(kernel, naturals.induction, Tag::Tm(TmTag::Eq))?;
    let [induction_predicate, _induction_body] =
        exact_children(kernel, induction_function, Tag::Tm(TmTag::Lam))?;
    join_same_syntax(
        kernel,
        kernel.classifier(induction_predicate)?,
        kernel.classifier(predicate)?,
    )?;
    let induction = forall_elim(kernel, naturals.induction_theorem, predicate).map_err(|_| {
        NaturalError::WrongForm {
            expected: "natural induction at graph functionality",
        }
    })?;
    let [premises, conclusion] = exact_op2(kernel, induction.proposition, Op2::Imp)?;
    let [base_target, step_target] = exact_op2(kernel, premises, Op2::And)?;
    let base_theorem = prove_functionality_base_at(
        kernel,
        predicate,
        naturals.zero,
        base_target,
        zero_functional_theorem,
    )?;
    let step_theorem = prove_functionality_step_at(
        kernel,
        naturals,
        predicate,
        recursion_step,
        successor_value_theorem,
        step_target,
        bool_ty,
    )?;
    let premises_theorem = kernel.and_right(base_theorem, step_theorem, positive(premises))?;
    let theorem = modus_ponens(
        kernel,
        induction.theorem,
        premises_theorem,
        induction.proposition,
    )?;
    Ok((conclusion, theorem))
}

fn prove_functionality_base_at(
    kernel: &mut Kernel,
    predicate: Ref,
    zero: Ref,
    target: Ref,
    zero_functional_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let (application, expanded, beta) = beta_apply(kernel, predicate, zero)?;
    join_same_syntax(kernel, target, application)?;
    kernel.union_syn_fact(beta)?;
    let [_outer_bool, outer_function, outer_truth] =
        exact_children(kernel, expanded, Tag::Tm(TmTag::Eq))?;
    let [left, inner_universal] = exact_children(kernel, outer_function, Tag::Tm(TmTag::Lam))?;
    let [outer_truth_binder, outer_truth_body] =
        exact_children(kernel, outer_truth, Tag::Tm(TmTag::Lam))?;
    if outer_truth_binder != left || kernel.arena().bool_value(outer_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the outer zero-functionality universal",
        });
    }
    let [_inner_bool, inner_function, inner_truth] =
        exact_children(kernel, inner_universal, Tag::Tm(TmTag::Eq))?;
    let [right, body] = exact_children(kernel, inner_function, Tag::Tm(TmTag::Lam))?;
    let [inner_truth_binder, inner_truth_body] =
        exact_children(kernel, inner_truth, Tag::Tm(TmTag::Lam))?;
    if inner_truth_binder != right || kernel.arena().bool_value(inner_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the inner zero-functionality universal",
        });
    }
    join_universal_argument_type(kernel, zero_functional_theorem, left)?;
    let at_left = forall_elim(kernel, zero_functional_theorem, left)?;
    join_universal_argument_type(kernel, at_left.theorem, right)?;
    let at_right = forall_elim(kernel, at_left.theorem, right)?;
    join_same_syntax(kernel, at_right.proposition, body)?;
    kernel.convert_conclusions(at_right.theorem, at_right.proposition, body)?;
    let inner = kernel.forall_intro_at(at_right.theorem, right, inner_universal)?;
    let outer = kernel.forall_intro_at(inner, left, expanded)?;
    kernel.convert_conclusions(outer, expanded, target)?;
    Ok(outer)
}

fn join_universal_argument_type(
    kernel: &mut Kernel,
    theorem: ThmId,
    argument: Ref,
) -> Result<(), NaturalError> {
    let universal = sole_conclusion(kernel, theorem)?;
    let [_bool_ty, function, _truth] = exact_children(kernel, universal, Tag::Tm(TmTag::Eq))?;
    let [binder, _body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let expected = kernel.classifier(binder)?;
    let actual = kernel.classifier(argument)?;
    join_same_syntax(kernel, expected, actual)?;
    Ok(())
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_functionality_step_at(
    kernel: &mut Kernel,
    naturals: &Naturals,
    predicate: Ref,
    recursion_step: Ref,
    successor_value_theorem: ThmId,
    target: Ref,
    bool_ty: Ref,
) -> Result<ThmId, NaturalError> {
    let [_step_bool, step_function, step_truth] =
        exact_children(kernel, target, Tag::Tm(TmTag::Eq))?;
    let [natural, step_implication] = exact_children(kernel, step_function, Tag::Tm(TmTag::Lam))?;
    let [step_truth_binder, step_truth_body] =
        exact_children(kernel, step_truth, Tag::Tm(TmTag::Lam))?;
    if step_truth_binder != natural || kernel.arena().bool_value(step_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the graph-functionality induction step universal",
        });
    }
    let [property_at_natural, property_at_successor] =
        exact_op2(kernel, step_implication, Op2::Imp)?;
    let property_assumption = kernel.identity(positive(property_at_natural))?;
    let (natural_application, expanded_natural, natural_beta) =
        beta_apply(kernel, predicate, natural)?;
    join_same_syntax(kernel, property_at_natural, natural_application)?;
    kernel.union_syn_fact(natural_beta)?;
    kernel.convert_conclusions(property_assumption, property_at_natural, expanded_natural)?;

    let successor = kernel.app(naturals.succ, natural)?;
    let (successor_application, expanded_successor, successor_beta) =
        beta_apply(kernel, predicate, successor)?;
    join_same_syntax(kernel, property_at_successor, successor_application)?;
    kernel.union_syn_fact(successor_beta)?;
    let [_outer_bool, outer_function, outer_truth] =
        exact_children(kernel, expanded_successor, Tag::Tm(TmTag::Eq))?;
    let [left, inner_universal] = exact_children(kernel, outer_function, Tag::Tm(TmTag::Lam))?;
    let [outer_truth_binder, outer_truth_body] =
        exact_children(kernel, outer_truth, Tag::Tm(TmTag::Lam))?;
    if outer_truth_binder != left || kernel.arena().bool_value(outer_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the outer successor-functionality universal",
        });
    }
    let [_inner_bool, inner_function, inner_truth] =
        exact_children(kernel, inner_universal, Tag::Tm(TmTag::Eq))?;
    let [right, functionality_body] = exact_children(kernel, inner_function, Tag::Tm(TmTag::Lam))?;
    let [inner_truth_binder, inner_truth_body] =
        exact_children(kernel, inner_truth, Tag::Tm(TmTag::Lam))?;
    if inner_truth_binder != right || kernel.arena().bool_value(inner_truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the inner successor-functionality universal",
        });
    }
    let [left_graph, right_implication] = exact_op2(kernel, functionality_body, Op2::Imp)?;
    let [right_graph, target_equality] = exact_op2(kernel, right_implication, Op2::Imp)?;
    let left_assumption = kernel.identity(positive(left_graph))?;
    let right_assumption = kernel.identity(positive(right_graph))?;

    let left_preimage = successor_preimage_at(
        kernel,
        successor_value_theorem,
        natural,
        left,
        left_graph,
        left_assumption,
    )?;
    let right_preimage = successor_preimage_at(
        kernel,
        successor_value_theorem,
        natural,
        right,
        right_graph,
        right_assumption,
    )?;
    let (left_witness, left_body, left_preimage_theorem) = open_choice_body(kernel, left_preimage)?;
    let (right_witness, right_body, right_preimage_theorem) =
        open_choice_body(kernel, right_preimage)?;
    let [left_predecessor_graph, _left_value_equality] = exact_op2(kernel, left_body, Op2::And)?;
    let [right_predecessor_graph, _right_value_equality] = exact_op2(kernel, right_body, Op2::And)?;
    let left_graph_theorem = project_and_left(kernel, left_body)?;
    let left_graph_theorem = kernel.cut(
        left_preimage_theorem,
        left_graph_theorem,
        positive(left_body),
    )?;
    let right_graph_theorem = project_and_left(kernel, right_body)?;
    let right_graph_theorem = kernel.cut(
        right_preimage_theorem,
        right_graph_theorem,
        positive(right_body),
    )?;
    let left_value_theorem = project_and_right(kernel, left_body)?;
    let left_value_theorem = kernel.cut(
        left_preimage_theorem,
        left_value_theorem,
        positive(left_body),
    )?;
    let right_value_theorem = project_and_right(kernel, right_body)?;
    let right_value_theorem = kernel.cut(
        right_preimage_theorem,
        right_value_theorem,
        positive(right_body),
    )?;

    let property_at_left =
        forall_elim(kernel, property_assumption, left_witness).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the functionality hypothesis at the left predecessor value",
            }
        })?;
    let property_at_right =
        forall_elim(kernel, property_at_left.theorem, right_witness).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the functionality hypothesis at the right predecessor value",
            }
        })?;
    let [left_source, right_property] = exact_op2(kernel, property_at_right.proposition, Op2::Imp)?;
    let [right_source, _witness_equality] = exact_op2(kernel, right_property, Op2::Imp)?;
    join_same_syntax(kernel, left_predecessor_graph, left_source)?;
    join_same_syntax(kernel, right_predecessor_graph, right_source)?;
    kernel.convert_conclusions(left_graph_theorem, left_predecessor_graph, left_source)?;
    kernel.convert_conclusions(right_graph_theorem, right_predecessor_graph, right_source)?;
    let after_left = modus_ponens(
        kernel,
        property_at_right.theorem,
        left_graph_theorem,
        property_at_right.proposition,
    )?;
    let witness_equality = modus_ponens(kernel, after_left, right_graph_theorem, right_property)?;

    let step_at_natural = kernel.app(recursion_step, natural)?;
    let stepped_equality = kernel.ap_term(witness_equality, step_at_natural)?;
    let left_to_step = proved_equality_from_theorem(kernel, left_value_theorem)?;
    let right_to_step = proved_equality_from_theorem(kernel, right_value_theorem)?;
    let stepped_equality = retarget_equality(
        kernel,
        bool_ty,
        stepped_equality.theorem,
        left_to_step.right,
        right_to_step.right,
    )?;
    let through_step = equality_transitivity(
        kernel,
        bool_ty,
        left_to_step.theorem,
        stepped_equality.theorem,
    )?;
    let step_to_right = equality_symmetry(kernel, bool_ty, right_to_step.theorem)?;
    let result =
        equality_transitivity(kernel, bool_ty, through_step.theorem, step_to_right.theorem)?;
    join_same_syntax(kernel, result.equality, target_equality)?;
    kernel.convert_conclusions(result.theorem, result.equality, target_equality)?;
    kernel.contract_theorem(result.theorem)?;
    let inner_implication = kernel.imp_right(result.theorem, positive(right_implication))?;
    let outer_implication = kernel.imp_right(inner_implication, positive(functionality_body))?;
    let at_right = kernel.forall_intro_at(outer_implication, right, inner_universal)?;
    let at_left = kernel.forall_intro_at(at_right, left, expanded_successor)?;
    kernel.convert_conclusions(at_left, expanded_successor, property_at_successor)?;
    let induction_step = kernel.imp_right(at_left, positive(step_implication))?;
    kernel.contract_theorem(induction_step)?;
    Ok(kernel.forall_intro_at(induction_step, natural, target)?)
}

fn successor_preimage_at(
    kernel: &mut Kernel,
    theorem: ThmId,
    natural: Ref,
    value: Ref,
    graph_proposition: Ref,
    graph_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let at_natural =
        forall_elim(kernel, theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "successor inversion at the induction predecessor",
        })?;
    let at_value =
        forall_elim(kernel, at_natural.theorem, value).map_err(|_| NaturalError::WrongForm {
            expected: "successor inversion at the induction value",
        })?;
    let [source, _target] = exact_op2(kernel, at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_proposition, source)?;
    kernel.convert_conclusions(graph_theorem, graph_proposition, source)?;
    modus_ponens(
        kernel,
        at_value.theorem,
        graph_theorem,
        at_value.proposition,
    )
}

fn open_choice_body(
    kernel: &mut Kernel,
    theorem: ThmId,
) -> Result<(Ref, Ref, ThmId), NaturalError> {
    let exists = sole_conclusion(kernel, theorem)?;
    let [predicate, witness] = exact_children(kernel, exists, Tag::Tm(TmTag::App))?;
    let (application, body, beta) = beta_apply(kernel, predicate, witness)?;
    join_same_syntax(kernel, exists, application)?;
    kernel.union_syn_fact(beta)?;
    kernel.convert_conclusions(theorem, exists, body)?;
    Ok((witness, body, theorem))
}

fn proved_equality_from_theorem(
    kernel: &Kernel,
    theorem: ThmId,
) -> Result<crate::ProvedEquality, NaturalError> {
    let equality = sole_conclusion(kernel, theorem)?;
    let [_domain, left, right] = exact_children(kernel, equality, Tag::Tm(TmTag::Eq))?;
    Ok(crate::ProvedEquality {
        left,
        right,
        equality,
        theorem,
    })
}

fn retarget_equality(
    kernel: &mut Kernel,
    bool_ty: Ref,
    theorem: ThmId,
    left: Ref,
    right: Ref,
) -> Result<crate::ProvedEquality, NaturalError> {
    let source = proved_equality_from_theorem(kernel, theorem)?;
    let target = kernel.eq(bool_ty, left, right)?;
    let [source_domain, _source_left, _source_right] =
        exact_children(kernel, source.equality, Tag::Tm(TmTag::Eq))?;
    let [target_domain, _target_left, _target_right] =
        exact_children(kernel, target, Tag::Tm(TmTag::Eq))?;
    let domain = join_same_syntax(kernel, source_domain, target_domain)?;
    let left_fact = join_same_syntax(kernel, source.left, left)?;
    let right_fact = join_same_syntax(kernel, source.right, right)?;
    let congruence = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        source.equality,
        target,
        &[domain, left_fact, right_fact],
    )?;
    kernel.union_syn_fact(congruence)?;
    kernel.convert_conclusions(theorem, source.equality, target)?;
    proved_equality_from_theorem(kernel, theorem)
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
    let predicate_natural = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let value = kernel.tm_fv(fresh_global_name(kernel)?, codomain)?;
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

/// Selects the unique graph value pointwise using the witness already present
/// in the equality/choice encoding of totality.  This is deliberately a
/// userspace construction: choice, beta conversion, congruence, and universal
/// introduction are all checked by the ordinary kernel surface.
fn select_graph_function(
    kernel: &mut Kernel,
    naturals: &Naturals,
    graph: Ref,
    total: Ref,
    total_theorem: ThmId,
) -> Result<(Ref, Ref, ThmId), NaturalError> {
    let [_bool_ty, total_function, truth_function] =
        exact_children(kernel, total, Tag::Tm(TmTag::Eq))?;
    let [natural, exists_value] = exact_children(kernel, total_function, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth_function, Tag::Tm(TmTag::Lam))?;
    if truth_binder != natural || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the graph totality universal",
        });
    }
    join_same_syntax(kernel, kernel.classifier(natural)?, naturals.ty)?;
    let [total_predicate, total_argument] =
        exact_children(kernel, exists_value, Tag::Tm(TmTag::App))?;
    join_same_syntax(kernel, total_argument, natural)?;
    let (total_application, expanded_exists, total_beta) =
        beta_apply(kernel, total_predicate, natural)?;
    join_same_syntax(kernel, total_application, exists_value)?;
    kernel.union_syn_fact(total_beta)?;
    let [predicate, choice] = exact_children(kernel, expanded_exists, Tag::Tm(TmTag::App))?;
    let rec = kernel.lam(natural, choice)?;

    let selected_exists =
        forall_elim(kernel, total_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "graph totality specialized at a natural",
        })?;
    join_same_syntax(kernel, selected_exists.proposition, exists_value)?;
    kernel.convert_conclusions(
        selected_exists.theorem,
        selected_exists.proposition,
        expanded_exists,
    )?;
    let (exists_application, selected_graph, exists_beta) = beta_apply(kernel, predicate, choice)?;
    join_same_syntax(kernel, exists_application, expanded_exists)?;
    kernel.union_syn_fact(exists_beta)?;
    kernel.convert_conclusions(selected_exists.theorem, expanded_exists, selected_graph)?;

    let (rec_application, selected_value, rec_beta) = beta_apply(kernel, rec, natural)?;
    join_same_syntax(kernel, selected_value, choice)?;
    kernel.union_syn_fact(rec_beta)?;
    let graph_at_natural = kernel.app(graph, natural)?;
    let rec_graph_at_natural = kernel.app(graph_at_natural, rec_application)?;
    let choice_graph_at_natural = kernel.app(graph_at_natural, choice)?;
    join_same_syntax(kernel, choice_graph_at_natural, selected_graph)?;
    let graph_refl = kernel.syn_refl(None, SynRel::Syn, graph_at_natural)?;
    let rec_congruence = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        rec_graph_at_natural,
        choice_graph_at_natural,
        &[graph_refl, rec_beta],
    )?;
    kernel.union_syn_fact(rec_congruence)?;
    kernel.convert_conclusions(
        selected_exists.theorem,
        selected_graph,
        rec_graph_at_natural,
    )?;
    let bool_ty = kernel.classifier(rec_graph_at_natural)?;
    let rec_graph = kernel.forall_tm(bool_ty, natural, rec_graph_at_natural)?;
    let rec_graph_theorem = kernel.forall_intro_at(selected_exists.theorem, natural, rec_graph)?;
    Ok((rec, rec_graph, rec_graph_theorem))
}

fn prove_rec_specification(
    kernel: &mut Kernel,
    specification_predicate: Ref,
    graph: &NaturalRecGraph,
) -> Result<(Ref, ThmId), NaturalError> {
    let predicate_ty = kernel.classifier(specification_predicate)?;
    let [candidate_ty, _bool_ty] = exact_children(
        kernel,
        predicate_ty,
        Tag::Ty(covalence_logic_hol::TyTag::Arr),
    )?;
    join_same_syntax(kernel, candidate_ty, kernel.classifier(graph.rec)?)?;
    let (_application, specification, beta) =
        beta_apply(kernel, specification_predicate, graph.rec)?;
    kernel.union_syn_fact(beta)?;
    let [zero_law, successor_law] = exact_op2(kernel, specification, Op2::And)?;
    let zero_theorem = kernel.copy_theorem(graph.rec_zero_theorem)?;
    let zero_conclusion = sole_conclusion(kernel, zero_theorem)?;
    join_same_syntax(kernel, zero_conclusion, zero_law)?;
    kernel.convert_conclusions(zero_theorem, zero_conclusion, zero_law)?;
    let [_successor_bool, successor_function, _successor_truth] =
        exact_children(kernel, successor_law, Tag::Tm(TmTag::Eq))?;
    let [successor_binder, successor_body] =
        exact_children(kernel, successor_function, Tag::Tm(TmTag::Lam))?;
    let specialized_successor = forall_elim(kernel, graph.rec_successor_theorem, successor_binder)
        .map_err(|_| NaturalError::WrongForm {
            expected: "the selected successor law at the specification binder",
        })?;
    join_same_syntax(kernel, specialized_successor.proposition, successor_body)?;
    kernel.convert_conclusions(
        specialized_successor.theorem,
        specialized_successor.proposition,
        successor_body,
    )?;
    let successor_theorem = kernel.forall_intro_at(
        specialized_successor.theorem,
        successor_binder,
        successor_law,
    )?;
    let theorem = kernel.and_right(zero_theorem, successor_theorem, positive(specification))?;
    Ok((specification, theorem))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_rec_uniqueness(
    kernel: &mut Kernel,
    naturals: &Naturals,
    specification_predicate: Ref,
    graph: &NaturalRecGraph,
    _base: Ref,
    step: Ref,
    codomain: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let function_ty = kernel.classifier(graph.rec)?;
    let candidate = kernel.tm_fv(fresh_global_name(kernel)?, function_ty)?;
    let (_specification_application, candidate_specification, specification_beta) =
        beta_apply(kernel, specification_predicate, candidate)?;
    kernel.union_syn_fact(specification_beta)?;
    let [_candidate_zero_law, candidate_successor_law] =
        exact_op2(kernel, candidate_specification, Op2::And)?;
    let candidate_zero_theorem = project_and_left(kernel, candidate_specification)?;
    let candidate_successor_theorem = project_and_right(kernel, candidate_specification)?;

    let index = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let candidate_at_index = kernel.app(candidate, index)?;
    let rec_at_index = kernel.app(graph.rec, index)?;
    let bool_ty = kernel.classifier(candidate_successor_law)?;
    let equality_at_index = kernel.eq(bool_ty, candidate_at_index, rec_at_index)?;
    let equality_predicate = kernel.lam(index, equality_at_index)?;

    let [_induction_bool, induction_function, _induction_truth] =
        exact_children(kernel, naturals.induction, Tag::Tm(TmTag::Eq))?;
    let [induction_predicate, _induction_body] =
        exact_children(kernel, induction_function, Tag::Tm(TmTag::Lam))?;
    join_same_syntax(
        kernel,
        kernel.classifier(induction_predicate)?,
        kernel.classifier(equality_predicate)?,
    )?;
    let induction =
        forall_elim(kernel, naturals.induction_theorem, equality_predicate).map_err(|_| {
            NaturalError::WrongForm {
                expected: "natural induction at recursor uniqueness",
            }
        })?;
    let [induction_premises, induction_conclusion] =
        exact_op2(kernel, induction.proposition, Op2::Imp)?;
    let [induction_base, induction_step] = exact_op2(kernel, induction_premises, Op2::And)?;

    // candidate zero = base = rec zero
    let rec_zero_reversed = equality_symmetry(kernel, bool_ty, graph.rec_zero_theorem)?;
    let base_equality = equality_transitivity(
        kernel,
        bool_ty,
        candidate_zero_theorem,
        rec_zero_reversed.theorem,
    )?;
    let (base_application, base_body, base_beta) =
        beta_apply(kernel, equality_predicate, naturals.zero)?;
    kernel.union_syn_fact(base_beta)?;
    join_same_syntax(kernel, base_equality.equality, base_body)?;
    kernel.convert_conclusions(
        base_equality.theorem,
        base_equality.equality,
        base_application,
    )?;
    join_same_syntax(kernel, base_application, induction_base)?;
    kernel.convert_conclusions(base_equality.theorem, base_application, induction_base)?;

    // The successor case transports the induction equality through `step n`,
    // then chains the candidate and selected computation equations.
    let [_step_bool, step_function, step_truth] =
        exact_children(kernel, induction_step, Tag::Tm(TmTag::Eq))?;
    let [step_index, step_implication] =
        exact_children(kernel, step_function, Tag::Tm(TmTag::Lam))?;
    let [truth_index, truth_body] = exact_children(kernel, step_truth, Tag::Tm(TmTag::Lam))?;
    if truth_index != step_index || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the recursor uniqueness induction step universal",
        });
    }
    let [step_hypothesis, step_conclusion] = exact_op2(kernel, step_implication, Op2::Imp)?;
    let hypothesis = kernel.identity(positive(step_hypothesis))?;
    let (hypothesis_application, hypothesis_equality, hypothesis_beta) =
        beta_apply(kernel, equality_predicate, step_index)?;
    join_same_syntax(kernel, hypothesis_application, step_hypothesis)?;
    kernel.union_syn_fact(hypothesis_beta)?;
    kernel.convert_conclusions(hypothesis, step_hypothesis, hypothesis_equality)?;

    let step_at_index = kernel.app(step, step_index)?;
    let lifted_hypothesis = kernel.ap_term(hypothesis, step_at_index)?;
    let candidate_step =
        forall_elim(kernel, candidate_successor_theorem, step_index).map_err(|_| {
            NaturalError::WrongForm {
                expected: "the candidate recursion successor law",
            }
        })?;
    let rec_step = forall_elim(kernel, graph.rec_successor_theorem, step_index).map_err(|_| {
        NaturalError::WrongForm {
            expected: "the selected recursion successor law",
        }
    })?;
    let reversed_rec_step = equality_symmetry(kernel, bool_ty, rec_step.theorem)?;
    let next_index = kernel.app(naturals.succ, step_index)?;
    let candidate_next = kernel.app(candidate, next_index)?;
    let candidate_current = kernel.app(candidate, step_index)?;
    let rec_current = kernel.app(graph.rec, step_index)?;
    let stepped_candidate = kernel.app(step_at_index, candidate_current)?;
    let stepped_rec = kernel.app(step_at_index, rec_current)?;
    let rec_next = kernel.app(graph.rec, next_index)?;
    let candidate_step = retarget_equality(
        kernel,
        bool_ty,
        candidate_step.theorem,
        candidate_next,
        stepped_candidate,
    )?;
    let lifted_hypothesis = retarget_equality(
        kernel,
        bool_ty,
        lifted_hypothesis.theorem,
        stepped_candidate,
        stepped_rec,
    )?;
    let reversed_rec_step = retarget_equality(
        kernel,
        bool_ty,
        reversed_rec_step.theorem,
        stepped_rec,
        rec_next,
    )?;
    let through_candidate = equality_transitivity(
        kernel,
        bool_ty,
        candidate_step.theorem,
        lifted_hypothesis.theorem,
    )?;
    let successor_equality = equality_transitivity(
        kernel,
        bool_ty,
        through_candidate.theorem,
        reversed_rec_step.theorem,
    )?;
    let (conclusion_application, conclusion_equality, conclusion_beta) =
        beta_apply(kernel, equality_predicate, next_index)?;
    kernel.union_syn_fact(conclusion_beta)?;
    join_same_syntax(kernel, successor_equality.equality, conclusion_equality)?;
    kernel.convert_conclusions(
        successor_equality.theorem,
        successor_equality.equality,
        conclusion_application,
    )?;
    join_same_syntax(kernel, conclusion_application, step_conclusion)?;
    kernel.convert_conclusions(
        successor_equality.theorem,
        conclusion_application,
        step_conclusion,
    )?;
    let successor_implication =
        kernel.imp_right(successor_equality.theorem, positive(step_implication))?;
    let successor_universal =
        kernel.forall_intro_at(successor_implication, step_index, induction_step)?;

    let induction_inputs = kernel.and_right(
        base_equality.theorem,
        successor_universal,
        positive(induction_premises),
    )?;
    kernel.contract_theorem(induction_inputs)?;
    let pointwise = modus_ponens(
        kernel,
        induction.theorem,
        induction_inputs,
        induction.proposition,
    )?;
    let uniqueness_body = kernel.op2(Op2::Imp, candidate_specification, induction_conclusion)?;
    let uniqueness_at_candidate = kernel.imp_right(pointwise, positive(uniqueness_body))?;
    let unique = kernel.forall_tm(bool_ty, candidate, uniqueness_body)?;
    let unique_theorem = kernel.forall_intro_at(uniqueness_at_candidate, candidate, unique)?;
    // Keep the codomain check explicit at this API boundary.
    join_same_syntax(kernel, kernel.classifier(candidate_at_index)?, codomain)?;
    Ok((unique, unique_theorem))
}

fn prove_rec_zero(
    kernel: &mut Kernel,
    naturals: &Naturals,
    rec: Ref,
    rec_graph_theorem: ThmId,
    zero_value_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let rec_at_zero = kernel.app(rec, naturals.zero)?;
    let selected_at_zero = forall_elim(kernel, rec_graph_theorem, naturals.zero).map_err(|_| {
        NaturalError::WrongForm {
            expected: "the selected recursion graph at zero",
        }
    })?;
    let zero_value_at_rec = forall_elim(kernel, zero_value_theorem, rec_at_zero).map_err(|_| {
        NaturalError::WrongForm {
            expected: "graph zero inversion at the selected value",
        }
    })?;
    let [source, equality] = exact_op2(kernel, zero_value_at_rec.proposition, Op2::Imp)?;
    join_same_syntax(kernel, source, selected_at_zero.proposition)?;
    kernel.convert_conclusions(
        selected_at_zero.theorem,
        selected_at_zero.proposition,
        source,
    )?;
    let theorem = modus_ponens(
        kernel,
        zero_value_at_rec.theorem,
        selected_at_zero.theorem,
        zero_value_at_rec.proposition,
    )?;
    Ok((equality, theorem))
}

#[allow(clippy::too_many_arguments)]
fn prove_rec_successor(
    kernel: &mut Kernel,
    naturals: &Naturals,
    rec: Ref,
    recursion_step: Ref,
    rec_graph_theorem: ThmId,
    graph_step_theorem: ThmId,
    functional_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let natural = kernel.tm_fv(fresh_global_name(kernel)?, naturals.ty)?;
    let rec_at_natural = kernel.app(rec, natural)?;
    let successor = kernel.app(naturals.succ, natural)?;
    let rec_at_successor = kernel.app(rec, successor)?;
    let step_at_natural = kernel.app(recursion_step, natural)?;
    let stepped_value = kernel.app(step_at_natural, rec_at_natural)?;

    let graph_at_natural =
        forall_elim(kernel, rec_graph_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "the selected recursion graph at a natural",
        })?;
    let graph_step_at_natural =
        forall_elim(kernel, graph_step_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "the recursion graph step at a natural",
        })?;
    let graph_step_at_value = forall_elim(kernel, graph_step_at_natural.theorem, rec_at_natural)
        .map_err(|_| NaturalError::WrongForm {
            expected: "the recursion graph step at the selected value",
        })?;
    let [step_source, _step_target] = exact_op2(kernel, graph_step_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, graph_at_natural.proposition, step_source)?;
    kernel.convert_conclusions(
        graph_at_natural.theorem,
        graph_at_natural.proposition,
        step_source,
    )?;
    let stepped_graph = modus_ponens(
        kernel,
        graph_step_at_value.theorem,
        graph_at_natural.theorem,
        graph_step_at_value.proposition,
    )?;
    let selected_successor =
        forall_elim(kernel, rec_graph_theorem, successor).map_err(|_| NaturalError::WrongForm {
            expected: "the selected recursion graph at a successor",
        })?;

    let functional_at_successor =
        forall_elim(kernel, functional_theorem, successor).map_err(|_| {
            NaturalError::WrongForm {
                expected: "graph functionality at a successor",
            }
        })?;
    let functional_at_successor = beta_reduce_conclusion(
        kernel,
        functional_at_successor.proposition,
        functional_at_successor.theorem,
    )?;
    let functional_at_selected = forall_elim(kernel, functional_at_successor.1, rec_at_successor)
        .map_err(|_| NaturalError::WrongForm {
        expected: "graph functionality at the selected successor value",
    })?;
    let functional_at_selected = beta_reduce_conclusion(
        kernel,
        functional_at_selected.proposition,
        functional_at_selected.theorem,
    )?;
    let functional_at_step =
        forall_elim(kernel, functional_at_selected.1, stepped_value).map_err(|_| {
            NaturalError::WrongForm {
                expected: "graph functionality at the recursive step value",
            }
        })?;
    let [selected_source, remaining] = exact_op2(kernel, functional_at_step.proposition, Op2::Imp)?;
    join_same_syntax(kernel, selected_source, selected_successor.proposition)?;
    kernel.convert_conclusions(
        selected_successor.theorem,
        selected_successor.proposition,
        selected_source,
    )?;
    let after_selected = modus_ponens(
        kernel,
        functional_at_step.theorem,
        selected_successor.theorem,
        functional_at_step.proposition,
    )?;
    let [stepped_source, equality] = exact_op2(kernel, remaining, Op2::Imp)?;
    let stepped_conclusion = sole_conclusion(kernel, stepped_graph)?;
    join_same_syntax(kernel, stepped_source, stepped_conclusion)?;
    kernel.convert_conclusions(stepped_graph, stepped_conclusion, stepped_source)?;
    let theorem = modus_ponens(kernel, after_selected, stepped_graph, remaining)?;
    let bool_ty = kernel.classifier(equality)?;
    let universal = kernel.forall_tm(bool_ty, natural, equality)?;
    let theorem = kernel.forall_intro_at(theorem, natural, universal)?;
    Ok((universal, theorem))
}

fn beta_reduce_conclusion(
    kernel: &mut Kernel,
    proposition: Ref,
    theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    if kernel.arena().tag(proposition) != Some(Tag::Tm(TmTag::App)) {
        return Ok((proposition, theorem));
    }
    let [function, argument] = exact_children(kernel, proposition, Tag::Tm(TmTag::App))?;
    if kernel.arena().tag(function) != Some(Tag::Tm(TmTag::Lam)) {
        return Ok((proposition, theorem));
    }
    let (application, body, beta) = beta_apply(kernel, function, argument)?;
    join_same_syntax(kernel, application, proposition)?;
    kernel.union_syn_fact(beta)?;
    kernel.convert_conclusions(theorem, proposition, body)?;
    Ok((body, theorem))
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

fn exact_op1(
    kernel: &Kernel,
    reference: Ref,
    op: covalence_logic_hol::builtin::Op1,
) -> Result<[Ref; 1], NaturalError> {
    if kernel.arena().op1(reference) != Some(op) {
        return Err(NaturalError::WrongForm {
            expected: "a compact unary logical opcode",
        });
    }
    exact_children(kernel, reference, Tag::Tm(TmTag::Op1))
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

fn fresh_global_name(kernel: &Kernel) -> Result<u64, NaturalError> {
    let roots = (1..=kernel.arena().len())
        .map(|raw| {
            Ref::new(i32::try_from(raw).map_err(|_| NaturalError::WrongForm {
                expected: "an i32-sized recursion arena",
            })?)
            .ok_or(NaturalError::WrongForm {
                expected: "a nonzero recursion row",
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(kernel.fresh_name(&roots)?)
}
