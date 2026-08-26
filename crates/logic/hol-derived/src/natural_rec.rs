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
        Ok(NaturalRecGraph {
            graph,
            base: base_proposition,
            base_theorem,
            step: step_proposition,
            step_theorem,
            total,
            total_theorem,
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
