//! Relational HOL expression lowering over the generic expression fold.

use std::{collections::BTreeSet, sync::Arc};

use covalence_data_spectec::{
    DeclarationId, IlArgument, IlBinding, IlClauseSchema, IlDeclarationBody, IlDomain,
    IlExpression, IlExpressionView, IlIteration, IlKind, IlPremise, IlRuleSchema, IlSchemaError,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, Tag, ThmId, TyTag, builtin::Op1, builtin::Op2,
};
use covalence_logic_hol_derived::{
    EqualityError, ExistsError, ForallError, ModelError, SyntaxError, equality_symmetry,
    forall_elim, introduce_exists, join_alpha_equivalent, open_exists, substitute,
};

use crate::{
    Evidence, ExpressionAlgebra, HolCase, HolFamilyError, HolRule, HolSchema, HolTheoryError,
    LeastPredicate, LeastPredicateError, Source, begin_least_closed_family_avoiding,
    close_hol_rule, close_hol_rules, existential_case, fold_expression,
};

/// Relational meaning of one expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalTerm {
    value: Ref,
    binders: Vec<Ref>,
    premises: Vec<Ref>,
}

/// Resolved graph predicate and checked result classifier for one call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RelationalCall {
    /// Graph predicate after applying every explicit input argument.
    pub predicate: Ref,
    /// Classifier of the fresh result accepted by `predicate`.
    pub result_type: Ref,
}

/// Why lowered clause terms could not form one exact HOL graph case.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RelationalCaseError {
    /// Clause patterns did not cover the declaration's formal inputs exactly.
    #[snafu(display("clause has {actual} patterns; definition has {expected} inputs"))]
    Arity {
        /// Number of declaration inputs.
        expected: usize,
        /// Number of clause patterns.
        actual: usize,
    },
    /// A checked HOL constructor rejected the case.
    #[snafu(display("could not construct relational HOL clause case: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A schema slot was not a curried graph predicate with a result argument.
    #[snafu(display("definition schema slot is not a function ending in bool"))]
    NotGraph,
    /// A lowered pattern did not share its formal input's classifier.
    #[snafu(display(
        "clause pattern {index} ({pattern:?}) does not match formal {formal:?}: {source}"
    ))]
    Pattern {
        /// Zero-based input position.
        index: usize,
        /// Universal formal input.
        formal: Ref,
        /// Lowered pattern value.
        pattern: Ref,
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A lowered result did not share the formal result's classifier.
    #[snafu(display("clause result {result:?} does not match formal {formal:?}: {source}"))]
    Result {
        /// Universal formal result.
        formal: Ref,
        /// Lowered result value.
        result: Ref,
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Lowered ingredients of one source-ordered definition clause.
#[derive(Clone, Copy, Debug)]
pub struct RelationalClause<'a> {
    /// Universally bound declaration inputs.
    pub formal_inputs: &'a [Ref],
    /// Universally bound graph result.
    pub formal_result: Ref,
    /// Clause-local variables decoded from explicit bindings.
    pub explicit_locals: &'a [Ref],
    /// Lowered left-hand-side patterns in input order.
    pub patterns: &'a [RelationalTerm],
    /// Lowered right-hand-side result expression.
    pub result: &'a RelationalTerm,
    /// Fresh binders introduced while lowering semantic premises.
    pub semantic_binders: &'a [Ref],
    /// Lowered semantic premise propositions.
    pub semantic_premises: &'a [Ref],
    /// Whether this clause carries `otherwise`.
    pub otherwise: bool,
}

/// Lowered conjunction contributed by one premise subtree.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RelationalCondition {
    binders: Vec<Ref>,
    premises: Vec<Ref>,
    otherwise: bool,
}

/// Checked result of lowering one complete ordered definition body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalDefinition {
    /// Universally quantified graph inputs derived from the schema slot.
    pub formal_inputs: Vec<Ref>,
    /// Universally quantified graph result derived from the schema slot.
    pub formal_result: Ref,
    /// Exact source-ordered cases.
    pub cases: Vec<HolCase>,
    /// Witness and conjunct structure retained for proving each case.
    pub case_artifacts: Vec<RelationalCaseArtifact>,
    /// Ordered disjunction used as the graph body.
    pub body: Ref,
    /// Universally closed exact graph equation.
    pub equation: Ref,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// One definition graph specialized at concrete inputs and a concrete result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalDefinitionInstance {
    /// Source-ordered specialized cases.
    pub cases: Vec<HolCase>,
    /// Specialized witness and conjunct structure for each case.
    pub case_artifacts: Vec<RelationalCaseArtifact>,
    /// Exact ordered disjunction of the specialized cases.
    pub body: Ref,
}

/// Exact existential structure used to construct one definition case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalCaseArtifact {
    /// Public ordered-case proposition.
    pub case: HolCase,
    /// Lowered left-hand-side pattern values in declaration-input order.
    pub pattern_values: Vec<Ref>,
    /// Lowered right-hand-side result value before graph-result equality.
    pub result_value: Ref,
    /// Existential binders of `case.applicable`.
    pub applicable_binders: Vec<Ref>,
    /// Conjuncts inside `case.applicable`.
    pub applicable_conditions: Vec<Ref>,
    /// Existential binders of `case.produces`.
    pub production_binders: Vec<Ref>,
    /// Conjuncts inside `case.produces`.
    pub production_conditions: Vec<Ref>,
}

/// Checked witnesses and elementary facts obtained by opening one production.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OpenedRelationalProduction {
    /// Hilbert-choice witnesses encoded by the production existentials.
    pub witnesses: Vec<Ref>,
    /// Specialized elementary conditions in source order.
    pub conditions: Vec<Ref>,
    /// Theorem facts proving the corresponding [`conditions`](Self::conditions).
    pub facts: Vec<ThmId>,
}

impl RelationalDefinition {
    /// Chooses production witnesses by structurally matching clause patterns.
    ///
    /// Pattern binders are unified with corresponding subterms of `inputs`.
    /// Repeated binders must match structurally identical subterms. Any
    /// production binder not mentioned by a pattern is filled with a fresh term
    /// of its exact retained classifier. This is syntax-directed witness
    /// selection only; it does not decide a semantic premise.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing case, wrong input arity, name exhaustion,
    /// or a rejected checked classifier/syntax operation. A structural mismatch
    /// returns `Ok(None)`. `kernel` is unchanged on failure or mismatch.
    pub fn match_production_witnesses(
        &self,
        kernel: &mut Kernel,
        index: usize,
        inputs: &[Ref],
    ) -> Result<Option<Vec<Ref>>, DefinitionProofError> {
        if inputs.len() != self.formal_inputs.len() {
            return Err(DefinitionProofError::Arity {
                expected: self.formal_inputs.len(),
                actual: inputs.len(),
            });
        }
        let artifact = self
            .case_artifacts
            .get(index)
            .ok_or(DefinitionProofError::MissingCase { index })?;
        if artifact.pattern_values.len() != inputs.len() {
            return Err(DefinitionProofError::ConditionShape);
        }
        let mut staged = kernel.fork();
        let mut assignments = vec![None; artifact.production_binders.len()];
        for (&pattern, &input) in artifact.pattern_values.iter().zip(inputs) {
            if !match_pattern_term(
                &mut staged,
                pattern,
                input,
                &artifact.production_binders,
                &mut assignments,
            )? {
                return Ok(None);
            }
        }
        let roots = artifact
            .production_binders
            .iter()
            .chain(artifact.pattern_values.iter())
            .chain(inputs.iter())
            .copied()
            .collect::<Vec<_>>();
        let first = staged.fresh_name(&roots)?;
        for (index, assignment) in assignments.iter_mut().enumerate() {
            if assignment.is_none() {
                let offset = u64::try_from(index).map_err(|_| KernelError::TooManyNames)?;
                let name = first.checked_add(offset).ok_or(KernelError::TooManyNames)?;
                let classifier = staged.classifier(artifact.production_binders[index])?;
                *assignment = Some(staged.tm_fv(name, classifier)?);
            }
        }
        let witnesses = assignments
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or(DefinitionProofError::ConditionShape)?;
        *kernel = staged;
        Ok(Some(witnesses))
    }

    /// Constructs a clause's lowered right-hand-side result at chosen values.
    ///
    /// The result expression is retained as the right operand of the final
    /// production condition `formal_result = result`. This method substitutes
    /// concrete declaration inputs and clause witnesses without evaluating the
    /// expression. Using the returned term as the graph result makes that final
    /// condition reflexive by construction.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing case, mismatched input or witness arity,
    /// or failed checked substitution.
    /// `kernel` is unchanged on failure.
    pub fn production_result(
        &self,
        kernel: &mut Kernel,
        index: usize,
        inputs: &[Ref],
        witnesses: &[Ref],
    ) -> Result<Ref, DefinitionProofError> {
        if inputs.len() != self.formal_inputs.len() {
            return Err(DefinitionProofError::Arity {
                expected: self.formal_inputs.len(),
                actual: inputs.len(),
            });
        }
        let artifact = self
            .case_artifacts
            .get(index)
            .ok_or(DefinitionProofError::MissingCase { index })?;
        if witnesses.len() != artifact.production_binders.len() {
            return Err(DefinitionProofError::WitnessArity {
                expected: artifact.production_binders.len(),
                actual: witnesses.len(),
            });
        }
        let mut staged = kernel.fork();
        let mut result = artifact.result_value;
        for (variable, value) in self
            .formal_inputs
            .iter()
            .copied()
            .zip(inputs.iter().copied())
            .chain(
                artifact
                    .production_binders
                    .iter()
                    .copied()
                    .zip(witnesses.iter().copied()),
            )
        {
            result = substitute(&mut staged, variable, value, result)
                .map_err(|source| DefinitionProofError::Substitute { source })?
                .output;
        }
        *kernel = staged;
        Ok(result)
    }

    /// Specializes every retained case at concrete graph inputs and result.
    ///
    /// # Errors
    ///
    /// Returns an error for the wrong input arity or if checked substitution or
    /// ordered-body reconstruction fails. `kernel` is unchanged on failure.
    pub fn specialize(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        inputs: &[Ref],
        result: Ref,
    ) -> Result<RelationalDefinitionInstance, DefinitionProofError> {
        if inputs.len() != self.formal_inputs.len() {
            return Err(DefinitionProofError::Arity {
                expected: self.formal_inputs.len(),
                actual: inputs.len(),
            });
        }
        let mut staged = kernel.fork();
        let substitutions = self
            .formal_inputs
            .iter()
            .copied()
            .zip(inputs.iter().copied())
            .chain(std::iter::once((self.formal_result, result)))
            .collect::<Vec<_>>();
        let specialize =
            |kernel: &mut Kernel, mut proposition: Ref| -> Result<Ref, DefinitionProofError> {
                for &(variable, value) in &substitutions {
                    proposition = substitute(kernel, variable, value, proposition)
                        .map_err(|source| DefinitionProofError::Substitute { source })?
                        .output;
                }
                Ok(proposition)
            };
        let case_artifacts = self
            .case_artifacts
            .iter()
            .map(|artifact| {
                let applicable_conditions = artifact
                    .applicable_conditions
                    .iter()
                    .map(|&condition| specialize(&mut staged, condition))
                    .collect::<Result<Vec<_>, _>>()?;
                let production_conditions = artifact
                    .production_conditions
                    .iter()
                    .map(|&condition| specialize(&mut staged, condition))
                    .collect::<Result<Vec<_>, _>>()?;
                let applicable = crate::existential_case(
                    &mut staged,
                    bool_ty,
                    &artifact.applicable_binders,
                    &applicable_conditions,
                )?;
                let produces = crate::existential_case(
                    &mut staged,
                    bool_ty,
                    &artifact.production_binders,
                    &production_conditions,
                )?;
                let case = HolCase {
                    applicable,
                    produces,
                    otherwise: artifact.case.otherwise,
                };
                Ok(RelationalCaseArtifact {
                    case,
                    pattern_values: artifact
                        .pattern_values
                        .iter()
                        .map(|&pattern| specialize(&mut staged, pattern))
                        .collect::<Result<Vec<_>, _>>()?,
                    result_value: specialize(&mut staged, artifact.result_value)?,
                    applicable_binders: artifact.applicable_binders.clone(),
                    applicable_conditions,
                    production_binders: artifact.production_binders.clone(),
                    production_conditions,
                })
            })
            .collect::<Result<Vec<_>, DefinitionProofError>>()?;
        let cases = case_artifacts
            .iter()
            .map(|artifact| artifact.case)
            .collect::<Vec<_>>();
        let body = crate::ordered_cases(&mut staged, bool_ty, &cases)
            .map_err(|source| DefinitionProofError::Kernel { source })?;
        *kernel = staged;
        Ok(RelationalDefinitionInstance {
            cases,
            case_artifacts,
            body,
        })
    }
}

fn match_pattern_term(
    kernel: &mut Kernel,
    pattern: Ref,
    input: Ref,
    binders: &[Ref],
    assignments: &mut [Option<Ref>],
) -> Result<bool, DefinitionProofError> {
    if let Some(index) = binders.iter().position(|&binder| binder == pattern) {
        if let Some(existing) = assignments[index] {
            return match covalence_logic_hol_derived::join_same_syntax(kernel, existing, input) {
                Ok(_) => Ok(true),
                Err(SyntaxError::Different) => Ok(false),
                Err(SyntaxError::Kernel { source }) => Err(DefinitionProofError::Kernel { source }),
            };
        }
        let pattern_ty = kernel.classifier(pattern)?;
        let input_ty = kernel.classifier(input)?;
        match covalence_logic_hol_derived::join_same_syntax(kernel, pattern_ty, input_ty) {
            Ok(_) => {
                assignments[index] = Some(input);
                return Ok(true);
            }
            Err(SyntaxError::Different) => return Ok(false),
            Err(SyntaxError::Kernel { source }) => {
                return Err(DefinitionProofError::Kernel { source });
            }
        }
    }
    if pattern == input {
        return Ok(true);
    }
    if kernel.arena().tag(pattern) != kernel.arena().tag(input)
        || kernel.arena().name(pattern) != kernel.arena().name(input)
        || kernel.arena().bool_value(pattern) != kernel.arena().bool_value(input)
        || kernel.arena().op1(pattern) != kernel.arena().op1(input)
        || kernel.arena().op2(pattern) != kernel.arena().op2(input)
    {
        return Ok(false);
    }
    let pattern_children = kernel
        .arena()
        .children(pattern)
        .ok_or(DefinitionProofError::ConditionShape)?
        .collect::<Vec<_>>();
    let input_children = kernel
        .arena()
        .children(input)
        .ok_or(DefinitionProofError::ConditionShape)?
        .collect::<Vec<_>>();
    if pattern_children.len() != input_children.len() {
        return Ok(false);
    }
    for (&pattern_child, &input_child) in pattern_children.iter().zip(&input_children) {
        if !match_pattern_term(kernel, pattern_child, input_child, binders, assignments)? {
            return Ok(false);
        }
    }
    Ok(true)
}

impl RelationalDefinitionInstance {
    /// Extracts the sole ordinary production from a proved definition body.
    ///
    /// This is intentionally limited to a one-case, non-`otherwise`
    /// definition, where no case choice or negated applicability evidence is
    /// required. It eliminates the ordered body's initial `false` branch with
    /// ordinary checked propositional rules.
    ///
    /// # Errors
    ///
    /// Returns an error unless this instance has exactly one ordinary case and
    /// `body_fact` proves its exact body. `kernel` is unchanged on failure.
    pub fn prove_only_production_from_body(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        body_fact: ThmId,
    ) -> Result<Evidence, DefinitionProofError> {
        if self.cases.len() != 1 || self.cases[0].otherwise {
            return Err(DefinitionProofError::MissingCase { index: 1 });
        }
        let mut staged = kernel.fork();
        let source = definition_positive_conclusion(&staged, body_fact)?;
        join_alpha_equivalent(&mut staged, source, self.body)?;
        let body_fact = staged.copy_theorem(body_fact)?;
        staged.convert_conclusions(body_fact, source, self.body)?;
        let expanded = staged.expand_conclusion(body_fact, positive(self.body), None)?;
        let falsehood = staged
            .arena()
            .children(self.body)
            .and_then(|mut children| children.next())
            .ok_or(DefinitionProofError::ConditionShape)?;
        if staged.classifier(falsehood)? != bool_ty {
            return Err(DefinitionProofError::ConditionShape);
        }
        let false_left = staged.false_left(positive(falsehood))?;
        let theorem = staged.cut(expanded, false_left, positive(falsehood))?;
        let production = self.cases[0].produces;
        let actual = definition_positive_conclusion(&staged, theorem)?;
        join_alpha_equivalent(&mut staged, actual, production)?;
        staged.convert_conclusions(theorem, actual, production)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: production,
            theorem,
            holds: true,
        })
    }

    /// Opens one proved case production into witnesses and elementary facts.
    ///
    /// Existentials are eliminated at their encoded Hilbert-choice witnesses;
    /// the resulting left-associated conjunction is projected into facts in
    /// the retained source order. Every returned fact preserves the premises
    /// of `production_fact`.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent case, a mismatched theorem, malformed
    /// existential/conjunction structure, or a rejected checked proof step.
    /// `kernel` is unchanged on failure.
    pub fn open_production(
        &self,
        kernel: &mut Kernel,
        index: usize,
        production_fact: ThmId,
    ) -> Result<OpenedRelationalProduction, DefinitionProofError> {
        let artifact = self
            .case_artifacts
            .get(index)
            .ok_or(DefinitionProofError::MissingCase { index })?;
        let mut staged = kernel.fork();
        let source = definition_positive_conclusion(&staged, production_fact)?;
        join_alpha_equivalent(&mut staged, source, artifact.case.produces)?;
        let mut working = staged.copy_theorem(production_fact)?;
        staged.convert_conclusions(working, source, artifact.case.produces)?;
        let mut proposition = artifact.case.produces;
        let mut witnesses = Vec::with_capacity(artifact.production_binders.len());
        for _ in &artifact.production_binders {
            let opened = open_exists(&mut staged, proposition)
                .map_err(|source| DefinitionProofError::Exists { source })?;
            staged.convert_conclusions(working, proposition, opened.body)?;
            witnesses.push(opened.witness);
            proposition = opened.body;
        }
        let conditions = instantiate_case_conditions(
            &mut staged,
            &artifact.production_conditions,
            &artifact.production_binders,
            &witnesses,
        )?;
        let mut reversed_facts = Vec::with_capacity(conditions.len());
        let mut conjunction = proposition;
        for &condition in conditions.iter().rev() {
            let fact = staged.copy_theorem(working)?;
            let right = staged.expand_conclusion(fact, positive(conjunction), Some(true))?;
            let actual = definition_positive_conclusion(&staged, right)?;
            join_alpha_equivalent(&mut staged, actual, condition)?;
            staged.convert_conclusions(right, actual, condition)?;
            reversed_facts.push(right);
            working = staged.expand_conclusion(working, positive(conjunction), Some(false))?;
            conjunction = definition_positive_conclusion(&staged, working)?;
        }
        reversed_facts.reverse();
        *kernel = staged;
        Ok(OpenedRelationalProduction {
            witnesses,
            conditions,
            facts: reversed_facts,
        })
    }

    /// Constructs the elementary obligations for a case's production witnesses.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is absent, the witness count differs from
    /// the retained existential binders, or checked substitution fails.
    /// `kernel` is unchanged on failure.
    pub fn production_obligations(
        &self,
        kernel: &mut Kernel,
        index: usize,
        witnesses: &[Ref],
    ) -> Result<Vec<Ref>, DefinitionProofError> {
        let artifact = self
            .case_artifacts
            .get(index)
            .ok_or(DefinitionProofError::MissingCase { index })?;
        if witnesses.len() != artifact.production_binders.len() {
            return Err(DefinitionProofError::WitnessArity {
                expected: artifact.production_binders.len(),
                actual: witnesses.len(),
            });
        }
        let mut staged = kernel.fork();
        let obligations = instantiate_case_conditions(
            &mut staged,
            &artifact.production_conditions,
            &artifact.production_binders,
            witnesses,
        )?;
        *kernel = staged;
        Ok(obligations)
    }

    /// Proves a case's existential production from elementary condition facts.
    ///
    /// Each theorem in `condition_facts` must prove the corresponding result of
    /// [`Self::production_obligations`]. The method conjoins those facts and
    /// introduces the retained witnesses using checked HOL rules. All premises
    /// remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::production_obligations`], when the fact count or conclusions do
    /// not match, or if checked conjunction or existential introduction fails.
    /// `kernel` is unchanged on failure.
    pub fn prove_production(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        index: usize,
        witnesses: &[Ref],
        condition_facts: &[ThmId],
    ) -> Result<Evidence, DefinitionProofError> {
        let artifact = self
            .case_artifacts
            .get(index)
            .ok_or(DefinitionProofError::MissingCase { index })?;
        let mut staged = kernel.fork();
        let obligations = self.production_obligations(&mut staged, index, witnesses)?;
        if condition_facts.len() != obligations.len() {
            return Err(DefinitionProofError::ConditionArity {
                expected: obligations.len(),
                actual: condition_facts.len(),
            });
        }
        let truth = staged.bool(bool_ty, true)?;
        let mut proposition = truth;
        let mut theorem = staged.true_right(positive(truth))?;
        for (&condition, &fact) in obligations.iter().zip(condition_facts) {
            let source = definition_positive_conclusion(&staged, fact)?;
            join_alpha_equivalent(&mut staged, source, condition)?;
            let aligned = staged.copy_theorem(fact)?;
            staged.convert_conclusions(aligned, source, condition)?;
            proposition = staged.op2(Op2::And, proposition, condition)?;
            theorem = staged.and_right(theorem, aligned, positive(proposition))?;
        }

        let mut current_values = witnesses.to_vec();
        for binder_index in (0..artifact.production_binders.len()).rev() {
            current_values[binder_index] = artifact.production_binders[binder_index];
            let conditions = instantiate_case_conditions(
                &mut staged,
                &artifact.production_conditions,
                &artifact.production_binders,
                &current_values,
            )?;
            let mut opened = crate::existential_case(&mut staged, bool_ty, &[], &conditions)?;
            for &inner in artifact.production_binders[binder_index + 1..].iter().rev() {
                opened = staged.exists_tm(inner, opened)?;
            }
            let introduced = introduce_exists(
                &mut staged,
                theorem,
                artifact.production_binders[binder_index],
                opened,
                witnesses[binder_index],
            )
            .map_err(|source| DefinitionProofError::Exists { source })?;
            theorem = introduced.theorem;
            proposition = introduced.proposition;
        }
        join_alpha_equivalent(&mut staged, proposition, artifact.case.produces)?;
        staged.convert_conclusions(theorem, proposition, artifact.case.produces)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: artifact.case.produces,
            theorem,
            holds: true,
        })
    }

    /// Derives the complete ordered body from one checked case-branch fact.
    ///
    /// For an ordinary case the branch is `case.produces`. For an `otherwise`
    /// case it is `not prior_applicability /\ case.produces`. The method then
    /// injects that branch into the exact source-ordered disjunction. All input
    /// theorem premises remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is absent, `branch_fact` proves a different
    /// proposition, or checked alignment or disjunction introduction fails.
    /// `kernel` is unchanged on failure.
    pub fn prove_body_case(
        &self,
        kernel: &mut Kernel,
        bool_ty: Ref,
        index: usize,
        branch_fact: ThmId,
    ) -> Result<Evidence, DefinitionProofError> {
        if index >= self.cases.len() {
            return Err(DefinitionProofError::MissingCase { index });
        }
        let mut staged = kernel.fork();
        let mut prior = staged.bool(bool_ty, false)?;
        let mut body = staged.bool(bool_ty, false)?;
        let mut theorem = None;
        for (case_index, case) in self.cases.iter().enumerate() {
            let branch = if case.otherwise {
                let no_prior = staged.op1(Op1::Not, prior)?;
                staged.op2(Op2::And, no_prior, case.produces)?
            } else {
                case.produces
            };
            let next = staged.op2(Op2::Or, body, branch)?;
            if case_index == index {
                let source = definition_positive_conclusion(&staged, branch_fact)?;
                join_alpha_equivalent(&mut staged, source, branch)?;
                let selected = staged.copy_theorem(branch_fact)?;
                staged.convert_conclusions(selected, source, branch)?;
                staged.weaken(selected, &[], &[positive(body)])?;
                theorem = Some(staged.or_right(selected, positive(next))?);
            } else if let Some(selected) = theorem {
                staged.weaken(selected, &[], &[positive(branch)])?;
                theorem = Some(staged.or_right(selected, positive(next))?);
            }
            prior = staged.op2(Op2::Or, prior, case.applicable)?;
            body = next;
        }
        join_alpha_equivalent(&mut staged, body, self.body)?;
        let theorem = theorem.ok_or(DefinitionProofError::MissingCase { index })?;
        staged.convert_conclusions(theorem, body, self.body)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: self.body,
            theorem,
            holds: true,
        })
    }
}

fn instantiate_case_conditions(
    kernel: &mut Kernel,
    conditions: &[Ref],
    binders: &[Ref],
    values: &[Ref],
) -> Result<Vec<Ref>, DefinitionProofError> {
    conditions
        .iter()
        .map(|&condition| {
            binders
                .iter()
                .copied()
                .zip(values.iter().copied())
                .try_fold(condition, |proposition, (binder, value)| {
                    substitute(kernel, binder, value, proposition)
                        .map(|result| result.output)
                        .map_err(|source| DefinitionProofError::Substitute { source })
                })
        })
        .collect()
}

fn definition_positive_conclusion(
    kernel: &Kernel,
    theorem: ThmId,
) -> Result<Ref, DefinitionProofError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(DefinitionProofError::BranchFact);
    };
    if conclusions.next().is_some() || !literal.is_positive() {
        return Err(DefinitionProofError::BranchFact);
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(DefinitionProofError::BranchFact)
}

/// Why a retained definition case could not be specialized or proved.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum DefinitionProofError {
    /// Concrete inputs did not match the definition arity.
    #[snafu(display("definition has {expected} inputs, found {actual}"))]
    Arity {
        /// Required input count.
        expected: usize,
        /// Supplied input count.
        actual: usize,
    },
    /// The selected source case is absent.
    #[snafu(display("definition has no case at index {index}"))]
    MissingCase {
        /// Requested source-order index.
        index: usize,
    },
    /// Production witnesses did not match the retained existential arity.
    #[snafu(display("definition production has {expected} witnesses, found {actual}"))]
    WitnessArity {
        /// Required witness count.
        expected: usize,
        /// Supplied witness count.
        actual: usize,
    },
    /// Condition facts did not match the production conjunction arity.
    #[snafu(display("definition production has {expected} conditions, found {actual} facts"))]
    ConditionArity {
        /// Required condition count.
        expected: usize,
        /// Supplied fact count.
        actual: usize,
    },
    /// A row tagged as equality did not have its checked three-child shape.
    #[snafu(display("malformed elementary definition equality"))]
    ConditionShape,
    /// The supplied theorem is not one positive case-branch fact.
    #[snafu(display("theorem does not prove the selected definition branch"))]
    BranchFact,
    /// Checked capture-avoiding specialization failed.
    #[snafu(display("could not specialize a retained definition case: {source}"))]
    Substitute {
        /// Underlying checked substitution failure.
        source: ModelError,
    },
    /// Checked existential introduction failed.
    #[snafu(display("could not introduce a retained definition witness: {source}"))]
    Exists {
        /// Underlying checked existential proof failure.
        source: ExistsError,
    },
    /// Checked syntax alignment failed.
    #[snafu(display("could not align a retained definition case: {source}"))]
    Syntax {
        /// Underlying checked syntax failure.
        source: SyntaxError,
    },
    /// A checked HOL construction or theorem rule failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

impl From<SyntaxError> for DefinitionProofError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

/// Proves an elementary definition condition when it is reflexive equality.
///
/// This recognizes only checked equality syntax whose two operands are
/// structurally identical (up to already checked syntax sharing). It performs
/// no evaluation. Non-equalities and genuinely different operands return
/// `Ok(None)` and remain explicit semantic obligations.
///
/// # Errors
///
/// Returns an error if malformed equality syntax or a checked syntax/theorem
/// operation fails. `kernel` is unchanged on both failure and `Ok(None)`.
pub fn prove_reflexive_condition(
    kernel: &mut Kernel,
    condition: Ref,
) -> Result<Option<Evidence>, DefinitionProofError> {
    if kernel.arena().tag(condition) != Some(Tag::Tm(covalence_logic_hol::TmTag::Eq)) {
        return Ok(None);
    }
    let children = kernel
        .arena()
        .children(condition)
        .ok_or(DefinitionProofError::ConditionShape)?
        .collect::<Vec<_>>();
    let [_operand_ty, left, right] = children.as_slice() else {
        return Err(DefinitionProofError::ConditionShape);
    };
    let mut staged = kernel.fork();
    match covalence_logic_hol_derived::join_same_syntax(&mut staged, *left, *right) {
        Ok(_) => {}
        Err(SyntaxError::Different) => return Ok(None),
        Err(SyntaxError::Kernel { source }) => {
            return Err(DefinitionProofError::Kernel { source });
        }
    }
    let bool_ty = staged.classifier(condition)?;
    let reflexive = staged.refl(bool_ty, *left)?;
    covalence_logic_hol_derived::join_same_syntax(&mut staged, reflexive.equality, condition)?;
    staged.convert_conclusions(reflexive.theorem, reflexive.equality, condition)?;
    *kernel = staged;
    Ok(Some(Evidence {
        proposition: condition,
        theorem: reflexive.theorem,
        holds: true,
    }))
}

/// Minimal inputs for lowering one complete checked definition schema.
#[derive(Clone, Copy, Debug)]
pub struct RelationalDefinitionSchema<'a> {
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Checked graph-predicate slot declared by the generic schema.
    pub predicate: Ref,
    /// Exact decoded clauses in source order.
    pub clauses: &'a [IlClauseSchema<'a>],
    /// Existing interpretation roots whose free-variable names are reserved.
    pub avoid: &'a [Ref],
}

/// Inputs selecting one complete definition graph constraint.
#[derive(Clone, Copy, Debug)]
pub struct RelationalDefinitionSource<'a> {
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Candidate graph predicate supplied by the checked schema.
    pub predicate: Ref,
    /// Universally quantified declaration inputs.
    pub formal_inputs: &'a [Ref],
    /// Universally quantified graph result.
    pub formal_result: Ref,
    /// Decoded clauses in exact source order.
    pub clauses: &'a [IlClauseSchema<'a>],
    /// First deterministic name available to clause-local lowering.
    pub first_name: u64,
}

/// One member of a mutually recursive relation group.
#[derive(Clone, Copy, Debug)]
pub struct RelationalRelation<'a> {
    /// Exact relation name used by nested rule premises.
    pub name: &'a str,
    /// Checked semantic-predicate slot declared by the generic schema.
    pub predicate: Ref,
    /// Decoded source rules in exact order.
    pub rules: &'a [IlRuleSchema<'a>],
}

/// Exact definition of one schema relation slot by a least-family member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalRelationDefinition {
    /// Free semantic slot supplied by the checked schema.
    pub predicate: Ref,
    /// Direct impredicative least predicate generated from the relation rules.
    pub least: LeastPredicate,
    /// Source-ordered universally closed rule propositions for this member.
    pub rules: Arc<[Ref]>,
    /// Source-ordered lowered rule ingredients before universal closure.
    pub rule_schemas: Arc<[HolRule]>,
    /// Source-ordered rules for the complete mutually recursive family.
    pub family_rules: Arc<[Ref]>,
    /// Candidate predicates quantified by the least-family definition.
    pub family_candidates: Arc<[Ref]>,
    /// Checked proposition `predicate = least.predicate`.
    pub equation: Ref,
}

impl RelationalRelationDefinition {
    /// Derives one member rule from the complete family closure.
    ///
    /// The resulting theorem has `least.closure` as its single visible premise
    /// and the selected universally closed rule as its conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is absent, the retained rule is inconsistent
    /// with the family closure, or a checked theorem step fails. `kernel` is
    /// unchanged on failure.
    pub fn derive_rule(
        &self,
        kernel: &mut Kernel,
        index: usize,
    ) -> Result<Evidence, RelationProofError> {
        let target = *self
            .rules
            .get(index)
            .ok_or(RelationProofError::Missing { index })?;
        let family_index = self
            .family_rules
            .iter()
            .position(|&rule| rule == target)
            .ok_or(RelationProofError::Inconsistent)?;
        let mut staged = kernel.fork();
        let mut theorem = staged.identity(positive(target))?;
        for (candidate_index, &rule) in self.family_rules.iter().enumerate() {
            if candidate_index != family_index {
                staged.weaken(theorem, &[positive(rule)], &[])?;
            }
        }
        if self.family_rules.len() > 1 {
            theorem = staged.fold_premise(theorem, positive(self.least.closure))?;
        } else if self.family_rules.first().copied() != Some(self.least.closure) {
            return Err(RelationProofError::Inconsistent);
        }
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem,
            holds: true,
        })
    }

    /// Derives and specializes one member rule at checked arguments.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`derive_rule`](Self::derive_rule), or if an argument does not match the
    /// next universal binder. `kernel` is unchanged on failure.
    pub fn specialize_rule(
        &self,
        kernel: &mut Kernel,
        index: usize,
        arguments: &[Ref],
    ) -> Result<Evidence, RelationProofError> {
        let mut staged = kernel.fork();
        let mut evidence = self.derive_rule(&mut staged, index)?;
        for &argument in arguments {
            let specialized = forall_elim(&mut staged, evidence.theorem, argument)
                .map_err(|source| RelationProofError::Specialize { source })?;
            evidence = Evidence {
                proposition: specialized.proposition,
                theorem: specialized.theorem,
                holds: true,
            };
        }
        *kernel = staged;
        Ok(evidence)
    }

    /// Applies a fully specialized member rule to its checked premise fact.
    ///
    /// `rule` is normally returned by [`Self::specialize_rule`] after passing
    /// one argument for every retained [`HolRule::binders`] entry. Its theorem
    /// must conclude `premises -> candidate conclusion` under the family
    /// closure. The result concludes `candidate conclusion`, preserving both
    /// the closure and all premises of `premises_fact` visibly.
    ///
    /// # Errors
    ///
    /// Returns an error unless `rule` is a positive implication and
    /// `premises_fact` proves its exact antecedent, or a checked theorem step
    /// fails. `kernel` is unchanged on failure.
    pub fn apply_specialized_rule(
        &self,
        kernel: &mut Kernel,
        rule: Evidence,
        premises_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, RelationProofError> {
        if !rule.holds || kernel.arena().op2(rule.proposition) != Some(Op2::Imp) {
            return Err(RelationProofError::NotImplication);
        }
        let mut operands = kernel
            .arena()
            .children(rule.proposition)
            .ok_or(RelationProofError::NotImplication)?;
        let antecedent = operands.next().ok_or(RelationProofError::NotImplication)?;
        let consequent = operands.next().ok_or(RelationProofError::NotImplication)?;
        drop(operands);
        let mut staged = kernel.fork();
        let premise_source = sole_positive_conclusion(&staged, premises_fact)?;
        join_alpha_equivalent(&mut staged, premise_source, antecedent)
            .map_err(|source| RelationProofError::Syntax { source })?;
        let aligned_premises = staged.copy_theorem(premises_fact)?;
        staged.convert_conclusions(aligned_premises, premise_source, antecedent)?;
        let consequence_identity = staged.identity(positive(consequent))?;
        let use_rule = staged.imp_left(
            aligned_premises,
            consequence_identity,
            positive(rule.proposition),
        )?;
        let theorem = staged.cut(rule.theorem, use_rule, positive(rule.proposition))?;
        *kernel = staged;
        Ok(Evidence {
            proposition: consequent,
            theorem,
            holds: true,
        })
    }

    /// Closes a candidate rule fact into the public least-defined relation.
    ///
    /// `candidate_fact` must conclude this member candidate applied to the
    /// single erased relation argument, with the shared family closure as a
    /// premise. `equation_fact` must prove this relation's checked defining
    /// equation. Other visible premises, such as grounding laws, are retained.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed candidate fact, a candidate-dependent
    /// residual premise, a mismatched defining equation, or a rejected checked
    /// quantification, beta-conversion, or equality step. `kernel` is unchanged
    /// on failure.
    pub fn close_rule_instance(
        &self,
        kernel: &mut Kernel,
        candidate_fact: Evidence,
        equation_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, RelationProofError> {
        if !candidate_fact.holds {
            return Err(RelationProofError::CandidateFact);
        }
        let mut candidate_children = kernel
            .arena()
            .children(candidate_fact.proposition)
            .ok_or(RelationProofError::CandidateFact)?;
        let function = candidate_children
            .next()
            .ok_or(RelationProofError::CandidateFact)?;
        let argument = candidate_children
            .next()
            .ok_or(RelationProofError::CandidateFact)?;
        drop(candidate_children);
        if function != self.least.candidate {
            return Err(RelationProofError::CandidateFact);
        }

        let mut staged = kernel.fork();
        let implication = staged.op2(Op2::Imp, self.least.closure, candidate_fact.proposition)?;
        let mut theorem = staged.copy_theorem(candidate_fact.theorem)?;
        theorem = staged.imp_right(theorem, positive(implication))?;
        let mut characterization = implication;
        for &candidate in self.family_candidates.iter().rev() {
            let bool_ty = staged.classifier(characterization)?;
            characterization = staged.forall_tm(bool_ty, candidate, characterization)?;
            theorem = staged.forall_intro_at(theorem, candidate, characterization)?;
        }

        let least_application = staged.app(self.least.predicate, argument)?;
        let mut lambda_children = staged
            .arena()
            .children(self.least.predicate)
            .ok_or(RelationProofError::CandidateFact)?;
        let binder = lambda_children
            .next()
            .ok_or(RelationProofError::CandidateFact)?;
        let body = lambda_children
            .next()
            .ok_or(RelationProofError::CandidateFact)?;
        drop(lambda_children);
        let reduced = substitute(&mut staged, binder, argument, body)
            .map_err(|source| RelationProofError::Substitute { source })?;
        let beta = staged.tm_beta_fact(None, least_application, reduced.fact)?;
        staged.union_syn_fact(beta)?;
        join_alpha_equivalent(&mut staged, characterization, reduced.output)
            .map_err(|source| RelationProofError::Syntax { source })?;
        staged.convert_conclusions(theorem, characterization, least_application)?;

        let equation_source = sole_positive_conclusion(&staged, equation_fact)?;
        join_alpha_equivalent(&mut staged, equation_source, self.equation)
            .map_err(|source| RelationProofError::Syntax { source })?;
        let aligned_equation = staged.copy_theorem(equation_fact)?;
        staged.convert_conclusions(aligned_equation, equation_source, self.equation)?;
        let applied_equation = staged.ap_thm(aligned_equation, argument)?;
        join_alpha_equivalent(&mut staged, least_application, applied_equation.right)
            .map_err(|source| RelationProofError::Syntax { source })?;
        staged.convert_conclusions(theorem, least_application, applied_equation.right)?;
        let bool_ty = staged.classifier(applied_equation.left)?;
        let reversed = equality_symmetry(&mut staged, bool_ty, applied_equation.theorem)
            .map_err(|source| RelationProofError::Equality { source })?;
        let theorem = staged.eq_mp(reversed.theorem, theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: applied_equation.left,
            theorem,
            holds: true,
        })
    }
}

fn sole_positive_conclusion(
    kernel: &Kernel,
    theorem: covalence_logic_hol::ThmId,
) -> Result<Ref, RelationProofError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(RelationProofError::PremiseFact);
    };
    if conclusions.next().is_some() || !literal.is_positive() {
        return Err(RelationProofError::PremiseFact);
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(RelationProofError::PremiseFact)
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

/// Why a checked relation rule could not be derived or specialized.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum RelationProofError {
    /// The member has no rule at the requested source index.
    #[snafu(display("SpecTec relation rule index {index} is absent"))]
    Missing {
        /// Requested member-local rule index.
        index: usize,
    },
    /// Retained member and family rule metadata disagree.
    #[snafu(display("retained SpecTec relation rules are inconsistent with their closure"))]
    Inconsistent,
    /// The specialized rule is not a positive implication.
    #[snafu(display("specialized SpecTec relation rule is not an implication"))]
    NotImplication,
    /// The supplied premise theorem is not one positive fact.
    #[snafu(display("SpecTec relation rule premises are not one positive fact"))]
    PremiseFact,
    /// The supplied fact is not an application of this least-family candidate.
    #[snafu(display("SpecTec relation candidate fact has the wrong shape"))]
    CandidateFact,
    /// A checked theorem step failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(display("could not specialize a SpecTec relation rule: {source}"))]
    Specialize {
        /// Underlying checked derived-rule failure.
        source: ForallError,
    },
    /// A supplied premise fact could not be aligned with the rule antecedent.
    #[snafu(display("could not align SpecTec relation rule premises: {source}"))]
    Syntax {
        /// Underlying checked syntax failure.
        source: SyntaxError,
    },
    /// Capture-avoiding beta substitution failed.
    #[snafu(display("could not beta-reduce a least SpecTec relation: {source}"))]
    Substitute {
        /// Underlying checked substitution failure.
        source: ModelError,
    },
    /// Equality transport from the least predicate to the public relation failed.
    #[snafu(display("could not rewrite a least SpecTec relation fact: {source}"))]
    Equality {
        /// Underlying checked derived equality failure.
        source: EqualityError,
    },
}

impl RelationalCondition {
    /// Constructs a lowered premise condition.
    #[must_use]
    pub const fn new(binders: Vec<Ref>, premises: Vec<Ref>, otherwise: bool) -> Self {
        Self {
            binders,
            premises,
            otherwise,
        }
    }

    /// Returns fresh variables introduced by relational subexpressions.
    #[must_use]
    pub fn binders(&self) -> &[Ref] {
        &self.binders
    }

    /// Returns checked Boolean propositions in source order.
    #[must_use]
    pub fn premises(&self) -> &[Ref] {
        &self.premises
    }

    /// Returns whether this subtree contains `otherwise`.
    #[must_use]
    pub const fn otherwise(&self) -> bool {
        self.otherwise
    }

    fn append(&mut self, other: &Self) {
        self.binders.extend_from_slice(&other.binders);
        self.premises.extend_from_slice(&other.premises);
        self.otherwise |= other.otherwise;
    }
}

impl RelationalTerm {
    /// Constructs an already-lowered relational term.
    #[must_use]
    pub const fn new(value: Ref, binders: Vec<Ref>, premises: Vec<Ref>) -> Self {
        Self {
            value,
            binders,
            premises,
        }
    }

    /// Returns the checked value term.
    #[must_use]
    pub const fn value(&self) -> Ref {
        self.value
    }

    /// Returns fresh result variables introduced by partial calls.
    #[must_use]
    pub fn binders(&self) -> &[Ref] {
        &self.binders
    }

    /// Returns graph premises required to produce the value.
    #[must_use]
    pub fn premises(&self) -> &[Ref] {
        &self.premises
    }
}

/// Composes lowered terms and extra premises into one HOL closure rule.
///
/// Terms appear in exact conclusion-argument order. Their fresh binders and
/// graph dependencies are accumulated before caller-supplied semantic
/// premises, preserving deterministic source order.
#[must_use]
pub fn relational_hol_rule(
    explicit_binders: &[Ref],
    conclusion: &[RelationalTerm],
    semantic_premises: &[Ref],
) -> HolRule {
    let mut binders = explicit_binders.to_vec();
    let mut premises = Vec::new();
    let mut arguments = Vec::with_capacity(conclusion.len());
    for term in conclusion {
        arguments.push(term.value);
        binders.extend_from_slice(&term.binders);
        premises.extend_from_slice(&term.premises);
    }
    premises.extend_from_slice(semantic_premises);
    HolRule::new(binders, premises, arguments)
}

/// Builds one exact ordered graph case from lowered clause terms.
///
/// Applicability includes pattern matching, pattern dependencies, and semantic
/// premises, but deliberately excludes evaluation of the right-hand side. A
/// selected partial clause therefore still blocks a later `otherwise` clause.
/// Production additionally requires right-hand-side dependencies and equality
/// with `formal_result`. All clause-local and relationally introduced values
/// are existentially closed.
///
/// # Errors
///
/// Returns an error when pattern and formal-input arities differ, an equality
/// is ill-typed, a premise is not Boolean, or existential construction fails.
pub fn relational_hol_case(
    kernel: &mut Kernel,
    bool_ty: Ref,
    clause: &RelationalClause<'_>,
) -> Result<HolCase, RelationalCaseError> {
    relational_hol_case_artifact(kernel, bool_ty, clause).map(|artifact| artifact.case)
}

fn relational_hol_case_artifact(
    kernel: &mut Kernel,
    bool_ty: Ref,
    clause: &RelationalClause<'_>,
) -> Result<RelationalCaseArtifact, RelationalCaseError> {
    if clause.formal_inputs.len() != clause.patterns.len() {
        return Err(RelationalCaseError::Arity {
            expected: clause.formal_inputs.len(),
            actual: clause.patterns.len(),
        });
    }

    let mut locals = clause.explicit_locals.to_vec();
    let mut applicability = Vec::new();
    for (index, (&formal, pattern)) in clause.formal_inputs.iter().zip(clause.patterns).enumerate()
    {
        locals.extend_from_slice(pattern.binders());
        applicability.extend_from_slice(pattern.premises());
        applicability.push(
            kernel
                .eq(bool_ty, formal, pattern.value())
                .map_err(|source| RelationalCaseError::Pattern {
                    index,
                    formal,
                    pattern: pattern.value(),
                    source,
                })?,
        );
    }
    locals.extend_from_slice(clause.semantic_binders);
    applicability.extend_from_slice(clause.semantic_premises);
    let applicable = existential_case(kernel, bool_ty, &locals, &applicability)
        .map_err(|source| RelationalCaseError::Kernel { source })?;

    let mut production_locals = locals.clone();
    production_locals.extend_from_slice(clause.result.binders());
    let mut production = applicability.clone();
    production.extend_from_slice(clause.result.premises());
    production.push(
        kernel
            .eq(bool_ty, clause.formal_result, clause.result.value())
            .map_err(|source| RelationalCaseError::Result {
                formal: clause.formal_result,
                result: clause.result.value(),
                source,
            })?,
    );
    let produces = existential_case(kernel, bool_ty, &production_locals, &production)
        .map_err(|source| RelationalCaseError::Kernel { source })?;

    let case = HolCase {
        applicable,
        produces,
        otherwise: clause.otherwise,
    };
    Ok(RelationalCaseArtifact {
        case,
        pattern_values: clause.patterns.iter().map(RelationalTerm::value).collect(),
        result_value: clause.result.value(),
        applicable_binders: locals,
        applicable_conditions: applicability,
        production_binders: production_locals,
        production_conditions: production,
    })
}

/// Supplies environment-dependent leaves and primitive meanings.
pub trait RelationalResolver {
    /// Lowering failure type.
    type Error;

    /// Attaches the structural declaration selector to a lowering failure.
    fn declaration_error(&mut self, id: DeclarationId, source: Self::Error) -> Self::Error;

    /// Creates an isolated clause-local resolver retaining global meanings.
    #[must_use]
    fn clause_scope(&mut self) -> Self
    where
        Self: Sized;

    /// Restores global resolver state after an isolated clause has completed.
    fn restore_scope(&mut self, scope: Self)
    where
        Self: Sized;

    /// Establishes any lexical bindings introduced by an expression before
    /// its semantic children are visited.
    ///
    /// # Errors
    ///
    /// Returns an error when the expression scope cannot be established.
    fn enter_expression(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpression<'_>,
    ) -> Result<(), Self::Error>;

    /// Restores the environment after [`enter_expression`](Self::enter_expression).
    ///
    /// # Errors
    ///
    /// Returns an error when the expression scope cannot be restored.
    fn leave_expression(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error>;

    /// Returns fresh binders introduced by the current expression scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the active scope cannot supply its binders.
    fn expression_binders(
        &mut self,
        expression: &IlExpression<'_>,
    ) -> Result<Vec<Ref>, Self::Error>;

    /// Creates a resolver scope binding a complete recursive relation family.
    #[must_use]
    fn relation_scope(&mut self, candidates: &[(&str, Ref)]) -> Self
    where
        Self: Sized;

    /// Converts a structural schema failure.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Converts a checked kernel failure.
    fn kernel_error(&mut self, source: KernelError) -> Self::Error;

    /// Reports exhaustion of the caller-selected name range.
    fn name_exhausted(&mut self) -> Self::Error;

    /// Converts exact-clause assembly failure.
    fn case_error(&mut self, source: RelationalCaseError) -> Self::Error;

    /// Converts least-family construction failure.
    fn least_error(&mut self, source: LeastPredicateError) -> Self::Error;

    /// Converts exact predicate-family assembly failure.
    fn family_error(&mut self, source: HolFamilyError) -> Self::Error;

    /// Converts complete-theory coverage or conjunction failure.
    fn theory_error(&mut self, source: HolTheoryError) -> Self::Error;

    /// Registers one checked term for an explicit IL binding.
    ///
    /// # Errors
    ///
    /// Returns an error for duplicate names or a target classifier incompatible
    /// with the binding category.
    fn binding(&mut self, binding: &IlBinding<'_>, reference: Ref) -> Result<(), Self::Error>;

    /// Produces the semantic well-formedness premise for one registered
    /// binding, if its category requires one.
    ///
    /// Expression bindings normally return membership in their decoded IL
    /// type. Higher-order/type bindings may return `None` when their checked
    /// classifier already expresses the complete requirement.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-membership or checked application failure.
    fn binding_premise(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
        reference: Ref,
    ) -> Result<Option<Ref>, Self::Error>;

    /// Resolves the checked classifier of one explicit IL binding.
    ///
    /// # Errors
    ///
    /// Returns an error when its IL type or higher-order signature cannot be
    /// embedded in the selected HOL representation.
    fn binding_type(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Resolves one variable expression to a checked term.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound variable or incompatible target term.
    fn variable(&mut self, kernel: &mut Kernel, name: &str) -> Result<Ref, Self::Error>;

    /// Resolves one non-expression type, definition, or grammar argument.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound higher-order name, unresolved type
    /// family argument, or incompatible checked classifier.
    fn argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Resolves a non-expression clause pattern with access to its formal.
    ///
    /// Higher-order shorthand patterns can use `formal` as their lexical
    /// binding. Other arguments use the ordinary argument interpretation.
    ///
    /// # Errors
    ///
    /// Returns an error when the pattern cannot be resolved at the formal.
    fn pattern_argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
        _formal: Ref,
    ) -> Result<Ref, Self::Error> {
        self.argument(kernel, argument)
    }

    /// Applies the HOL membership interpretation of one decoded IL type.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved type family or an ill-typed checked
    /// predicate application.
    fn type_membership(
        &mut self,
        kernel: &mut Kernel,
        ty: &covalence_data_spectec::IlType<'_>,
        value: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Resolves the checked classifier used for a witness of one IL type.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected type embedding cannot classify the
    /// witness.
    fn type_classifier(
        &mut self,
        kernel: &mut Kernel,
        ty: &covalence_data_spectec::IlType<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Constructs the interpreted value of a tuple payload.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable tuple interpretation or rejected
    /// checked application.
    fn tuple_value(&mut self, kernel: &mut Kernel, elements: &[Ref]) -> Result<Ref, Self::Error>;

    /// Constructs one interpreted tagged-variant value.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable constructor interpretation or
    /// rejected checked application.
    fn variant_value(
        &mut self,
        kernel: &mut Kernel,
        constructor: &str,
        payload: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Constructs one interpreted record value from exact field names/order.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable record interpretation or rejected
    /// checked application.
    fn struct_value(
        &mut self,
        kernel: &mut Kernel,
        fields: &[(&str, Ref)],
    ) -> Result<Ref, Self::Error>;

    /// Interprets one grammar-symbol constructor from its already-lowered
    /// semantic children.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved grammar constructor/reference or a
    /// rejected checked application.
    fn grammar_value(
        &mut self,
        kernel: &mut Kernel,
        symbol: &covalence_data_spectec::IlGrammarSymbol<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error>;

    /// Reports an `otherwise` marker in a structural type side condition.
    fn type_otherwise(&mut self) -> Self::Error;

    /// Reports an `otherwise` marker in a grammar-production side condition.
    fn grammar_otherwise(&mut self) -> Self::Error;

    /// Lowers one non-variable, non-call constructor from child values.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved primitive or rejected checked
    /// construction.
    fn operation(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpressionView<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error>;

    /// Resolves a call and applies all explicit arguments, returning a graph
    /// predicate prefix that accepts one fresh result value.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved definition, unsupported
    /// higher-order argument, arity mismatch, or rejected checked application.
    fn call(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        arguments: &[IlArgument<'_>],
        expression_arguments: &[Ref],
    ) -> Result<RelationalCall, Self::Error>;

    /// Applies a named relation to its lowered single argument.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown relation or ill-typed application.
    fn relation(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        argument: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Lowers an iterated premise after its repeated condition and domain
    /// expressions have been lowered.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected value representation cannot express
    /// the iteration or its named domains.
    fn iterated_premise(
        &mut self,
        kernel: &mut Kernel,
        iteration: &IlIteration<'_>,
        domains: &[(&str, RelationalTerm)],
        repeated: RelationalCondition,
    ) -> Result<RelationalCondition, Self::Error>;

    /// Reports nested relation-premise binders unsupported by this lowering.
    fn nested_premise_bindings(&mut self, count: usize) -> Self::Error;

    /// Reports an `otherwise` marker in an inductive relation rule.
    fn relation_otherwise(&mut self) -> Self::Error;
}

/// Transactionally lowers a complete ordered definition to one exact graph
/// equation.
///
/// Each clause receives a fresh resolver scope, preventing pattern bindings
/// from leaking between siblings. `formal_inputs` and `formal_result` are
/// universally closed in predicate-application order.
///
/// # Errors
///
/// Returns the first clause-lowering or checked HOL failure through the
/// resolver's typed error vocabulary. `kernel` is unchanged on failure.
pub fn relational_definition<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &RelationalDefinitionSource<'_>,
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let mut case_artifacts = Vec::with_capacity(source.clauses.len());
    let mut next_name = source.first_name;
    for clause in source.clauses {
        let clause_resolver = resolver.clause_scope();
        let mut algebra = RelationalExpressionAlgebra::new(
            &mut staged,
            clause_resolver,
            source.bool_ty,
            next_name,
        );
        case_artifacts.push(algebra.clause_artifact(
            clause,
            source.formal_inputs,
            source.formal_result,
        )?);
        next_name = algebra.next_name();
        resolver.restore_scope(algebra.into_resolver());
    }
    let cases = case_artifacts
        .iter()
        .map(|artifact| artifact.case)
        .collect::<Vec<_>>();
    let body = crate::ordered_cases(&mut staged, source.bool_ty, &cases)
        .map_err(|source| resolver.kernel_error(source))?;
    let mut arguments = source.formal_inputs.to_vec();
    arguments.push(source.formal_result);
    let equation = crate::close_graph_equation(
        &mut staged,
        source.bool_ty,
        source.predicate,
        &arguments,
        &arguments,
        body,
    )
    .map_err(|source| resolver.kernel_error(source))?;
    *kernel = staged;
    Ok(RelationalDefinition {
        formal_inputs: source.formal_inputs.to_vec(),
        formal_result: source.formal_result,
        cases,
        case_artifacts,
        body,
        equation,
        next_name,
    })
}

/// Derives a definition's formal inputs, result, and fresh-name range directly
/// from its checked schema slot, then lowers every decoded clause.
///
/// This is the whole-schema entry point. [`relational_definition`] remains the
/// lower-level form for callers that already own formal variables.
///
/// # Errors
///
/// Returns an error when the slot is not a curried graph predicate with at
/// least a result argument, name allocation fails, or clause lowering fails.
/// `kernel` is unchanged on failure.
pub fn relational_definition_schema<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &RelationalDefinitionSchema<'_>,
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let classifier = staged
        .classifier(source.predicate)
        .map_err(|error| resolver.kernel_error(error))?;
    let domains = graph_domains(&staged, classifier, source.bool_ty)
        .map_err(|error| resolver.case_error(error))?;
    let Some((result_type, input_types)) = domains.split_last() else {
        return Err(resolver.case_error(RelationalCaseError::NotGraph));
    };
    let roots = std::iter::once(source.predicate)
        .chain(std::iter::once(source.bool_ty))
        .chain(source.avoid.iter().copied())
        .collect::<Vec<_>>();
    let mut next_name = staged
        .fresh_name(&roots)
        .map_err(|error| resolver.kernel_error(error))?;
    let mut formal_inputs = Vec::with_capacity(input_types.len());
    for &input_type in input_types {
        formal_inputs.push(
            staged
                .tm_fv(next_name, input_type)
                .map_err(|error| resolver.kernel_error(error))?,
        );
        next_name = next_name
            .checked_add(1)
            .ok_or_else(|| resolver.name_exhausted())?;
    }
    let formal_result = staged
        .tm_fv(next_name, *result_type)
        .map_err(|error| resolver.kernel_error(error))?;
    next_name = next_name
        .checked_add(1)
        .ok_or_else(|| resolver.name_exhausted())?;
    let definition = relational_definition(
        &mut staged,
        resolver,
        &RelationalDefinitionSource {
            bool_ty: source.bool_ty,
            predicate: source.predicate,
            formal_inputs: &formal_inputs,
            formal_result,
            clauses: source.clauses,
            first_name: next_name,
        },
    )?;
    *kernel = staged;
    Ok(definition)
}

/// Decodes and lowers one complete definition selected from an exact source
/// and its checked generic schema.
///
/// All schema slots are reserved automatically for hygienic formal-variable
/// allocation. `avoid` adds primitive-interpretation or caller-owned roots.
///
/// # Errors
///
/// Returns an error for an absent/non-definition selector, a mismatched HOL
/// schema slot, malformed clause, or any schema-derived lowering failure.
/// `kernel` is unchanged on failure.
pub fn relational_definition_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let declaration = source
        .il()
        .schema(id)
        .map_err(|error| resolver.schema_error(error))?
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "inventoried definition declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    let target = schema.declaration(id).ok_or_else(|| {
        resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "checked HOL definition slot",
            actual: "missing schema slot".to_owned(),
        })
    })?;
    let IlDeclarationBody::Definition { clauses, .. } = declaration.body() else {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "definition declaration",
            actual: format!("{:?} declaration", target.kind()),
        }));
    };
    if target.kind() != IlKind::Definition {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "HOL definition slot",
            actual: format!("HOL {:?} slot", target.kind()),
        }));
    }
    let clauses = clauses
        .iter()
        .map(IlClauseSchema::decode)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| resolver.schema_error(error))?;
    let reserved = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    relational_definition_schema(
        kernel,
        resolver,
        &RelationalDefinitionSchema {
            bool_ty: schema.bool_ty(),
            predicate: target.reference(),
            clauses: &clauses,
            avoid: &reserved,
        },
    )
}

pub(crate) fn graph_domains(
    kernel: &Kernel,
    predicate_type: Ref,
    bool_ty: Ref,
) -> Result<Vec<Ref>, RelationalCaseError> {
    let mut domains = Vec::new();
    let mut current = predicate_type;
    while kernel.arena().tag(current) == Some(Tag::Ty(TyTag::Arr)) {
        let children = kernel
            .arena()
            .children(current)
            .ok_or(RelationalCaseError::NotGraph)?
            .collect::<Vec<_>>();
        let [domain, codomain] = children.as_slice() else {
            return Err(RelationalCaseError::NotGraph);
        };
        domains.push(*domain);
        current = *codomain;
    }
    if !kernel
        .equivalent(current, bool_ty)
        .map_err(|source| RelationalCaseError::Kernel { source })?
    {
        return Err(RelationalCaseError::NotGraph);
    }
    Ok(domains)
}

/// Transactionally lowers complete mutually recursive relation groups to their
/// simultaneous least HOL predicates.
///
/// Every nested relation premise resolves against the checked candidate family
/// during rule lowering. Rule-local bindings are isolated from sibling rules.
/// A consecutive `otherwise` chain is guarded by the negated applicability of
/// the preceding alternatives; a new unguarded rule starts a new chain.
///
/// # Errors
///
/// Returns the first candidate-family, rule-lowering, relation-resolution, or
/// checked closure failure through the resolver's typed error vocabulary.
/// `kernel` is unchanged on failure.
pub fn relational_relations<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    bool_ty: Ref,
    relations: &[RelationalRelation<'_>],
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    relational_relations_avoiding(kernel, resolver, bool_ty, relations, &[])
}

/// Lowers a complete mutually recursive relation family while reserving names
/// reachable from additional interpretation roots.
///
/// # Errors
///
/// Returns the same failures as [`relational_relations`]. `kernel` is unchanged
/// on failure.
pub fn relational_relations_avoiding<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    bool_ty: Ref,
    relations: &[RelationalRelation<'_>],
    avoid: &[Ref],
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let predicate_types = relations
        .iter()
        .map(|relation| {
            staged
                .classifier(relation.predicate)
                .map_err(|source| resolver.kernel_error(source))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let predicates = relations
        .iter()
        .map(|relation| relation.predicate)
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    let mut builder =
        begin_least_closed_family_avoiding(&mut staged, bool_ty, &predicate_types, &predicates)
            .map_err(|source| resolver.least_error(source))?;
    let mut relation_rules = Vec::with_capacity(relations.len());
    let mut relation_rule_schemas = Vec::with_capacity(relations.len());
    let (closure, family_rules, family_candidates) = {
        let (staged, candidates) = builder.parts();
        let candidate_names = relations
            .iter()
            .zip(candidates)
            .map(|(relation, &candidate)| (relation.name, candidate))
            .collect::<Vec<_>>();
        let mut scoped = resolver.relation_scope(&candidate_names);
        let roots = candidates.to_vec();
        let mut next_name = staged
            .fresh_name(&roots)
            .map_err(|source| resolver.kernel_error(source))?;
        let mut closures = Vec::new();
        for (relation, &candidate) in relations.iter().zip(candidates) {
            let first_rule = closures.len();
            let mut member_schemas = Vec::with_capacity(relation.rules.len());
            let mut preceding = None;
            for schema in relation.rules {
                let rule_resolver = scoped.clause_scope();
                let mut algebra =
                    RelationalExpressionAlgebra::new(staged, rule_resolver, bool_ty, next_name);
                let (mut rule, otherwise) = algebra.ordered_rule(schema)?;
                next_name = algebra.next_name();
                scoped.restore_scope(algebra.into_resolver());
                if otherwise {
                    if preceding.is_some_and(|guard| depends_on_any(staged, guard, candidates)) {
                        return Err(resolver.relation_otherwise());
                    }
                    let guard = ordered_rule_guard(staged, bool_ty, preceding, &rule)
                        .map_err(|source| resolver.kernel_error(source))?;
                    rule.premises.push(guard);
                }
                member_schemas.push(rule.clone());
                closures.push(
                    close_hol_rule(staged, bool_ty, candidate, &rule)
                        .map_err(|source| resolver.kernel_error(source))?,
                );
                let preceding_chain = if otherwise { preceding } else { None };
                preceding = Some(
                    extend_ordered_applicability(staged, bool_ty, preceding_chain, &rule)
                        .map_err(|source| resolver.kernel_error(source))?,
                );
            }
            relation_rules.push(Arc::from(&closures[first_rule..]));
            relation_rule_schemas.push(Arc::from(member_schemas));
        }
        let closure = close_hol_rules(staged, bool_ty, &closures)
            .map_err(|source| resolver.kernel_error(source))?;
        let family_rules = Arc::from(closures);
        resolver.restore_scope(scoped);
        (closure, family_rules, Arc::from(candidates))
    };
    let family = builder
        .finish(closure)
        .map_err(|source| resolver.least_error(source))?;
    let definitions = relations
        .iter()
        .zip(family)
        .zip(relation_rules)
        .zip(relation_rule_schemas)
        .map(|(((relation, least), rules), rule_schemas)| {
            staged
                .eq(bool_ty, relation.predicate, least.predicate)
                .map(|equation| RelationalRelationDefinition {
                    predicate: relation.predicate,
                    least,
                    rules,
                    rule_schemas,
                    family_rules: Arc::clone(&family_rules),
                    family_candidates: Arc::clone(&family_candidates),
                    equation,
                })
                .map_err(|source| resolver.kernel_error(source))
        })
        .collect::<Result<Vec<_>, _>>()?;
    *kernel = staged;
    Ok(definitions)
}

fn depends_on_any(kernel: &Kernel, root: Ref, needles: &[Ref]) -> bool {
    let needles = needles.iter().copied().collect::<BTreeSet<_>>();
    let mut seen = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(reference) = pending.pop() {
        if needles.contains(&reference) {
            return true;
        }
        if seen.insert(reference)
            && let Some(children) = kernel.arena().children(reference)
        {
            pending.extend(children);
        }
    }
    false
}

fn ordered_rule_guard(
    kernel: &mut Kernel,
    bool_ty: Ref,
    preceding: Option<Ref>,
    current: &HolRule,
) -> Result<Ref, KernelError> {
    debug_assert_eq!(current.conclusion.len(), 1);
    let argument = current.conclusion[0];
    let Some(preceding) = preceding else {
        return kernel.bool(bool_ty, true);
    };
    let applicable = kernel.app(preceding, argument)?;
    kernel.op1(Op1::Not, applicable)
}

fn extend_ordered_applicability(
    kernel: &mut Kernel,
    bool_ty: Ref,
    preceding: Option<Ref>,
    rule: &HolRule,
) -> Result<Ref, KernelError> {
    debug_assert_eq!(rule.conclusion.len(), 1);
    let conclusion = rule.conclusion[0];
    let argument_ty = kernel.classifier(conclusion)?;
    let roots = rule
        .binders
        .iter()
        .chain(rule.premises.iter())
        .copied()
        .chain(preceding)
        .chain([conclusion, bool_ty])
        .collect::<Vec<_>>();
    let formal = kernel.tm_fv(kernel.fresh_name(&roots)?, argument_ty)?;
    let mut premises = rule.premises.clone();
    premises.push(kernel.eq(bool_ty, formal, conclusion)?);
    let current = existential_case(kernel, bool_ty, &rule.binders, &premises)?;
    let body = if let Some(preceding) = preceding {
        let prior = kernel.app(preceding, formal)?;
        kernel.op2(Op2::Or, prior, current)?
    } else {
        current
    };
    let predicate_ty = kernel.ty_arr(argument_ty, bool_ty)?;
    kernel.lam_at(predicate_ty, formal, body)
}

/// Decodes and lowers the complete recursive relation root containing `id`.
///
/// Non-relation members of a mixed recursive root are left for their respective
/// declaration lowerers. Every relation member is tied to its checked schema
/// slot, and all schema slots plus `avoid` are reserved for name hygiene.
///
/// # Errors
///
/// Returns an error when `id` is absent or not a relation, a family member has
/// no matching relation slot, relation names repeat within the root, a rule is
/// malformed, or family lowering fails. `kernel` is unchanged on failure.
#[allow(clippy::too_many_lines)] // Keeps exact root/schema checks at one authority boundary.
pub fn relational_relation_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    let selected = source
        .il()
        .declarations()
        .iter()
        .find(|declaration| declaration.id() == id)
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "inventoried relation declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    if selected.kind() != IlKind::Relation {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "relation declaration",
            actual: format!("{:?} declaration", selected.kind()),
        }));
    }
    let root = source
        .il()
        .roots()
        .iter()
        .find(|root| root.ordinal() == id.root())
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "containing relation root",
                actual: "missing root".to_owned(),
            })
        })?;
    let mut decoded = Vec::new();
    let mut names = BTreeSet::new();
    for member in source.il().root_declarations(root) {
        if member.kind() != IlKind::Relation {
            continue;
        }
        if !names.insert(member.name()) {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "unique relation name within recursive root",
                actual: format!("duplicate name {:?}", member.name()),
            }));
        }
        let declaration = source
            .il()
            .schema(member.id())
            .map_err(|error| resolver.schema_error(error))?
            .ok_or_else(|| {
                resolver.schema_error(IlSchemaError::Shape {
                    id: member.id(),
                    path: Vec::new(),
                    expected: "inventoried relation schema",
                    actual: "missing declaration".to_owned(),
                })
            })?;
        let IlDeclarationBody::Relation { rules, .. } = declaration.body() else {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "relation declaration body",
                actual: "different declaration body".to_owned(),
            }));
        };
        let target = schema.declaration(member.id()).ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "checked HOL relation slot",
                actual: "missing schema slot".to_owned(),
            })
        })?;
        if target.kind() != IlKind::Relation {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "HOL relation slot",
                actual: format!("HOL {:?} slot", target.kind()),
            }));
        }
        let rules = rules
            .iter()
            .map(IlRuleSchema::decode)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| resolver.schema_error(error))?;
        decoded.push((member.name(), target.reference(), rules));
    }
    let relations = decoded
        .iter()
        .map(|(name, predicate, rules)| RelationalRelation {
            name,
            predicate: *predicate,
            rules,
        })
        .collect::<Vec<_>>();
    let reserved = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    relational_relations_avoiding(kernel, resolver, schema.bool_ty(), &relations, &reserved)
}

/// Concrete expression algebra producing relational HOL terms.
pub struct RelationalExpressionAlgebra<'a, R> {
    kernel: &'a mut Kernel,
    resolver: R,
    bool_ty: Ref,
    next_name: u64,
    binding_premises: Vec<Ref>,
}

impl<'a, R> RelationalExpressionAlgebra<'a, R> {
    /// Starts a lowering with an explicit deterministic name range.
    #[must_use]
    pub const fn new(kernel: &'a mut Kernel, resolver: R, bool_ty: Ref, first_name: u64) -> Self {
        Self {
            kernel,
            resolver,
            bool_ty,
            next_name: first_name,
            binding_premises: Vec::new(),
        }
    }

    /// Declares and registers explicit bindings in exact source order.
    ///
    /// # Errors
    ///
    /// Returns an error on name exhaustion, rejected checked classifiers, or a
    /// resolver registration failure.
    pub fn bindings(&mut self, bindings: &[IlBinding<'_>]) -> Result<Vec<Ref>, R::Error>
    where
        R: RelationalResolver,
    {
        let mut references = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let classifier = self.resolver.binding_type(self.kernel, binding)?;
            let name = self.take_name()?;
            let reference = self
                .kernel
                .tm_fv(name, classifier)
                .map_err(|source| self.resolver.kernel_error(source))?;
            self.resolver.binding(binding, reference)?;
            if let Some(premise) = self
                .resolver
                .binding_premise(self.kernel, binding, reference)?
            {
                self.binding_premises.push(premise);
            }
            references.push(reference);
        }
        Ok(references)
    }

    /// Removes semantic premises accumulated by explicit bindings.
    #[must_use]
    pub fn take_binding_premises(&mut self) -> Vec<Ref> {
        std::mem::take(&mut self.binding_premises)
    }

    /// Lowers one heterogeneous argument as a relational term.
    ///
    /// # Errors
    ///
    /// Returns the first expression or resolver failure. Expression arguments
    /// retain introduced graph binders and premises; other categories are
    /// resolved as already checked terms.
    pub fn argument(&mut self, argument: &IlArgument<'_>) -> Result<RelationalTerm, R::Error>
    where
        R: RelationalResolver,
    {
        match argument {
            IlArgument::Expression(expression) => fold_expression(expression, self),
            IlArgument::Type(_) | IlArgument::Definition(_) | IlArgument::Grammar(_) => self
                .resolver
                .argument(self.kernel, argument)
                .map(|value| RelationalTerm::new(value, Vec::new(), Vec::new())),
        }
    }

    fn pattern_argument(
        &mut self,
        argument: &IlArgument<'_>,
        formal: Ref,
    ) -> Result<RelationalTerm, R::Error>
    where
        R: RelationalResolver,
    {
        match argument {
            IlArgument::Expression(expression) => fold_expression(expression, self),
            IlArgument::Type(_) | IlArgument::Definition(_) | IlArgument::Grammar(_) => self
                .resolver
                .pattern_argument(self.kernel, argument, formal)
                .map(|value| RelationalTerm::new(value, Vec::new(), Vec::new())),
        }
    }

    /// Applies the resolver's type-membership interpretation.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-type or checked application failure.
    pub fn type_membership(
        &mut self,
        ty: &covalence_data_spectec::IlType<'_>,
        value: Ref,
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.type_membership(self.kernel, ty, value)
    }

    /// Allocates one deterministic fresh witness of `classifier`.
    ///
    /// # Errors
    ///
    /// Returns an error on name exhaustion or rejected checked construction.
    pub fn fresh_variable(&mut self, classifier: Ref) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        let name = self.take_name()?;
        self.kernel
            .tm_fv(name, classifier)
            .map_err(|source| self.resolver.kernel_error(source))
    }

    /// Resolves the embedded classifier of one IL type.
    ///
    /// # Errors
    ///
    /// Returns an error when the resolver cannot classify the decoded type.
    pub fn type_classifier(
        &mut self,
        ty: &covalence_data_spectec::IlType<'_>,
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.type_classifier(self.kernel, ty)
    }

    /// Constructs one interpreted tuple value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-interpretation or checked application failure.
    pub fn tuple_value(&mut self, elements: &[Ref]) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.tuple_value(self.kernel, elements)
    }

    /// Constructs one interpreted variant value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-constructor or checked application failure.
    pub fn variant_value(&mut self, constructor: &str, payload: Ref) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver
            .variant_value(self.kernel, constructor, payload)
    }

    /// Constructs one interpreted struct value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-record or checked application failure.
    pub fn struct_value(&mut self, fields: &[(&str, Ref)]) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.struct_value(self.kernel, fields)
    }

    /// Constructs one interpreted grammar-symbol value.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-symbol or checked application failure.
    pub fn grammar_value(
        &mut self,
        symbol: &covalence_data_spectec::IlGrammarSymbol<'_>,
        children: &[Ref],
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.grammar_value(self.kernel, symbol, children)
    }

    /// Registers an existing term for one decoded binding.
    ///
    /// # Errors
    ///
    /// Returns a duplicate-name or incompatible-binding failure.
    pub fn register_binding(
        &mut self,
        binding: &IlBinding<'_>,
        reference: Ref,
    ) -> Result<(), R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.binding(binding, reference)?;
        if let Some(premise) = self
            .resolver
            .binding_premise(self.kernel, binding, reference)?
        {
            self.binding_premises.push(premise);
        }
        Ok(())
    }

    /// Converts an unsupported structural `otherwise` premise.
    pub fn type_otherwise(&mut self) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.type_otherwise()
    }

    /// Converts an unsupported grammar `otherwise` premise.
    pub fn grammar_otherwise(&mut self) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.grammar_otherwise()
    }

    /// Converts a structural schema failure through the resolver.
    pub fn schema_error(&mut self, source: IlSchemaError) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.schema_error(source)
    }

    /// Converts an exact family-assembly failure through the resolver.
    pub fn family_error(&mut self, source: HolFamilyError) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.family_error(source)
    }

    /// Lowers one complete definition clause to an exact ordered graph case.
    ///
    /// The algebra should be scoped to this clause so resolver bindings do not
    /// leak into a sibling clause.
    ///
    /// # Errors
    ///
    /// Returns the first binding, pattern, expression, premise, relation,
    /// iteration, arity, or checked HOL failure.
    pub fn clause(
        &mut self,
        schema: &IlClauseSchema<'_>,
        formal_inputs: &[Ref],
        formal_result: Ref,
    ) -> Result<HolCase, R::Error>
    where
        R: RelationalResolver,
    {
        self.clause_artifact(schema, formal_inputs, formal_result)
            .map(|artifact| artifact.case)
    }

    fn clause_artifact(
        &mut self,
        schema: &IlClauseSchema<'_>,
        formal_inputs: &[Ref],
        formal_result: Ref,
    ) -> Result<RelationalCaseArtifact, R::Error>
    where
        R: RelationalResolver,
    {
        let explicit_locals = self.bindings(schema.bindings())?;
        let binding_premises = self.take_binding_premises();
        let patterns = schema
            .arguments()
            .iter()
            .zip(formal_inputs)
            .map(|(argument, &formal)| self.pattern_argument(argument, formal))
            .collect::<Result<Vec<_>, _>>()?;
        let result = fold_expression(schema.result(), self)?;
        let conditions = schema
            .premises()
            .iter()
            .map(|premise| self.premise(premise))
            .collect::<Result<Vec<_>, _>>()?;
        let semantic_binders = conditions
            .iter()
            .flat_map(|condition| condition.binders().iter().copied())
            .collect::<Vec<_>>();
        let semantic_premises = binding_premises
            .into_iter()
            .chain(
                conditions
                    .iter()
                    .flat_map(|condition| condition.premises().iter().copied()),
            )
            .collect::<Vec<_>>();
        let otherwise = conditions.iter().any(RelationalCondition::otherwise);
        relational_hol_case_artifact(
            self.kernel,
            self.bool_ty,
            &RelationalClause {
                formal_inputs,
                formal_result,
                explicit_locals: &explicit_locals,
                patterns: &patterns,
                result: &result,
                semantic_binders: &semantic_binders,
                semantic_premises: &semantic_premises,
                otherwise,
            },
        )
        .map_err(|source| self.resolver.case_error(source))
    }

    /// Lowers one complete relation rule to an inductive HOL rule.
    ///
    /// # Errors
    ///
    /// Returns the first binding, conclusion, premise, relation, iteration, or
    /// checked HOL failure. `otherwise` is rejected because negative ordered
    /// fallback is not a monotone inductive rule.
    pub fn rule(&mut self, schema: &IlRuleSchema<'_>) -> Result<HolRule, R::Error>
    where
        R: RelationalResolver,
    {
        let (rule, otherwise) = self.ordered_rule(schema)?;
        if otherwise {
            return Err(self.resolver.relation_otherwise());
        }
        Ok(rule)
    }

    fn ordered_rule(&mut self, schema: &IlRuleSchema<'_>) -> Result<(HolRule, bool), R::Error>
    where
        R: RelationalResolver,
    {
        let mut binders = self.bindings(schema.bindings())?;
        let mut premises = self.take_binding_premises();
        let conclusion = fold_expression(schema.conclusion(), self)?;
        binders.extend_from_slice(conclusion.binders());
        premises.extend_from_slice(conclusion.premises());
        let mut otherwise = false;
        for premise in schema.premises() {
            let condition = self.premise(premise)?;
            otherwise |= condition.otherwise();
            binders.extend_from_slice(condition.binders());
            premises.extend_from_slice(condition.premises());
        }
        Ok((
            HolRule::new(binders, premises, vec![conclusion.value()]),
            otherwise,
        ))
    }

    /// Returns the next unused name after lowering.
    #[must_use]
    pub const fn next_name(&self) -> u64 {
        self.next_name
    }

    /// Consumes the algebra and returns its resolver.
    #[must_use]
    pub fn into_resolver(self) -> R {
        self.resolver
    }

    /// Lowers one complete premise subtree to relational HOL conditions.
    ///
    /// # Errors
    ///
    /// Returns the first expression, binding, relation, iteration, or checked
    /// HOL failure reported by the resolver.
    pub fn premise(&mut self, premise: &IlPremise<'_>) -> Result<RelationalCondition, R::Error>
    where
        R: RelationalResolver,
    {
        match premise {
            IlPremise::If(expression) => {
                let term = fold_expression(expression, self)?;
                let truth = self
                    .kernel
                    .bool(self.bool_ty, true)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let proposition = self
                    .kernel
                    .op2(covalence_logic_hol::builtin::Op2::And, truth, term.value())
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let mut premises = term.premises().to_vec();
                premises.push(proposition);
                Ok(RelationalCondition::new(
                    term.binders().to_vec(),
                    premises,
                    false,
                ))
            }
            IlPremise::Let { left, right } => {
                let left = fold_expression(left, self)?;
                let right = fold_expression(right, self)?;
                let equality = self
                    .kernel
                    .eq(self.bool_ty, left.value(), right.value())
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let mut binders = left.binders().to_vec();
                binders.extend_from_slice(right.binders());
                let mut premises = left.premises().to_vec();
                premises.extend_from_slice(right.premises());
                premises.push(equality);
                Ok(RelationalCondition::new(binders, premises, false))
            }
            IlPremise::Otherwise => Ok(RelationalCondition::new(Vec::new(), Vec::new(), true)),
            IlPremise::Rule(rule) => {
                if !rule.bindings().is_empty() {
                    return Err(self.resolver.nested_premise_bindings(rule.bindings().len()));
                }
                let conclusion = fold_expression(rule.conclusion(), self)?;
                let relation =
                    self.resolver
                        .relation(self.kernel, rule.name(), conclusion.value())?;
                let mut condition = RelationalCondition::new(
                    conclusion.binders().to_vec(),
                    conclusion.premises().to_vec(),
                    false,
                );
                condition.premises.push(relation);
                for nested in rule.premises() {
                    let nested = self.premise(nested)?;
                    condition.append(&nested);
                }
                Ok(condition)
            }
            IlPremise::Iterated {
                premise,
                iteration,
                domains,
            } => {
                let repeated = self.premise(premise)?;
                let domains = domains
                    .iter()
                    .map(|domain| self.lower_domain(domain))
                    .collect::<Result<Vec<_>, _>>()?;
                self.resolver
                    .iterated_premise(self.kernel, iteration, &domains, repeated)
            }
        }
    }

    fn lower_domain<'b>(
        &mut self,
        domain: &'b IlDomain<'b>,
    ) -> Result<(&'b str, RelationalTerm), R::Error>
    where
        R: RelationalResolver,
    {
        Ok((domain.name(), fold_expression(domain.expression(), self)?))
    }

    fn take_name(&mut self) -> Result<u64, R::Error>
    where
        R: RelationalResolver,
    {
        let name = self.next_name;
        self.next_name = self
            .next_name
            .checked_add(1)
            .ok_or_else(|| self.resolver.name_exhausted())?;
        Ok(name)
    }
}

impl<R: RelationalResolver> ExpressionAlgebra for RelationalExpressionAlgebra<'_, R> {
    type Term = RelationalTerm;
    type Error = R::Error;

    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
        self.resolver.schema_error(source)
    }

    fn enter(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        self.resolver.enter_expression(self.kernel, expression)
    }

    fn leave(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        self.resolver.leave_expression(expression)
    }

    fn expression(
        &mut self,
        expression: &IlExpression<'_>,
        children: Vec<Self::Term>,
    ) -> Result<Self::Term, Self::Error> {
        let mut binders = Vec::new();
        let mut premises = Vec::new();
        let mut values = Vec::with_capacity(children.len());
        for child in children {
            values.push(child.value);
            binders.extend(child.binders);
            premises.extend(child.premises);
        }
        let view = expression
            .view()
            .map_err(|source| self.resolver.schema_error(source))?;
        let value = match &view {
            IlExpressionView::Variable(name) => self.resolver.variable(self.kernel, name)?,
            IlExpressionView::Call { name, arguments } => {
                let call = self.resolver.call(self.kernel, name, arguments, &values)?;
                let name = self.take_name()?;
                let result = self
                    .kernel
                    .tm_fv(name, call.result_type)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let premise = self
                    .kernel
                    .app(call.predicate, result)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                binders.push(result);
                premises.push(premise);
                result
            }
            _ => self.resolver.operation(self.kernel, &view, &values)?,
        };
        binders.extend(self.resolver.expression_binders(expression)?);
        Ok(RelationalTerm::new(value, binders, premises))
    }
}
