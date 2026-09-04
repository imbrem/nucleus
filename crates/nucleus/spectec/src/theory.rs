//! Exact HOL model constraints for ordered and potentially non-monotone definitions.

use std::collections::{BTreeMap, BTreeSet};

use covalence_data_spectec::DeclarationId;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    EqualityError, ForallError, SyntaxError, equality_symmetry, forall_elim, join_alpha_equivalent,
};

use crate::{Evidence, Source};

/// A complete source-ordered set of declaration constraints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HolTheory {
    constraints: Vec<(DeclarationId, Ref)>,
    conjunctions: Vec<Ref>,
    proposition: Ref,
}

impl HolTheory {
    /// Returns declaration constraints in exact elaborated source order.
    #[must_use]
    pub fn constraints(&self) -> &[(DeclarationId, Ref)] {
        &self.constraints
    }

    /// Returns their checked conjunction.
    #[must_use]
    pub const fn proposition(&self) -> Ref {
        self.proposition
    }

    /// Derives one declaration constraint from the complete theory conjunction.
    ///
    /// The returned theorem has the single visible premise `self.proposition`
    /// and the selected constraint as its single positive conclusion. No axiom
    /// or frontend fact is introduced.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is not part of this exact theory or a checked
    /// Boolean or theorem construction fails. `kernel` is unchanged on failure.
    pub fn derive_constraint(
        &self,
        kernel: &mut Kernel,
        id: DeclarationId,
    ) -> Result<Evidence, HolTheoryProofError> {
        let target_index = self
            .constraints
            .iter()
            .position(|(candidate, _)| *candidate == id)
            .ok_or(HolTheoryProofError::Missing { id })?;
        let target = self.constraints[target_index].1;
        let mut staged = kernel.fork();
        let mut theorem = None;
        for (index, &(_, constraint)) in self.constraints.iter().enumerate() {
            let conjunction = self.conjunctions[index];
            let next = self.conjunctions[index + 1];
            if index == target_index {
                let selected = staged
                    .identity(positive(constraint))
                    .map_err(|source| HolTheoryProofError::Kernel { source })?;
                staged
                    .weaken(selected, &[positive(conjunction)], &[])
                    .map_err(|source| HolTheoryProofError::Kernel { source })?;
                theorem = Some(
                    staged
                        .and_left(selected, positive(next))
                        .map_err(|source| HolTheoryProofError::Kernel { source })?,
                );
            } else if let Some(selected) = theorem {
                staged
                    .weaken(selected, &[positive(constraint)], &[])
                    .map_err(|source| HolTheoryProofError::Kernel { source })?;
                theorem = Some(
                    staged
                        .and_left(selected, positive(next))
                        .map_err(|source| HolTheoryProofError::Kernel { source })?,
                );
            }
        }
        if self.conjunctions.last().copied() != Some(self.proposition) {
            return Err(HolTheoryProofError::Kernel {
                source: KernelError::InvalidTheoremRule {
                    rule: "complete theory reconstruction",
                },
            });
        }
        let theorem = theorem.ok_or(HolTheoryProofError::Missing { id })?;
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem,
            holds: true,
        })
    }

    /// Derives and specializes one declaration constraint at checked arguments.
    ///
    /// This is the ordinary efficient entry point for unfolding a declaration
    /// at a concrete or symbolic value. It eliminates equality-encoded
    /// universals and applies function equations as appropriate. This is
    /// userspace orchestration; every substitution, congruence, and theorem
    /// transport step is checked by the kernel, and the complete theory premise
    /// remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`derive_constraint`](Self::derive_constraint), or if an argument does
    /// not match the next universal binder. `kernel` is unchanged on failure.
    pub fn specialize_constraint(
        &self,
        kernel: &mut Kernel,
        id: DeclarationId,
        arguments: &[Ref],
    ) -> Result<Evidence, HolTheoryProofError> {
        let mut staged = kernel.fork();
        let mut evidence = self.derive_constraint(&mut staged, id)?;
        for &argument in arguments {
            let mut universal = staged.fork();
            match forall_elim(&mut universal, evidence.theorem, argument) {
                Ok(specialized) => {
                    staged = universal;
                    evidence = Evidence {
                        proposition: specialized.proposition,
                        theorem: specialized.theorem,
                        holds: true,
                    };
                }
                Err(ForallError::WrongForm) => {
                    let specialized = staged
                        .ap_thm(evidence.theorem, argument)
                        .map_err(|source| HolTheoryProofError::Kernel { source })?;
                    evidence = Evidence {
                        proposition: specialized.equality,
                        theorem: specialized.theorem,
                        holds: true,
                    };
                }
                Err(source) => return Err(HolTheoryProofError::Specialize { source }),
            }
        }
        *kernel = staged;
        Ok(evidence)
    }

    /// Proves one specialized graph application from its checked definition body.
    ///
    /// This specializes the selected declaration equation at `arguments`,
    /// checks that `body_fact` proves its exact right-hand side, reverses the
    /// equation, and transports the fact to the graph application. The complete
    /// theory premise and every premise of `body_fact` remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error if specialization does not end in a Boolean equality,
    /// `body_fact` has the wrong conclusion, or checked alignment, symmetry, or
    /// equality transport fails. `kernel` is unchanged on failure.
    pub fn prove_specialized_from_body(
        &self,
        kernel: &mut Kernel,
        id: DeclarationId,
        arguments: &[Ref],
        body_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, HolTheoryProofError> {
        let mut staged = kernel.fork();
        let equation = self.specialize_constraint(&mut staged, id, arguments)?;
        let operands = staged
            .arena()
            .children(equation.proposition)
            .ok_or(HolTheoryProofError::GraphEquation)?
            .collect::<Vec<_>>();
        let [bool_ty, graph, body] = operands.as_slice() else {
            return Err(HolTheoryProofError::GraphEquation);
        };
        let source = sole_positive_conclusion(&staged, body_fact)?;
        join_alpha_equivalent(&mut staged, source, *body)
            .map_err(|source| HolTheoryProofError::Syntax { source })?;
        let body_fact = staged
            .copy_theorem(body_fact)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        staged
            .convert_conclusions(body_fact, source, *body)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        let reversed = equality_symmetry(&mut staged, *bool_ty, equation.theorem)
            .map_err(|source| HolTheoryProofError::Equality { source })?;
        let theorem = staged
            .eq_mp(reversed.theorem, body_fact)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        *kernel = staged;
        Ok(Evidence {
            proposition: *graph,
            theorem,
            holds: true,
        })
    }

    /// Unfolds one proved specialized graph application to its definition body.
    ///
    /// This is the elimination direction of
    /// [`prove_specialized_from_body`](Self::prove_specialized_from_body). It
    /// specializes the declaration equation at `arguments`, checks that
    /// `graph_fact` proves its exact left-hand side, and transports that fact
    /// to the right-hand definition body. The complete theory premise and all
    /// premises of `graph_fact` remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error if specialization does not end in a Boolean equality,
    /// `graph_fact` has the wrong conclusion, or checked alignment or equality
    /// transport fails. `kernel` is unchanged on failure.
    pub fn prove_body_from_specialized(
        &self,
        kernel: &mut Kernel,
        id: DeclarationId,
        arguments: &[Ref],
        graph_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, HolTheoryProofError> {
        let mut staged = kernel.fork();
        let equation = self.specialize_constraint(&mut staged, id, arguments)?;
        let operands = staged
            .arena()
            .children(equation.proposition)
            .ok_or(HolTheoryProofError::GraphEquation)?
            .collect::<Vec<_>>();
        let [_bool_ty, graph, body] = operands.as_slice() else {
            return Err(HolTheoryProofError::GraphEquation);
        };
        let source = sole_positive_conclusion(&staged, graph_fact)?;
        join_alpha_equivalent(&mut staged, source, *graph)
            .map_err(|source| HolTheoryProofError::Syntax { source })?;
        let graph_fact = staged
            .copy_theorem(graph_fact)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        staged
            .convert_conclusions(graph_fact, source, *graph)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        let theorem = staged
            .eq_mp(equation.theorem, graph_fact)
            .map_err(|source| HolTheoryProofError::Kernel { source })?;
        *kernel = staged;
        Ok(Evidence {
            proposition: *body,
            theorem,
            holds: true,
        })
    }
}

fn sole_positive_conclusion(
    kernel: &Kernel,
    theorem: covalence_logic_hol::ThmId,
) -> Result<Ref, HolTheoryProofError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(HolTheoryProofError::Kernel {
            source: KernelError::MissingTheorem { id: theorem },
        })?;
    let mut rows = theorem.rhs.rows();
    let Some([literal]) = rows.next() else {
        return Err(HolTheoryProofError::BodyFact);
    };
    if rows.next().is_some() || !literal.is_positive() {
        return Err(HolTheoryProofError::BodyFact);
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(HolTheoryProofError::BodyFact)
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

/// Why a declaration constraint could not be derived from its complete theory.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum HolTheoryProofError {
    /// The requested declaration is not part of the exact theory.
    #[snafu(display("the SpecTec theory has no declaration constraint for {id:?}"))]
    Missing {
        /// Requested structural declaration selector.
        id: DeclarationId,
    },
    /// A checked HOL construction failed.
    #[snafu(display("could not derive a SpecTec theory constraint: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(display("could not specialize a SpecTec theory constraint: {source}"))]
    Specialize {
        /// Underlying checked derived-rule failure.
        source: ForallError,
    },
    /// Specialization did not produce the expected graph equality.
    #[snafu(display("specialized SpecTec definition is not a graph equation"))]
    GraphEquation,
    /// The supplied theorem did not prove one positive definition body.
    #[snafu(display("theorem does not prove the specialized SpecTec definition body"))]
    BodyFact,
    /// Checked body syntax could not be aligned.
    #[snafu(display("could not align the specialized SpecTec definition body: {source}"))]
    Syntax {
        /// Underlying checked syntax failure.
        source: SyntaxError,
    },
    /// Checked equality symmetry failed.
    #[snafu(display("could not reverse the specialized SpecTec graph equation: {source}"))]
    Equality {
        /// Underlying checked equality proof failure.
        source: EqualityError,
    },
}

/// Why declaration constraints could not form one complete HOL theory.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolTheoryError {
    /// A source declaration has no semantic constraint.
    #[snafu(display("SpecTec declaration {id:?} has no HOL semantic constraint"))]
    Missing {
        /// Uncovered structural selector.
        id: DeclarationId,
    },
    /// A constraint names no declaration in the exact source.
    #[snafu(display("HOL semantic constraint names foreign SpecTec declaration {id:?}"))]
    Foreign {
        /// Selector outside the source inventory.
        id: DeclarationId,
    },
    /// The checked conjunction could not be constructed.
    #[snafu(display("could not construct complete SpecTec HOL theory: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Applicability and result proposition for one source-ordered clause.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolCase {
    /// Existential proposition that this clause matches and its premises hold,
    /// independent of the graph result currently being tested.
    pub applicable: Ref,
    /// Proposition that this clause produces the graph result being tested.
    pub produces: Ref,
    /// Whether this clause carries the `SpecTec` `otherwise` premise.
    pub otherwise: bool,
}

/// One existential branch of an exact predicate-family definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HolFamilyBranch {
    /// Branch-local variables.
    pub binders: Vec<Ref>,
    /// Values matched against every formal predicate argument.
    pub arguments: Vec<Ref>,
    /// Additional Boolean conditions required by the branch.
    pub premises: Vec<Ref>,
}

/// Checked exact definition assembled from predicate-family branches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HolFamilyDefinition {
    /// Existential branch propositions in source order.
    pub branches: Vec<Ref>,
    /// Their exact disjunction.
    pub body: Ref,
    /// Universally closed equation relating the schema slot to `body`.
    pub equation: Ref,
}

/// Why exact family branches could not form a checked graph equation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolFamilyError {
    /// A branch did not match the predicate's formal arity.
    #[snafu(display("family branch has {actual} arguments; expected {expected}"))]
    Arity {
        /// Number of universally quantified formal arguments.
        expected: usize,
        /// Number of branch arguments.
        actual: usize,
    },
    /// A checked HOL constructor rejected the family definition.
    #[snafu(display("could not construct exact HOL family definition: {source}"))]
    Checked {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Builds an exact ordered-clause body for fixed graph inputs and result.
///
/// An `otherwise` case is guarded by the negation of the disjunction of every
/// earlier clause's applicability. Ordinary cases retain their source formula.
/// Empty case lists denote false.
///
/// # Errors
///
/// Returns an error unless every applicability and production term is Boolean
/// and all checked Boolean constructors succeed.
pub fn ordered_cases(
    kernel: &mut Kernel,
    bool_ty: Ref,
    cases: &[HolCase],
) -> Result<Ref, KernelError> {
    let mut prior = kernel.bool(bool_ty, false)?;
    let mut body = kernel.bool(bool_ty, false)?;
    for case in cases {
        let produces = if case.otherwise {
            let no_prior = kernel.op1(Op1::Not, prior)?;
            kernel.op2(Op2::And, no_prior, case.produces)?
        } else {
            case.produces
        };
        body = kernel.op2(Op2::Or, body, produces)?;
        prior = kernel.op2(Op2::Or, prior, case.applicable)?;
    }
    Ok(body)
}

/// Existentially closes a conjunction over clause-local variables.
///
/// Empty propositions denote true. Local variables are closed in source order.
///
/// # Errors
///
/// Returns an error unless propositions are Boolean, locals are free term
/// variables, and checked conjunction or existential construction fails.
pub fn existential_case(
    kernel: &mut Kernel,
    bool_ty: Ref,
    locals: &[Ref],
    propositions: &[Ref],
) -> Result<Ref, KernelError> {
    let mut body = conjoin(kernel, bool_ty, propositions)?;
    for &local in locals.iter().rev() {
        body = kernel.exists_tm(local, body)?;
    }
    Ok(body)
}

/// Closes one exact graph equation as a universally quantified proposition.
///
/// Constructs `∀ variables. predicate arguments... = body`. This only creates
/// checked syntax; it does not assume the equation or mint a theorem fact.
///
/// # Errors
///
/// Returns an error for ill-typed predicate application, a non-Boolean body,
/// invalid universal variables, or rejected equality construction.
pub fn close_graph_equation(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate: Ref,
    variables: &[Ref],
    arguments: &[Ref],
    body: Ref,
) -> Result<Ref, KernelError> {
    let applied = arguments
        .iter()
        .try_fold(predicate, |function, &argument| {
            kernel.app(function, argument)
        })?;
    let mut equation = kernel.eq(bool_ty, applied, body)?;
    for &variable in variables.iter().rev() {
        equation = kernel.forall_tm(bool_ty, variable, equation)?;
    }
    Ok(equation)
}

/// Transactionally defines one predicate family by an exact disjunction of
/// existential branches.
///
/// For each branch this equates every formal argument with its corresponding
/// branch argument, conjoins the branch premises, and existentially closes the
/// local binders. Empty branch lists denote false. The result is checked syntax
/// only and does not mint or assume a theorem fact.
///
/// # Errors
///
/// Returns an arity error or the first rejected equality, Boolean connective,
/// quantifier, predicate application, or graph equation. `kernel` is unchanged
/// on failure.
pub fn close_family_definition(
    kernel: &mut Kernel,
    bool_ty: Ref,
    predicate: Ref,
    formal_arguments: &[Ref],
    branches: &[HolFamilyBranch],
) -> Result<HolFamilyDefinition, HolFamilyError> {
    let mut staged = kernel.fork();
    let mut propositions = Vec::with_capacity(branches.len());
    for branch in branches {
        if branch.arguments.len() != formal_arguments.len() {
            return Err(HolFamilyError::Arity {
                expected: formal_arguments.len(),
                actual: branch.arguments.len(),
            });
        }
        let mut conditions = formal_arguments
            .iter()
            .zip(&branch.arguments)
            .map(|(&formal, &actual)| {
                staged
                    .eq(bool_ty, formal, actual)
                    .map_err(|source| HolFamilyError::Checked { source })
            })
            .collect::<Result<Vec<_>, _>>()?;
        conditions.extend_from_slice(&branch.premises);
        propositions.push(
            existential_case(&mut staged, bool_ty, &branch.binders, &conditions)
                .map_err(|source| HolFamilyError::Checked { source })?,
        );
    }
    let falsity = staged
        .bool(bool_ty, false)
        .map_err(|source| HolFamilyError::Checked { source })?;
    let body = propositions.iter().try_fold(falsity, |left, &right| {
        staged
            .op2(Op2::Or, left, right)
            .map_err(|source| HolFamilyError::Checked { source })
    })?;
    let equation = close_graph_equation(
        &mut staged,
        bool_ty,
        predicate,
        formal_arguments,
        formal_arguments,
        body,
    )
    .map_err(|source| HolFamilyError::Checked { source })?;
    *kernel = staged;
    Ok(HolFamilyDefinition {
        branches: propositions,
        body,
        equation,
    })
}

/// Conjoins exact declaration constraints into one model proposition.
///
/// Empty theories denote true.
///
/// # Errors
///
/// Returns an error unless every constraint is Boolean.
pub fn conjoin_constraints(
    kernel: &mut Kernel,
    bool_ty: Ref,
    constraints: &[Ref],
) -> Result<Ref, KernelError> {
    conjoin(kernel, bool_ty, constraints)
}

/// Transactionally closes exactly one constraint per source declaration into
/// one source-ordered HOL model proposition.
///
/// Structural selectors, not names, establish coverage. The result is checked
/// syntax only and does not assume the proposition or mint a theorem fact.
///
/// # Errors
///
/// Returns the first missing declaration in source order, the first foreign
/// selector in map order, or a checked Boolean-conjunction failure. `kernel`
/// is unchanged on failure.
pub fn close_hol_theory(
    source: &Source,
    kernel: &mut Kernel,
    bool_ty: Ref,
    constraints: &BTreeMap<DeclarationId, Ref>,
) -> Result<HolTheory, HolTheoryError> {
    let source_ids = source
        .declarations()
        .iter()
        .map(crate::SourceDeclaration::id)
        .collect::<BTreeSet<_>>();
    if let Some(&id) = constraints.keys().find(|id| !source_ids.contains(id)) {
        return Err(HolTheoryError::Foreign { id });
    }
    let ordered = source
        .declarations()
        .iter()
        .map(|declaration| {
            constraints
                .get(&declaration.id())
                .copied()
                .map(|constraint| (declaration.id(), constraint))
                .ok_or(HolTheoryError::Missing {
                    id: declaration.id(),
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut staged = kernel.fork();
    let mut conjunctions = Vec::with_capacity(ordered.len() + 1);
    let mut proposition = staged
        .bool(bool_ty, true)
        .map_err(|source| HolTheoryError::Kernel { source })?;
    conjunctions.push(proposition);
    for &(_, constraint) in &ordered {
        proposition = staged
            .op2(Op2::And, proposition, constraint)
            .map_err(|source| HolTheoryError::Kernel { source })?;
        conjunctions.push(proposition);
    }
    *kernel = staged;
    Ok(HolTheory {
        constraints: ordered,
        conjunctions,
        proposition,
    })
}

fn conjoin(kernel: &mut Kernel, bool_ty: Ref, propositions: &[Ref]) -> Result<Ref, KernelError> {
    let truth = kernel.bool(bool_ty, true)?;
    propositions
        .iter()
        .try_fold(truth, |left, &right| kernel.op2(Op2::And, left, right))
}
