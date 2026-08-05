//! Untrusted HOL proof recipes shared by terminal and browser consumers.
//!
//! These functions can only compose branded capabilities returned by
//! Nucleus. Bugs here can fail to find a proof or choose an unintended valid
//! theorem, but cannot forge a theorem or access the enclosed `SQLite` state.

use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextError, ContextId, ContextImplication, Conversion, Hol, Policy, ProofError,
    ProofSession, TermError, TermId, Theorem, TypeError, TypeId,
};

/// Expanded terms shared by the first above-LCF standard-library seed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Definitions {
    bool_type: TypeId,
    identity: TermId,
    truth: TermId,
    falsehood: TermId,
}

impl Definitions {
    /// Interns expanded truth, universal quantification, and falsehood.
    ///
    /// * `T` is `(lambda p:bool. p) = (lambda p:bool. p)`;
    /// * `forall_A(P)` is `(lambda x:A. P x) = (lambda x:A. T)`;
    /// * `F` is `forall_bool(lambda p:bool. p)`.
    ///
    /// These are definitions assembled through checked public syntax APIs, not
    /// new kernel constructors or rules.
    ///
    /// # Errors
    ///
    /// Returns an error if Nucleus rejects any checked term or type insertion.
    pub fn new<P: Policy>(connection: &mut Connection<Hol<P>>) -> Result<Self, DerivedError> {
        let bool_type = connection.insert_bool_type()?;
        let bound = connection.insert_bound_term(0, bool_type)?;
        let identity = connection.insert_lambda(bool_type, bound)?;
        let truth = connection.insert_equality(identity, identity)?;

        let seed = Self {
            bool_type,
            identity,
            truth,
            falsehood: truth,
        };
        let falsehood = seed.forall(connection, bool_type, identity)?;
        Ok(Self { falsehood, ..seed })
    }

    /// Returns the canonical Boolean type.
    #[must_use]
    pub const fn bool_type(self) -> TypeId {
        self.bool_type
    }

    /// Returns expanded truth `T`.
    #[must_use]
    pub const fn truth(self) -> TermId {
        self.truth
    }

    /// Returns expanded falsehood `F`.
    #[must_use]
    pub const fn falsehood(self) -> TermId {
        self.falsehood
    }

    /// Interns expanded universal quantification at `domain` for `predicate`.
    ///
    /// # Errors
    ///
    /// Returns an error if the predicate is ill-typed or insertion fails.
    pub fn forall<P: Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
        domain: TypeId,
        predicate: TermId,
    ) -> Result<TermId, DerivedError> {
        if !connection.term_is_locally_closed(predicate)? {
            return Err(DerivedError::OpenPredicate(predicate));
        }
        let variable = connection.insert_bound_term(0, domain)?;
        let application = connection.insert_application(predicate, variable)?;
        let lhs = connection.insert_lambda(domain, application)?;
        let rhs = connection.insert_lambda(domain, self.truth)?;
        Ok(connection.insert_equality(lhs, rhs)?)
    }

    /// Interns expanded negation `proposition = F`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `proposition` is Boolean.
    pub fn not<P: Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<TermId, DerivedError> {
        Ok(connection.insert_equality(proposition, self.falsehood)?)
    }

    /// Prepares syntax for the derived universal-elimination proof.
    ///
    /// # Errors
    ///
    /// Returns an error if `predicate` or `argument` is open or ill-typed.
    pub fn prepare_all_elim<P: Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
        domain: TypeId,
        predicate: TermId,
        argument: TermId,
    ) -> Result<AllElim, DerivedError> {
        let universal = self.forall(connection, domain, predicate)?;

        let variable = connection.insert_bound_term(0, domain)?;
        let predicate_body = connection.insert_application(predicate, variable)?;
        let lhs_function = connection.insert_lambda(domain, predicate_body)?;
        let rhs_function = connection.insert_lambda(domain, self.truth)?;
        let predicate_at_argument = connection.insert_application(predicate, argument)?;
        connection.insert_application(lhs_function, argument)?;
        AllElim::prepare_exact(
            connection,
            self,
            ExactElim {
                universal,
                domain,
                lhs_function,
                rhs_function,
                predicate_at_argument,
                argument,
            },
        )
    }
}

/// Pre-checked syntax for derived universal elimination.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AllElim {
    universal: TermId,
    argument: TermId,
    lhs_function: TermId,
    rhs_function: TermId,
    predicate_at_argument: TermId,
    rhs_at_argument: TermId,
    application_predicate: TermId,
    normalization_predicate: TermId,
    truth_witness: TermId,
    truth: TermId,
}

#[derive(Clone, Copy)]
struct ExactElim {
    universal: TermId,
    domain: TypeId,
    lhs_function: TermId,
    rhs_function: TermId,
    predicate_at_argument: TermId,
    argument: TermId,
}

impl AllElim {
    fn prepare_exact<P: Policy>(
        connection: &mut Connection<Hol<P>>,
        definitions: Definitions,
        exact: ExactElim,
    ) -> Result<Self, DerivedError> {
        let rhs_at_argument = connection.insert_application(exact.rhs_function, exact.argument)?;
        let function_type = connection.insert_arrow_type(exact.domain, definitions.bool_type)?;
        let function_variable = connection.insert_bound_term(0, function_type)?;
        let variable_at_argument =
            connection.insert_application(function_variable, exact.argument)?;
        let application_body =
            connection.insert_equality(variable_at_argument, exact.predicate_at_argument)?;
        let application_predicate = connection.insert_lambda(function_type, application_body)?;

        let proposition_variable = connection.insert_bound_term(0, definitions.bool_type)?;
        let normalization_body =
            connection.insert_equality(proposition_variable, exact.predicate_at_argument)?;
        let normalization_predicate =
            connection.insert_lambda(definitions.bool_type, normalization_body)?;

        Ok(Self {
            universal: exact.universal,
            argument: exact.argument,
            lhs_function: exact.lhs_function,
            rhs_function: exact.rhs_function,
            predicate_at_argument: exact.predicate_at_argument,
            rhs_at_argument,
            application_predicate,
            normalization_predicate,
            truth_witness: definitions.identity,
            truth: definitions.truth,
        })
    }

    /// Returns the exact expanded universal proposition accepted by [`Self::prove`].
    #[must_use]
    pub const fn universal(self) -> TermId {
        self.universal
    }

    /// Returns the expected conclusion `predicate argument`.
    #[must_use]
    pub const fn conclusion(self) -> TermId {
        self.predicate_at_argument
    }

    /// Derives `Gamma |- predicate argument` from `Gamma |- forall_A(predicate)`.
    ///
    /// # Errors
    ///
    /// Returns the public Nucleus proof error when a premise or exact endpoint
    /// does not match.
    pub fn prove<'brand, P: Policy>(
        self,
        proof: &mut ProofSession<'brand, P>,
        universal: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        let lhs_beta = proof.conversion_beta(self.lhs_function, self.argument)?;
        let lhs_equals_value = proof.prove_conversion_equality(universal.context(), &lhs_beta)?;

        let application_beta =
            proof.conversion_beta(self.application_predicate, self.lhs_function)?;
        let application_expand = proof.conversion_symmetry(&application_beta)?;
        let application_premise = proof.convert_theorem(&lhs_equals_value, &application_expand)?;
        let rhs_application = proof.equality_substitution(
            universal,
            self.application_predicate,
            &application_premise,
        )?;
        let rhs_application_beta =
            proof.conversion_beta(self.application_predicate, self.rhs_function)?;
        let rhs_equals_value = proof.convert_theorem(&rhs_application, &rhs_application_beta)?;

        let rhs_beta = proof.conversion_beta(self.rhs_function, self.argument)?;
        let rhs_equals_truth = proof.prove_conversion_equality(universal.context(), &rhs_beta)?;
        let normalization_beta =
            proof.conversion_beta(self.normalization_predicate, self.rhs_at_argument)?;
        let normalization_expand = proof.conversion_symmetry(&normalization_beta)?;
        let normalization_premise =
            proof.convert_theorem(&rhs_equals_value, &normalization_expand)?;
        let truth_application = proof.equality_substitution(
            &rhs_equals_truth,
            self.normalization_predicate,
            &normalization_premise,
        )?;
        let truth_beta = proof.conversion_beta(self.normalization_predicate, self.truth)?;
        let truth_equals_value = proof.convert_theorem(&truth_application, &truth_beta)?;

        let truth_theorem = proof.prove_reflexivity(universal.context(), self.truth_witness)?;
        proof.equality_modus_ponens(&truth_equals_value, &truth_theorem)
    }
}

/// IDs produced by the explicit infinite-carrier-assumption seed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinitySeed {
    /// Opaque carrier type used by the assumptions.
    pub ind_type: TypeId,
    /// Opaque zero-like constant.
    pub zero: TermId,
    /// Opaque successor-like constant.
    pub successor: TermId,
    /// Assumption `forall x. not (successor x = zero)`.
    pub successor_nonzero_assumption: TermId,
    /// Assumption `forall x y. (successor x = successor y) = (x = y)`.
    pub successor_injective_assumption: TermId,
    /// Exact context containing both assumptions.
    pub context: ContextId,
    /// Persisted conclusion `not (successor zero = zero)`.
    pub conclusion: TermId,
    /// Persisted injectivity instance
    /// `(successor zero = successor (successor zero)) = (zero = successor zero)`.
    pub injectivity_instance: TermId,
}

/// Builds explicit infinite-carrier assumptions and proves `not (successor zero = zero)`.
///
/// This deliberately makes no natural-number or induction claim. The current
/// primitive API exposes choice but no infinity axiom; choice alone cannot show
/// that an opaque inhabited type is infinite. Consequently `ind`, `zero`, and
/// `successor` remain opaque declarations and both assumptions remain visible
/// in the exact theorem context.
///
/// # Errors
///
/// Returns an error if checked syntax/context construction or a public proof
/// operation fails.
pub fn prove_infinity_seed<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    ind_symbol: i64,
    zero_symbol: i64,
    successor_symbol: i64,
) -> Result<InfinitySeed, DerivedError> {
    let definitions = Definitions::new(connection)?;
    let ind_type = connection.insert_base_type(ind_symbol)?;
    let zero = connection.insert_constant(zero_symbol, ind_type)?;
    let successor_type = connection.insert_arrow_type(ind_type, ind_type)?;
    let successor = connection.insert_constant(successor_symbol, successor_type)?;

    let x = connection.insert_bound_term(0, ind_type)?;
    let successor_x = connection.insert_application(successor, x)?;
    let successor_x_equals_zero = connection.insert_equality(successor_x, zero)?;
    let successor_x_nonzero = definitions.not(connection, successor_x_equals_zero)?;
    let nonzero_predicate = connection.insert_lambda(ind_type, successor_x_nonzero)?;
    let successor_nonzero_assumption =
        definitions.forall(connection, ind_type, nonzero_predicate)?;

    let inner_y = connection.insert_bound_term(0, ind_type)?;
    let inner_x = connection.insert_bound_term(1, ind_type)?;
    let successor_inner_x = connection.insert_application(successor, inner_x)?;
    let successor_inner_y = connection.insert_application(successor, inner_y)?;
    let successors_equal = connection.insert_equality(successor_inner_x, successor_inner_y)?;
    let arguments_equal = connection.insert_equality(inner_x, inner_y)?;
    let injectivity_body = connection.insert_equality(successors_equal, arguments_equal)?;
    let injectivity_for_y = connection.insert_lambda(ind_type, injectivity_body)?;
    let always_truth_for_y = connection.insert_lambda(ind_type, definitions.truth())?;
    let forall_y = connection.insert_equality(injectivity_for_y, always_truth_for_y)?;
    let injectivity_predicate = connection.insert_lambda(ind_type, forall_y)?;
    let successor_injective_assumption =
        definitions.forall(connection, ind_type, injectivity_predicate)?;

    let context = connection
        .define_context([successor_nonzero_assumption, successor_injective_assumption])?;
    let nonzero_plan =
        definitions.prepare_all_elim(connection, ind_type, nonzero_predicate, zero)?;
    let outer_injectivity_plan =
        definitions.prepare_all_elim(connection, ind_type, injectivity_predicate, zero)?;

    // The result of eliminating the outer injectivity quantifier at zero.
    let successor_zero = connection.insert_application(successor, zero)?;
    let y = connection.insert_bound_term(0, ind_type)?;
    let successor_y = connection.insert_application(successor, y)?;
    let successors_equal = connection.insert_equality(successor_zero, successor_y)?;
    let arguments_equal = connection.insert_equality(zero, y)?;
    let injectivity_at_zero_body = connection.insert_equality(successors_equal, arguments_equal)?;
    let injectivity_at_zero_predicate =
        connection.insert_lambda(ind_type, injectivity_at_zero_body)?;
    let injectivity_at_zero_universal =
        connection.insert_equality(injectivity_at_zero_predicate, always_truth_for_y)?;
    let successor_successor_zero = connection.insert_application(successor, successor_zero)?;
    let successor_equality =
        connection.insert_equality(successor_zero, successor_successor_zero)?;
    let argument_equality = connection.insert_equality(zero, successor_zero)?;
    let injectivity_instance_term =
        connection.insert_equality(successor_equality, argument_equality)?;
    let inner_injectivity_plan = AllElim::prepare_exact(
        connection,
        definitions,
        ExactElim {
            universal: injectivity_at_zero_universal,
            domain: ind_type,
            lhs_function: injectivity_at_zero_predicate,
            rhs_function: always_truth_for_y,
            predicate_at_argument: injectivity_instance_term,
            argument: successor_zero,
        },
    )?;

    let (conclusion, injectivity_instance) =
        connection.with_proof_session(|mut proof| -> Result<(TermId, TermId), ProofError> {
            let assumption = proof.prove_hypothesis(context, successor_nonzero_assumption)?;
            let theorem = nonzero_plan.prove(&mut proof, &assumption)?;
            let beta = proof.conversion_beta(nonzero_predicate, zero)?;
            let theorem = proof.convert_theorem(&theorem, &beta)?;
            proof.persist_theorem(&theorem)?;

            let injectivity = proof.prove_hypothesis(context, successor_injective_assumption)?;
            let injectivity = outer_injectivity_plan.prove(&mut proof, &injectivity)?;
            let outer_beta = proof.conversion_beta(injectivity_predicate, zero)?;
            let injectivity = proof.convert_theorem(&injectivity, &outer_beta)?;
            let injectivity = inner_injectivity_plan.prove(&mut proof, &injectivity)?;
            proof.persist_theorem(&injectivity)?;
            Ok((theorem.conclusion(), injectivity.conclusion()))
        })?;

    Ok(InfinitySeed {
        ind_type,
        zero,
        successor,
        successor_nonzero_assumption,
        successor_injective_assumption,
        context,
        conclusion,
        injectivity_instance,
    })
}

/// Failure in checked derived-library construction or proof replay.
#[derive(Debug)]
pub enum DerivedError {
    /// Checked type construction failed.
    Type(TypeError),
    /// Checked term construction failed.
    Term(TermError),
    /// Checked context construction failed.
    Context(ContextError),
    /// Public LCF proof replay failed.
    Proof(ProofError),
    /// Expanded universal quantification requires a closed predicate.
    OpenPredicate(TermId),
}

impl fmt::Display for DerivedError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(error) => write!(formatter, "HOL type construction failed: {error}"),
            Self::Term(error) => write!(formatter, "HOL term construction failed: {error}"),
            Self::Context(error) => write!(formatter, "HOL context construction failed: {error}"),
            Self::Proof(error) => write!(formatter, "HOL proof replay failed: {error}"),
            Self::OpenPredicate(predicate) => write!(
                formatter,
                "expanded universal predicate {} is not locally closed",
                predicate.get()
            ),
        }
    }
}

impl StdError for DerivedError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Context(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::OpenPredicate(_) => None,
        }
    }
}

impl From<TypeError> for DerivedError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<TermError> for DerivedError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ContextError> for DerivedError {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
    }
}

impl From<ProofError> for DerivedError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

/// An ordinary upper-layer view of two opposite implication witnesses.
///
/// This is not a new kernel capability and has no authoritative table.
pub struct ContextEquivalence<'witness, 'brand> {
    forward: &'witness ContextImplication<'brand>,
    backward: &'witness ContextImplication<'brand>,
}

impl<'brand> ContextEquivalence<'_, 'brand> {
    /// Returns the left-to-right witness.
    #[must_use]
    pub const fn forward(&self) -> &ContextImplication<'brand> {
        self.forward
    }

    /// Returns the right-to-left witness.
    #[must_use]
    pub const fn backward(&self) -> &ContextImplication<'brand> {
        self.backward
    }

    /// Returns the left endpoint.
    #[must_use]
    pub const fn left(&self) -> ContextId {
        self.forward.antecedent()
    }

    /// Returns the right endpoint.
    #[must_use]
    pub const fn right(&self) -> ContextId {
        self.forward.consequent()
    }
}

/// Two implication witnesses are not exact opposites.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ContextEquivalenceMismatch {
    /// Forward antecedent.
    pub forward_antecedent: ContextId,
    /// Forward consequent.
    pub forward_consequent: ContextId,
    /// Backward antecedent.
    pub backward_antecedent: ContextId,
    /// Backward consequent.
    pub backward_consequent: ContextId,
}

/// Derives `context |- term = term` from conversion reflexivity.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn reflexivity<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    context: ContextId,
    term: TermId,
) -> Result<Theorem<'brand>, ProofError> {
    let conversion = proof.conversion_reflexivity(term)?;
    proof.prove_conversion_equality(context, &conversion)
}

/// Derives closed beta equality by composing checked beta conversion with
/// conversion-to-equality.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn beta<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    context: ContextId,
    abstraction: TermId,
    argument: TermId,
) -> Result<Theorem<'brand>, ProofError> {
    let conversion = proof.conversion_beta(abstraction, argument)?;
    proof.prove_conversion_equality(context, &conversion)
}

/// Transports a Boolean theorem along a checked conversion.
///
/// This is exactly conversion-to-equality followed by equality modus ponens;
/// it introduces no additional trusted rule.
///
/// # Errors
///
/// Returns an error from either checked primitive operation.
pub fn convert_theorem<'brand, P: Policy>(
    proof: &mut ProofSession<'brand, P>,
    theorem: &Theorem<'brand>,
    conversion: &Conversion<'brand>,
) -> Result<Theorem<'brand>, ProofError> {
    let equality = proof.prove_conversion_equality(theorem.context(), conversion)?;
    proof.equality_modus_ponens(&equality, theorem)
}

/// Checks that two implication witnesses have exactly opposite endpoints.
///
/// # Errors
///
/// Returns the four observed endpoints when the witnesses are not opposites.
pub fn context_equivalence<'witness, 'brand>(
    forward: &'witness ContextImplication<'brand>,
    backward: &'witness ContextImplication<'brand>,
) -> Result<ContextEquivalence<'witness, 'brand>, ContextEquivalenceMismatch> {
    if forward.antecedent() != backward.consequent()
        || forward.consequent() != backward.antecedent()
    {
        return Err(ContextEquivalenceMismatch {
            forward_antecedent: forward.antecedent(),
            forward_consequent: forward.consequent(),
            backward_antecedent: backward.antecedent(),
            backward_consequent: backward.consequent(),
        });
    }
    Ok(ContextEquivalence { forward, backward })
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_nucleus::{AllowAll, Connection, TermView, TypeView};

    #[test]
    fn expanded_definitions_have_the_promised_shape() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let definitions = Definitions::new(&mut connection).unwrap();

        let TermView::Equality { left, right } = connection.term(definitions.truth()).unwrap()
        else {
            panic!("truth must be an equality");
        };
        assert_eq!(left, right);

        let TermView::Equality { left, right } = connection.term(definitions.falsehood()).unwrap()
        else {
            panic!("falsehood must be expanded universal quantification");
        };
        assert_ne!(left, right);
        assert_eq!(
            connection.term_type(definitions.falsehood()).unwrap(),
            definitions.bool_type()
        );
    }

    #[test]
    fn expanded_forall_rejects_accidental_de_bruijn_capture() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let definitions = Definitions::new(&mut connection).unwrap();
        let open_proposition = connection
            .insert_bound_term(0, definitions.bool_type())
            .unwrap();
        let error = definitions
            .forall(&mut connection, definitions.bool_type(), open_proposition)
            .unwrap_err();
        assert!(matches!(
            error,
            DerivedError::OpenPredicate(term) if term == open_proposition
        ));
    }

    #[test]
    fn checked_all_elim_derives_only_the_exact_predicate_instance() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let definitions = Definitions::new(&mut connection).unwrap();
        let bool_type = definitions.bool_type();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let argument = connection.insert_bool_term(false).unwrap();
        let unrelated = connection.insert_bool_term(true).unwrap();
        let plan = definitions
            .prepare_all_elim(&mut connection, bool_type, identity, argument)
            .unwrap();
        let context = connection
            .define_context([plan.universal(), unrelated])
            .unwrap();

        connection
            .with_proof_session(|mut proof| {
                let universal = proof.prove_hypothesis(context, plan.universal())?;
                let theorem = plan.prove(&mut proof, &universal)?;
                assert_eq!(theorem.context(), context);
                assert_eq!(theorem.conclusion(), plan.conclusion());

                let unrelated = proof.prove_hypothesis(context, unrelated)?;
                assert!(plan.prove(&mut proof, &unrelated).is_err());
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn infinity_seed_preserves_assumptions_and_only_persists_kernel_state() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let seed = prove_infinity_seed(&mut connection, 10, 20, 30).unwrap();

        let mut expected = vec![
            seed.successor_nonzero_assumption,
            seed.successor_injective_assumption,
        ];
        expected.sort_unstable();
        assert_eq!(connection.context_members(seed.context).unwrap(), expected);
        assert!(
            connection
                .proved_judgement(seed.context, seed.conclusion)
                .unwrap()
        );
        assert!(
            connection
                .proved_judgement(seed.context, seed.injectivity_instance)
                .unwrap()
        );
        assert!(matches!(
            connection.type_view(seed.ind_type).unwrap(),
            TypeView::Base { symbol: 10 }
        ));

        let TermView::Equality { left, right } = connection.term(seed.conclusion).unwrap() else {
            panic!("expanded negation must be an equality");
        };
        assert_eq!(
            right,
            Definitions::new(&mut connection).unwrap().falsehood()
        );
        let TermView::Equality {
            left: successor_zero,
            right: zero,
        } = connection.term(left).unwrap()
        else {
            panic!("negated proposition must be successor zero equals zero");
        };
        assert_eq!(zero, seed.zero);
        assert!(matches!(
            connection.term(successor_zero).unwrap(),
            TermView::Application {
                function,
                argument
            } if function == seed.successor && argument == seed.zero
        ));

        let TermView::Equality {
            left: successors_equal,
            right: arguments_equal,
        } = connection.term(seed.injectivity_instance).unwrap()
        else {
            panic!("injectivity instance must be equality of equalities");
        };
        let TermView::Equality {
            left: instance_successor_zero,
            right: successor_successor_zero,
        } = connection.term(successors_equal).unwrap()
        else {
            panic!("injectivity instance left side must be an equality");
        };
        let TermView::Equality {
            left: instance_zero,
            right: argument_successor_zero,
        } = connection.term(arguments_equal).unwrap()
        else {
            panic!("injectivity instance right side must be an equality");
        };
        assert_eq!(instance_zero, seed.zero);
        assert_eq!(instance_successor_zero, successor_zero);
        assert_eq!(argument_successor_zero, successor_zero);
        assert!(matches!(
            connection.term(successor_successor_zero).unwrap(),
            TermView::Application {
                function,
                argument
            } if function == seed.successor && argument == successor_zero
        ));
    }

    #[test]
    fn beta_recipe_produces_a_persistable_kernel_theorem() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();

        let conclusion = connection
            .with_proof_session(|mut proof| {
                let theorem = beta(&mut proof, ContextId::empty(), identity, truth)?;
                let conclusion = theorem.conclusion();
                proof.persist_theorem(&theorem)?;
                Ok::<_, ProofError>(conclusion)
            })
            .unwrap();

        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("beta recipe did not produce equality")
        };
        assert!(matches!(
            connection.term(left).unwrap(),
            TermView::Application {
                function,
                argument
            } if function == identity && argument == truth
        ));
        assert_eq!(right, truth);
        assert!(
            connection
                .proved_judgement(ContextId::empty(), conclusion)
                .unwrap()
        );
    }

    #[test]
    fn theorem_conversion_and_context_equivalence_are_ordinary_compositions() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let bool_type = connection.insert_bool_type().unwrap();
        let p = connection.insert_free_term(7, bool_type).unwrap();
        let equality = connection.insert_equality(p, p).unwrap();
        let truth = connection.insert_bool_term(true).unwrap();
        let variable = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, variable).unwrap();
        let application = connection.insert_application(identity, truth).unwrap();
        let application_context = connection.define_context([application]).unwrap();
        let left = connection.define_context([equality]).unwrap();
        let right = connection.define_context([truth]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let truth_witness = proof.prove_truth(left)?;
                let forward = proof.prove_context_implication(left, right, &[truth_witness])?;
                let equality_witness = reflexivity(&mut proof, right, p)?;
                let backward = proof.prove_context_implication(right, left, &[equality_witness])?;

                assert!(context_equivalence(&forward, &forward).is_err());
                let equivalence = context_equivalence(&forward, &backward).unwrap();
                assert_eq!(equivalence.left(), left);
                assert_eq!(equivalence.right(), right);
                assert_eq!(equivalence.forward().antecedent(), left);
                assert_eq!(equivalence.backward().antecedent(), right);

                let premise = proof.prove_hypothesis(application_context, application)?;
                let conversion = proof.conversion_beta(identity, truth)?;
                let converted = convert_theorem(&mut proof, &premise, &conversion)?;
                assert_eq!(converted.conclusion(), truth);
                Ok::<_, ProofError>(())
            })
            .unwrap();
    }
}
