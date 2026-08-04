//! Expanded HOL definitions and derived proofs built above Nucleus's LCF boundary.
//!
//! This crate owns no authoritative tables and introduces no proof rule.  Every theorem it
//! returns has been replayed through a branded [`ProofSession`] using public Nucleus operations.

use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextError, ContextId, Hol, Policy, ProofError, ProofSession, TermError, TermId,
    TermInstantiation, Theorem, TypeError, TypeId, TypeInstantiation,
};

/// Expanded terms shared by the small classical HOL library.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Definitions {
    bool_type: TypeId,
    identity: TermId,
    truth: TermId,
    falsehood: TermId,
}

impl Definitions {
    /// Interns the expanded definitions of truth and falsehood.
    ///
    /// * `T` is `(lambda p:bool. p) = (lambda p:bool. p)`;
    /// * `forall_A(P)` is `(lambda x:A. P x) = (lambda x:A. T)`;
    /// * `F` is `forall_bool(lambda p:bool. p)`.
    ///
    /// # Errors
    ///
    /// Returns an error if Nucleus rejects any checked term or type insertion.
    pub fn new<P: Policy>(connection: &mut Connection<Hol<P>>) -> Result<Self, Error> {
        let bool_type = connection.insert_bool_type()?;
        let bound = connection.insert_bound_term(0, bool_type)?;
        let identity = connection.insert_lambda(bool_type, bound)?;
        let truth = connection.insert_equality(identity, identity)?;

        let seed = Self {
            bool_type,
            identity,
            truth,
            // Replaced immediately below; this avoids an optional field in a fully initialized
            // public value while preserving one canonical construction path for `forall`.
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

    /// Interns expanded universal quantification at `domain` for a closed `predicate`.
    ///
    /// Nucleus checks typing while admitting the resulting term DAG. If `predicate` has an outer
    /// de Bruijn boundary, that boundary is preserved in the result.
    ///
    /// # Errors
    ///
    /// Returns an error if the predicate is not of type `domain -> bool` or insertion otherwise
    /// fails.
    pub fn forall<P: Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
        domain: TypeId,
        predicate: TermId,
    ) -> Result<TermId, Error> {
        let variable = connection.insert_bound_term(0, domain)?;
        let application = connection.insert_application(predicate, variable)?;
        let lhs = connection.insert_lambda(domain, application)?;
        let rhs = connection.insert_lambda(domain, self.truth)?;
        Ok(connection.insert_equality(lhs, rhs)?)
    }

    /// Interns expanded negation `p = F`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `proposition` is Boolean. Any existing outer de Bruijn boundary is
    /// preserved.
    pub fn not<P: Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
        proposition: TermId,
    ) -> Result<TermId, Error> {
        Ok(connection.insert_equality(proposition, self.falsehood)?)
    }

    /// Prepares all syntax needed by the checked derived `ALL_ELIM` proof.
    ///
    /// Preparing syntax before opening a proof session keeps the LCF brand local while ensuring
    /// that the subsequent proof uses no privileged access to the connection.
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
    ) -> Result<AllElim, Error> {
        let universal = self.forall(connection, domain, predicate)?;

        let variable = connection.insert_bound_term(0, domain)?;
        let predicate_body = connection.insert_application(predicate, variable)?;
        let lhs_function = connection.insert_lambda(domain, predicate_body)?;
        let rhs_function = connection.insert_lambda(domain, self.truth)?;
        let predicate_at_argument = connection.insert_application(predicate, argument)?;
        connection.insert_application(lhs_function, argument)?;
        let rhs_at_argument = connection.insert_application(rhs_function, argument)?;

        // λf. f argument = P argument, used to apply the quantified function equality.
        let function_type = connection.insert_arrow_type(domain, self.bool_type)?;
        let function_variable = connection.insert_bound_term(0, function_type)?;
        let variable_at_argument = connection.insert_application(function_variable, argument)?;
        let application_body =
            connection.insert_equality(variable_at_argument, predicate_at_argument)?;
        let application_predicate = connection.insert_lambda(function_type, application_body)?;

        // λq. q = P argument, used once more to beta-normalize the right-hand side to T.
        let proposition_variable = connection.insert_bound_term(0, self.bool_type)?;
        let normalization_body =
            connection.insert_equality(proposition_variable, predicate_at_argument)?;
        let normalization_predicate =
            connection.insert_lambda(self.bool_type, normalization_body)?;

        Ok(AllElim {
            universal,
            argument,
            lhs_function,
            rhs_function,
            predicate_at_argument,
            rhs_at_argument,
            application_predicate,
            normalization_predicate,
            truth_witness: self.identity,
            truth: self.truth,
        })
    }
}

/// Pre-checked syntax for the derived universal-elimination proof.
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

impl AllElim {
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
    /// This is an ordinary proof program. It uses beta conversion, conversion equality,
    /// reflexivity, typed Leibniz substitution, and equality modus ponens. An unrelated premise
    /// fails in Nucleus rather than being accepted by this wrapper.
    ///
    /// # Errors
    ///
    /// Returns the public Nucleus proof error if any premise, context, conversion, or exact term
    /// endpoint does not match.
    pub fn prove<'brand, P: Policy>(
        self,
        proof: &mut ProofSession<'brand, P>,
        universal: &Theorem<'brand>,
    ) -> Result<Theorem<'brand>, ProofError> {
        // First obtain `(lhs argument) = (P argument)` by beta conversion.
        let lhs_beta = proof.conversion_beta(self.lhs_function, self.argument)?;
        let lhs_equals_value = proof.prove_conversion_equality(universal.context(), &lhs_beta)?;

        // Re-expand that theorem as `(λf. f argument = P argument) lhs`, the exact premise
        // expected by Leibniz substitution on the quantified function equality.
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

        // The quantified right function beta-reduces to expanded T. Use a second Leibniz step
        // to turn `(rhs argument) = P argument` into `T = P argument`.
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

        // Expanded T is itself equality reflexivity of the identity function.
        let truth_theorem = proof.prove_reflexivity(universal.context(), self.truth_witness)?;
        proof.equality_modus_ponens(&truth_equals_value, &truth_theorem)
    }
}

/// IDs produced by the explicit infinite-`ind` assumption demo.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinityDemo {
    /// Opaque base type used by the assumptions.
    pub ind_type: TypeId,
    /// Opaque zero-like constant.
    pub zero: TermId,
    /// Opaque successor-like constant.
    pub successor: TermId,
    /// Assumption `forall x. not (successor x = zero)`.
    pub successor_nonzero_assumption: TermId,
    /// Preserved injectivity assumption.
    pub successor_injective_assumption: TermId,
    /// Exact context containing both assumptions.
    pub context: ContextId,
    /// Persisted conclusion `not (successor zero = zero)`.
    pub conclusion: TermId,
}

/// Builds explicit infinity assumptions and proves `not (successor zero = zero)`.
///
/// This deliberately makes no natural-number, induction, or choice claim. `ind`, `zero`, and
/// `successor` remain opaque signature declarations, and both assumptions remain visible in the
/// exact theorem context.
///
/// # Errors
///
/// Returns an error if checked syntax/context construction or any public proof rule fails.
pub fn prove_infinity_successor_nonzero<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    ind_symbol: i64,
    zero_symbol: i64,
    successor_symbol: i64,
) -> Result<InfinityDemo, Error> {
    let definitions = Definitions::new(connection)?;
    let ind_type = connection.insert_base_type(ind_symbol)?;
    let zero = connection.insert_constant(zero_symbol, ind_type)?;
    let successor_type = connection.insert_arrow_type(ind_type, ind_type)?;
    let successor = connection.insert_constant(successor_symbol, successor_type)?;

    // H0 = forall x. not(successor x = zero).
    let x = connection.insert_bound_term(0, ind_type)?;
    let successor_x = connection.insert_application(successor, x)?;
    let successor_x_equals_zero = connection.insert_equality(successor_x, zero)?;
    let successor_x_nonzero = definitions.not(connection, successor_x_equals_zero)?;
    let nonzero_predicate = connection.insert_lambda(ind_type, successor_x_nonzero)?;
    let successor_nonzero_assumption =
        definitions.forall(connection, ind_type, nonzero_predicate)?;

    // Hinj = forall x. forall y. (successor x = successor y) = (x = y).
    // Under the inner binder, x is index 1 and y is index 0.
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
    let plan = definitions.prepare_all_elim(connection, ind_type, nonzero_predicate, zero)?;
    let conclusion = connection.with_proof_session(|mut proof| -> Result<TermId, ProofError> {
        let assumption = proof.prove_hypothesis(context, successor_nonzero_assumption)?;
        let theorem = plan.prove(&mut proof, &assumption)?;
        let beta = proof.conversion_beta(nonzero_predicate, zero)?;
        let theorem = proof.convert_theorem(&theorem, &beta)?;
        proof.persist_theorem(&theorem)?;
        Ok(theorem.conclusion())
    })?;

    Ok(InfinityDemo {
        ind_type,
        zero,
        successor,
        successor_nonzero_assumption,
        successor_injective_assumption,
        context,
        conclusion,
    })
}

/// Coordinates produced by the schematic beta-instantiation demonstration.
///
/// `alpha` is a free rank-zero schematic type variable, not a first-class universally quantified
/// type. No opaque polymorphic constant is introduced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SchematicBetaDemo {
    /// The shared empty assumption context.
    pub context: ContextId,
    /// Free schematic type variable `alpha`.
    pub alpha: TypeId,
    /// Primitive Boolean type.
    pub bool_type: TypeId,
    /// Function type `alpha -> alpha`.
    pub alpha_identity_type: TypeId,
    /// Function type `bool -> bool`.
    pub bool_identity_type: TypeId,
    /// Free term `y_alpha : alpha`.
    pub y_alpha: TermId,
    /// Identity function `lambda x:alpha. x`.
    pub identity_alpha: TermId,
    /// Persisted generic beta conclusion `(lambda x:alpha. x) y_alpha = y_alpha`.
    pub generic_conclusion: TermId,
    /// Type-instantiated free term `y_bool : bool`.
    pub y_bool: TermId,
    /// Type-instantiated identity function `lambda x:bool. x`.
    pub identity_bool: TermId,
    /// Persisted conclusion after `alpha := bool`.
    pub bool_conclusion: TermId,
    /// Primitive Boolean truth used for the term instance.
    pub truth: TermId,
    /// Persisted conclusion after `y_bool := true`.
    pub concrete_conclusion: TermId,
}

/// Proves generic beta, instantiates its schematic type with `bool`, then its free term with true.
///
/// This is an above-TCB proof program. It sequences existing checked beta and term-instantiation
/// operations with Nucleus's checked schematic type-instantiation operation; it adds no rule or
/// authoritative table.
///
/// # Errors
///
/// Returns an error if checked syntax construction or any public branded proof operation fails.
pub fn prove_schematic_beta<P: Policy>(
    connection: &mut Connection<Hol<P>>,
    alpha_symbol: i64,
    y_symbol: i64,
) -> Result<SchematicBetaDemo, Error> {
    let context = ContextId::empty();
    let alpha = connection.insert_free_type(alpha_symbol)?;
    let bool_type = connection.insert_bool_type()?;
    let alpha_identity_type = connection.insert_arrow_type(alpha, alpha)?;
    let bool_identity_type = connection.insert_arrow_type(bool_type, bool_type)?;

    let y_alpha = connection.insert_free_term(y_symbol, alpha)?;
    let alpha_bound = connection.insert_bound_term(0, alpha)?;
    let identity_alpha = connection.insert_lambda(alpha, alpha_bound)?;
    let generic_application = connection.insert_application(identity_alpha, y_alpha)?;
    let expected_generic = connection.insert_equality(generic_application, y_alpha)?;

    // Pre-interning the expected instances gives the demo stable helper coordinates. The rules
    // still rebuild and check their outputs independently inside the branded session.
    let y_bool = connection.insert_free_term(y_symbol, bool_type)?;
    let bool_bound = connection.insert_bound_term(0, bool_type)?;
    let identity_bool = connection.insert_lambda(bool_type, bool_bound)?;
    let bool_application = connection.insert_application(identity_bool, y_bool)?;
    let expected_bool = connection.insert_equality(bool_application, y_bool)?;
    let truth = connection.insert_bool_term(true)?;
    let concrete_application = connection.insert_application(identity_bool, truth)?;
    let expected_concrete = connection.insert_equality(concrete_application, truth)?;

    let (generic_conclusion, bool_conclusion, concrete_conclusion) = connection
        .with_proof_session(|mut proof| -> Result<_, ProofError> {
            let generic = proof.prove_beta(context, identity_alpha, y_alpha)?;
            proof.persist_theorem(&generic)?;
            let bool_instance = proof.instantiate_types(
                &generic,
                &[TypeInstantiation {
                    variable: alpha,
                    replacement: bool_type,
                }],
            )?;
            proof.persist_theorem(&bool_instance)?;
            let concrete = proof.instantiate_terms(
                &bool_instance,
                &[TermInstantiation {
                    variable: y_bool,
                    replacement: truth,
                }],
            )?;
            proof.persist_theorem(&concrete)?;
            Ok((
                generic.conclusion(),
                bool_instance.conclusion(),
                concrete.conclusion(),
            ))
        })?;

    // These equalities are consequences of canonical checked interning, not additional proof
    // authority. Report an implementation mismatch without turning an above-TCB assertion into a
    // process abort.
    for (stage, expected, actual) in [
        ("generic beta", expected_generic, generic_conclusion),
        ("type instance", expected_bool, bool_conclusion),
        ("term instance", expected_concrete, concrete_conclusion),
    ] {
        if expected != actual {
            return Err(Error::UnexpectedConclusion {
                stage,
                expected,
                actual,
            });
        }
    }

    Ok(SchematicBetaDemo {
        context,
        alpha,
        bool_type,
        alpha_identity_type,
        bool_identity_type,
        y_alpha,
        identity_alpha,
        generic_conclusion,
        y_bool,
        identity_bool,
        bool_conclusion,
        truth,
        concrete_conclusion,
    })
}

/// Failure in checked library construction or proof replay.
#[derive(Debug)]
pub enum Error {
    /// Checked type construction failed.
    Type(TypeError),
    /// Checked term construction failed.
    Term(TermError),
    /// Checked context construction failed.
    Context(ContextError),
    /// Public LCF proof replay failed.
    Proof(ProofError),
    /// A derived proof did not produce its independently constructed canonical endpoint.
    UnexpectedConclusion {
        /// Above-TCB construction stage.
        stage: &'static str,
        /// Independently interned expected term.
        expected: TermId,
        /// Term returned by checked proof replay.
        actual: TermId,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Type(error) => write!(formatter, "HOL type construction failed: {error}"),
            Self::Term(error) => write!(formatter, "HOL term construction failed: {error}"),
            Self::Context(error) => write!(formatter, "HOL context construction failed: {error}"),
            Self::Proof(error) => write!(formatter, "HOL proof replay failed: {error}"),
            Self::UnexpectedConclusion {
                stage,
                expected,
                actual,
            } => write!(
                formatter,
                "HOL {stage} produced term {}, expected canonical term {}",
                actual.get(),
                expected.get()
            ),
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Context(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::UnexpectedConclusion { .. } => None,
        }
    }
}

impl From<TypeError> for Error {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<TermError> for Error {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ContextError> for Error {
    fn from(error: ContextError) -> Self {
        Self::Context(error)
    }
}

impl From<ProofError> for Error {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

#[cfg(test)]
mod tests {
    use covalence_nucleus::{AllowAll, Connection, TermView, TypeView};

    use super::{Definitions, prove_infinity_successor_nonzero, prove_schematic_beta};

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
    fn checked_all_elim_derives_the_predicate_instance() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let definitions = Definitions::new(&mut connection).unwrap();
        let bool_type = definitions.bool_type();
        let bound = connection.insert_bound_term(0, bool_type).unwrap();
        let identity = connection.insert_lambda(bool_type, bound).unwrap();
        let argument = connection.insert_bool_term(false).unwrap();
        let plan = definitions
            .prepare_all_elim(&mut connection, bool_type, identity, argument)
            .unwrap();
        let context = connection.define_context([plan.universal()]).unwrap();

        connection
            .with_proof_session(|mut proof| {
                let universal = proof.prove_hypothesis(context, plan.universal())?;
                let theorem = plan.prove(&mut proof, &universal)?;
                assert_eq!(theorem.context(), context);
                assert_eq!(theorem.conclusion(), plan.conclusion());
                Ok::<_, covalence_nucleus::ProofError>(())
            })
            .unwrap();
    }

    #[test]
    fn checked_all_elim_rejects_an_unrelated_theorem() {
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

        connection.with_proof_session(|mut proof| {
            let theorem = proof.prove_hypothesis(context, unrelated).unwrap();
            assert!(plan.prove(&mut proof, &theorem).is_err());
        });
    }

    #[test]
    fn infinity_demo_preserves_both_assumptions_and_persists_exact_result() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let demo = prove_infinity_successor_nonzero(&mut connection, 10, 20, 30).unwrap();

        assert_eq!(connection.context_members(demo.context).unwrap(), {
            let mut members = vec![
                demo.successor_nonzero_assumption,
                demo.successor_injective_assumption,
            ];
            members.sort_unstable();
            members
        });
        assert!(
            connection
                .proved_judgement(demo.context, demo.conclusion)
                .unwrap()
        );
        assert!(matches!(
            connection.type_view(demo.ind_type).unwrap(),
            TypeView::Base { symbol: 10 }
        ));

        let TermView::Equality { left, right } = connection.term(demo.conclusion).unwrap() else {
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
        assert_eq!(zero, demo.zero);
        assert!(matches!(
            connection.term(successor_zero).unwrap(),
            TermView::Application {
                function,
                argument
            } if function == demo.successor && argument == demo.zero
        ));
    }

    #[test]
    fn schematic_beta_persists_generic_type_and_term_instances() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let demo = prove_schematic_beta(&mut connection, 700, 701).unwrap();

        assert!(matches!(
            connection.type_view(demo.alpha).unwrap(),
            TypeView::Free { symbol: 700 }
        ));
        assert!(matches!(
            connection.type_view(demo.bool_type).unwrap(),
            TypeView::Bool
        ));
        assert!(matches!(
            connection.type_view(demo.alpha_identity_type).unwrap(),
            TypeView::Arrow { domain, codomain }
                if domain == demo.alpha && codomain == demo.alpha
        ));
        assert!(matches!(
            connection.type_view(demo.bool_identity_type).unwrap(),
            TypeView::Arrow { domain, codomain }
                if domain == demo.bool_type && codomain == demo.bool_type
        ));

        for conclusion in [
            demo.generic_conclusion,
            demo.bool_conclusion,
            demo.concrete_conclusion,
        ] {
            assert!(
                connection
                    .proved_judgement(demo.context, conclusion)
                    .unwrap()
            );
        }

        assert_beta_shape(
            &mut connection,
            demo.generic_conclusion,
            demo.identity_alpha,
            demo.y_alpha,
        );
        assert_beta_shape(
            &mut connection,
            demo.bool_conclusion,
            demo.identity_bool,
            demo.y_bool,
        );
        assert_beta_shape(
            &mut connection,
            demo.concrete_conclusion,
            demo.identity_bool,
            demo.truth,
        );
        assert!(matches!(
            connection.term(demo.truth).unwrap(),
            TermView::Bool(true)
        ));
    }

    fn assert_beta_shape(
        connection: &mut Connection<covalence_nucleus::Hol<AllowAll>>,
        conclusion: covalence_nucleus::TermId,
        identity: covalence_nucleus::TermId,
        argument: covalence_nucleus::TermId,
    ) {
        let TermView::Equality { left, right } = connection.term(conclusion).unwrap() else {
            panic!("beta conclusion must be an equality");
        };
        assert_eq!(right, argument);
        assert!(matches!(
            connection.term(left).unwrap(),
            TermView::Application {
                function,
                argument: actual_argument,
            } if function == identity && actual_argument == argument
        ));
    }
}
