use super::{
    AllowAll, Connection, ConnectionId, ContextId, ExpectedKernelIdentity, Hol, KernelId,
    LocalConnection, Repl, RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact, prepare_retained_trusted_hol_state,
    produce_signed_natlike_artifact, retain_signed_natlike_artifact,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    Conversion, ExportId, HolImageCounts, Kernel, NamespaceExport, ProofError, ProofSession,
    TermId, TermView, TypeId, TypeView, ValidatedHolImage,
};

const CONJUNCTION_ORACLE: &str = "(LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true)))))";
const P_ORACLE: &str = "(APP (LAM:(I->I) (EQ (LAM:I (EQ (LAM:I (EQ (APP (APP AND (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I))) (EQ #1:I #0:I)) (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I)))) (LAM:I true))) (LAM:I true))) s)";
const Q_ORACLE: &str = "(EQ (APP (LAM:(I->I) (EQ (LAM:I (APP (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I)) (EPS (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I))))) (LAM:I true))) s) false)";

#[derive(Clone, Copy)]
struct SourceSyntax {
    ind: TypeId,
    property: TermId,
    successor: TermId,
}

#[derive(Clone, Copy)]
struct ConjunctPlan {
    conjunction: TermId,
    left_conjunct: TermId,
    right_conjunct: TermId,
    equality_left: TermId,
    equality_right: TermId,
    selector: TermId,
    symmetry_predicate: TermId,
    projection: TermId,
}

fn named_export(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: covalence_nucleus::NamespaceId,
    name: &str,
) -> Result<NamespaceExport, SignedHolRoundTripError> {
    connection
        .resolve_export_name(namespace, name)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
        .map(|(_, export)| export.value)
        .ok_or_else(|| {
            SignedHolRoundTripError::at(
                "nonsurjective-source-resolved",
                format_args!("missing source export {name}"),
            )
        })
}

fn resolve_source(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: covalence_nucleus::NamespaceId,
    expected_context: ContextId,
    expected_conclusion: TermId,
) -> Result<SourceSyntax, SignedHolRoundTripError> {
    let NamespaceExport::Context(context) =
        named_export(connection, namespace, "empty-assumption-context")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source context export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(conclusion) =
        named_export(connection, namespace, "dedekind-infinity-assumption")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source conclusion export has the wrong sort",
        ));
    };
    let NamespaceExport::Type(ind) = named_export(connection, namespace, "ind")? else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source ind export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(property) =
        named_export(connection, namespace, "dedekind-endomap-property")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source property export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor) = named_export(connection, namespace, "successor")? else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source successor export has the wrong sort",
        ));
    };
    if context != expected_context || conclusion != expected_conclusion {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "typed source coordinates differ from the exact named exports",
        ));
    }
    let TermView::Application { function, argument } = connection
        .term(conclusion)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "inherited conclusion is not an application",
        ));
    };
    if function != property || argument != successor {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "inherited conclusion is not exact PROPERTY successor",
        ));
    }
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?;
    let endomap = connection
        .insert_arrow_type(ind, ind)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?;
    let property_type = connection
        .insert_arrow_type(endomap, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?;
    if connection
        .term_type(successor)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
        != endomap
        || connection
            .term_type(property)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
            != property_type
        || connection
            .term_type(conclusion)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
            != bool_type
        || !connection
            .term_is_locally_closed(conclusion)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-resolved", error))?
    {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-source-resolved",
            "source successor, property, or conclusion has the wrong type or closure",
        ));
    }
    Ok(SourceSyntax {
        ind,
        property,
        successor,
    })
}

fn normalize_conjunction<'brand>(
    proof: &mut ProofSession<'brand, AllowAll>,
    conjunction: TermId,
    left: TermId,
    right: TermId,
) -> Result<Conversion<'brand>, ProofError> {
    let first = proof.conversion_beta(conjunction, left)?;
    let right_reflexive = proof.conversion_reflexivity(right)?;
    let applied = proof.conversion_application(&first, &right_reflexive)?;
    let second_abstraction = first.right();
    let second = proof.conversion_beta(second_abstraction, right)?;
    proof.conversion_transitivity(&applied, &second)
}

fn normalize_projection<'brand>(
    proof: &mut ProofSession<'brand, AllowAll>,
    projection: TermId,
    function: TermId,
    selector: TermId,
    first_argument: TermId,
    second_argument: TermId,
) -> Result<Conversion<'brand>, ProofError> {
    let project = proof.conversion_beta(projection, function)?;
    let apply_selector = proof.conversion_beta(function, selector)?;
    let projected = proof.conversion_transitivity(&project, &apply_selector)?;
    let selector_first = proof.conversion_beta(selector, first_argument)?;
    let second_reflexive = proof.conversion_reflexivity(second_argument)?;
    let selector_applied = proof.conversion_application(&selector_first, &second_reflexive)?;
    let second_abstraction = selector_first.right();
    let selector_second = proof.conversion_beta(second_abstraction, second_argument)?;
    let selected = proof.conversion_transitivity(&selector_applied, &selector_second)?;
    proof.conversion_transitivity(&projected, &selected)
}

fn render_type(
    connection: &mut Connection<Hol<AllowAll>>,
    ty: TypeId,
    ind: TypeId,
) -> Result<String, SignedHolRoundTripError> {
    if ty == ind {
        return Ok("I".to_owned());
    }
    match connection
        .type_view(ty)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-q-oracle", error))?
    {
        TypeView::Bool => Ok("B".to_owned()),
        TypeView::Arrow { domain, codomain } => Ok(format!(
            "({}->{})",
            render_type(connection, domain, ind)?,
            render_type(connection, codomain, ind)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            "nonsurjective-q-oracle",
            "right conjunct contains a non-profile type",
        )),
    }
}

fn render_profile_term(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
    ind: TypeId,
    successor: TermId,
    conjunction: TermId,
    root: TermId,
) -> Result<String, SignedHolRoundTripError> {
    if term != root {
        if term == successor {
            return Ok("s".to_owned());
        }
        if term == conjunction {
            return Ok("AND".to_owned());
        }
    }
    match connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-q-oracle", error))?
    {
        TermView::Bool(true) => Ok("true".to_owned()),
        TermView::Bool(false) => Ok("false".to_owned()),
        TermView::Bound { index } => {
            let ty = connection
                .term_type(term)
                .map_err(|error| SignedHolRoundTripError::at("nonsurjective-q-oracle", error))?;
            Ok(format!("#{index}:{}", render_type(connection, ty, ind)?))
        }
        TermView::Application { function, argument } => Ok(format!(
            "(APP {} {})",
            render_profile_term(connection, function, ind, successor, conjunction, root)?,
            render_profile_term(connection, argument, ind, successor, conjunction, root)?
        )),
        TermView::Lambda {
            parameter_type,
            body,
        } => Ok(format!(
            "(LAM:{} {})",
            render_type(connection, parameter_type, ind)?,
            render_profile_term(connection, body, ind, successor, conjunction, root)?
        )),
        TermView::Equality { left, right } => Ok(format!(
            "(EQ {} {})",
            render_profile_term(connection, left, ind, successor, conjunction, root)?,
            render_profile_term(connection, right, ind, successor, conjunction, root)?
        )),
        TermView::Epsilon { predicate } => Ok(format!(
            "(EPS {})",
            render_profile_term(connection, predicate, ind, successor, conjunction, root)?
        )),
        TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::TypeLambda { .. }
        | TermView::TypeApplication { .. } => Err(SignedHolRoundTripError::invalid(
            "nonsurjective-q-oracle",
            "right conjunct contains a non-profile term",
        )),
    }
}

fn recover_exact_conjuncts(
    connection: &mut Connection<Hol<AllowAll>>,
    source: SourceSyntax,
) -> Result<(TermId, TermId, TermId, TypeId), SignedHolRoundTripError> {
    let reduct = connection
        .with_proof_session(|mut proof| {
            proof
                .conversion_beta(source.property, source.successor)
                .map(|conversion| conversion.right())
        })
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-beta", error))?;
    let TermView::Application {
        function: partial,
        argument: right_conjunct,
    } = connection
        .term(reduct)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-property-shape",
            "PROPERTY successor reduct is not curried AND p q",
        ));
    };
    let TermView::Application {
        function: conjunction,
        argument: left_conjunct,
    } = connection
        .term(partial)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-property-shape",
            "PROPERTY successor reduct is not curried AND p q",
        ));
    };
    let exact_terms = [
        (conjunction, CONJUNCTION_ORACLE),
        (left_conjunct, P_ORACLE),
        (right_conjunct, Q_ORACLE),
    ];
    for (term, expected) in exact_terms {
        if render_profile_term(
            connection,
            term,
            source.ind,
            source.successor,
            conjunction,
            term,
        )? != expected
        {
            return Err(SignedHolRoundTripError::invalid(
                "nonsurjective-property-shape",
                "AND, INJ successor, or NOT(SURJ successor) differs from its exact oracle",
            ));
        }
    }
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?;
    if connection
        .term_type(left_conjunct)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
        != bool_type
        || connection
            .term_type(right_conjunct)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
            != bool_type
        || !connection
            .term_is_locally_closed(left_conjunct)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
        || !connection
            .term_is_locally_closed(right_conjunct)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-property-shape", error))?
    {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-property-shape",
            "recovered conjuncts are not closed Boolean propositions",
        ));
    }
    Ok((conjunction, left_conjunct, right_conjunct, bool_type))
}

fn prepare_conjunct_plan(
    connection: &mut Connection<Hol<AllowAll>>,
    source: SourceSyntax,
) -> Result<ConjunctPlan, SignedHolRoundTripError> {
    let (conjunction, left_conjunct, right_conjunct, bool_type) =
        recover_exact_conjuncts(connection, source)?;
    let normalized = connection
        .with_proof_session(|mut proof| {
            normalize_conjunction(&mut proof, conjunction, left_conjunct, right_conjunct)
                .map(|conversion| conversion.right())
        })
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?;
    let TermView::Equality {
        left: equality_left,
        right: equality_right,
    } = connection
        .term(normalized)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-and-normalized",
            "canonical AND p q did not normalize to equality",
        ));
    };
    let selector_body = connection
        .insert_bound_term(0, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let selector_body = connection
        .insert_lambda(bool_type, selector_body)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let selector = connection
        .insert_lambda(bool_type, selector_body)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let function_type = connection
        .term_type(equality_left)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    if connection
        .term_type(equality_right)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?
        != function_type
    {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-selector-built",
            "AND equality endpoints have different types",
        ));
    }
    verify_normalized_conjunction(
        connection,
        equality_left,
        equality_right,
        left_conjunct,
        right_conjunct,
        bool_type,
        function_type,
    )?;
    let symmetry_variable = connection
        .insert_bound_term(0, function_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let symmetry_body = connection
        .insert_equality(symmetry_variable, equality_left)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let symmetry_predicate = connection
        .insert_lambda(function_type, symmetry_body)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let projection_variable = connection
        .insert_bound_term(0, function_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let projection_body = connection
        .insert_application(projection_variable, selector)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    let projection = connection
        .insert_lambda(function_type, projection_body)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-selector-built", error))?;
    Ok(ConjunctPlan {
        conjunction,
        left_conjunct,
        right_conjunct,
        equality_left,
        equality_right,
        selector,
        symmetry_predicate,
        projection,
    })
}

fn application_pair(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
) -> Result<(TermId, TermId), SignedHolRoundTripError> {
    let TermView::Application { function, argument } = connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-and-normalized",
            "normalized conjunction endpoint has the wrong application shape",
        ));
    };
    Ok((function, argument))
}

fn verify_normalized_conjunction(
    connection: &mut Connection<Hol<AllowAll>>,
    left: TermId,
    right: TermId,
    p: TermId,
    q: TermId,
    bool_type: TypeId,
    function_type: TypeId,
) -> Result<(), SignedHolRoundTripError> {
    let bool_to_bool = connection
        .insert_arrow_type(bool_type, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?;
    let binary_type = connection
        .insert_arrow_type(bool_type, bool_to_bool)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?;
    let expected_function_type = connection
        .insert_arrow_type(binary_type, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?;
    let TermView::Lambda {
        parameter_type: left_parameter,
        body: left_body,
    } = connection
        .term(left)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-and-normalized",
            "normalized left endpoint is not a lambda",
        ));
    };
    let TermView::Lambda {
        parameter_type: right_parameter,
        body: right_body,
    } = connection
        .term(right)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-and-normalized",
            "normalized right endpoint is not a lambda",
        ));
    };
    let (left_partial, left_second) = application_pair(connection, left_body)?;
    let (left_choice, left_first) = application_pair(connection, left_partial)?;
    let (right_partial, right_second) = application_pair(connection, right_body)?;
    let (right_choice, right_first) = application_pair(connection, right_partial)?;
    let truth = connection
        .insert_bool_term(true)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?;
    let exact_choice = |view| matches!(view, TermView::Bound { index: 0 });
    if function_type != expected_function_type
        || left_parameter != binary_type
        || right_parameter != binary_type
        || left_first != p
        || left_second != q
        || right_first != truth
        || right_second != truth
        || !exact_choice(
            connection.term(left_choice).map_err(|error| {
                SignedHolRoundTripError::at("nonsurjective-and-normalized", error)
            })?,
        )
        || !exact_choice(
            connection.term(right_choice).map_err(|error| {
                SignedHolRoundTripError::at("nonsurjective-and-normalized", error)
            })?,
        )
        || connection
            .term_type(left_choice)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
            != binary_type
        || connection
            .term_type(right_choice)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-and-normalized", error))?
            != binary_type
    {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-and-normalized",
            "canonical AND did not normalize to exact selector functions",
        ));
    }
    Ok(())
}

fn derive_right_conjunct(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    inherited_conclusion: TermId,
    source: SourceSyntax,
    plan: ConjunctPlan,
) -> Result<(), SignedHolRoundTripError> {
    let persisted = connection
        .with_proof_session(|mut proof| {
            let Some(inherited) = proof.load_theorem(context, inherited_conclusion)? else {
                return Ok(false);
            };
            let property_beta = proof.conversion_beta(source.property, source.successor)?;
            let conjunction_theorem = proof.convert_theorem(&inherited, &property_beta)?;
            let conjunction = normalize_conjunction(
                &mut proof,
                plan.conjunction,
                plan.left_conjunct,
                plan.right_conjunct,
            )?;
            let left_equals_right = proof.convert_theorem(&conjunction_theorem, &conjunction)?;

            let left_reflexive = proof.prove_reflexivity(context, plan.equality_left)?;
            let symmetry_left =
                proof.conversion_beta(plan.symmetry_predicate, plan.equality_left)?;
            let symmetry_left = proof.conversion_symmetry(&symmetry_left)?;
            let predicate_left = proof.convert_theorem(&left_reflexive, &symmetry_left)?;
            let predicate_right = proof.equality_substitution(
                &left_equals_right,
                plan.symmetry_predicate,
                &predicate_left,
            )?;
            let symmetry_right =
                proof.conversion_beta(plan.symmetry_predicate, plan.equality_right)?;
            let right_equals_left = proof.convert_theorem(&predicate_right, &symmetry_right)?;

            let truth = proof.prove_truth(context)?;
            let true_term = truth.conclusion();
            let right_projection = normalize_projection(
                &mut proof,
                plan.projection,
                plan.equality_right,
                plan.selector,
                true_term,
                true_term,
            )?;
            let true_to_projection = proof.conversion_symmetry(&right_projection)?;
            let projected_right = proof.convert_theorem(&truth, &true_to_projection)?;
            let projected_left = proof.equality_substitution(
                &right_equals_left,
                plan.projection,
                &projected_right,
            )?;
            let left_projection = normalize_projection(
                &mut proof,
                plan.projection,
                plan.equality_left,
                plan.selector,
                plan.left_conjunct,
                plan.right_conjunct,
            )?;
            let right_conjunct = proof.convert_theorem(&projected_left, &left_projection)?;
            if right_conjunct.conclusion() != plan.right_conjunct {
                return Err(ProofError::ConversionPremiseMismatch {
                    expected: plan.right_conjunct,
                    actual: right_conjunct.conclusion(),
                });
            }
            proof.persist_theorem(&right_conjunct)?;
            Ok(true)
        })
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-derived", error))?;
    if !persisted {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-derived",
            "inherited PROPERTY successor judgement is absent",
        ));
    }
    Ok(())
}

/// Signed extension containing the branded right-conjunct derivation.
pub struct SignedNonsurjectiveConjunct {
    artifact: SignedHolArtifact,
    natlike_namespace: covalence_nucleus::NamespaceId,
    context: ContextId,
    inherited_infinity: TermId,
    conclusion: TermId,
}

impl SignedNonsurjectiveConjunct {
    /// Returns the exact signed image.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the exact inherited namespace containing the `NatLike` syntax.
    #[must_use]
    pub const fn natlike_namespace(&self) -> covalence_nucleus::NamespaceId {
        self.natlike_namespace
    }

    /// Returns the empty theorem context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the inherited signed Dedekind-infinity assumption conclusion.
    #[must_use]
    pub const fn inherited_infinity(&self) -> TermId {
        self.inherited_infinity
    }

    /// Returns exact `NOT(SURJ successor)`.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Returns the authority-safe presentation label.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-nonsurjective-conjunct"
    }

    /// Renders an authority-safe sidecar for the exact signed kernel state.
    ///
    /// The theorem is kernel-derived from the separately signed
    /// Dedekind-infinity assumption. The signature authenticates the exact
    /// database bytes; it is not itself a proof of the derived theorem.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\ntheorem=not-surjective-successor\nsignature-scope=exact-database-bytes\nsignature-meaning=authentication-not-proof\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn export_namespace(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    conclusion: TermId,
    source: SourceSyntax,
) -> Result<covalence_nucleus::NamespaceId, SignedHolRoundTripError> {
    let namespace = connection
        .create_namespace(None, Some("nonsurjective-conjunct-v1"))
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-exported", error))?;
    let exports = [
        (0, NamespaceExport::Context(context), "empty-context"),
        (
            1,
            NamespaceExport::Term(conclusion),
            "not-surjective-successor",
        ),
        (2, NamespaceExport::Type(source.ind), "ind"),
        (
            3,
            NamespaceExport::Term(source.property),
            "dedekind-endomap-property",
        ),
        (4, NamespaceExport::Term(source.successor), "successor"),
    ];
    for (slot, value, name) in exports {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-exported", error))?;
    }
    Ok(namespace)
}

fn verify_raw_profile(
    raw: &covalence_neutron::Connection,
    namespace: covalence_nucleus::NamespaceId,
    context: ContextId,
    inherited: TermId,
    conclusion: TermId,
    source: SourceSyntax,
) -> Result<(), SignedHolRoundTripError> {
    let connection = raw.sqlite();
    let namespace_profile = connection
        .query_row(
            "SELECT name, parent_namespace_id, source_import_id, source_namespace_id
             FROM hol_namespace WHERE namespace_id = ?1",
            [namespace.get()],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, Option<i64>>(1)?,
                    row.get::<_, Option<i64>>(2)?,
                    row.get::<_, Option<i64>>(3)?,
                ))
            },
        )
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?;
    if namespace_profile != ("nonsurjective-conjunct-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-profile-checked",
            "derived namespace differs from the exact local profile",
        ));
    }
    let mut exports = connection
        .prepare(
            "SELECT export_id, sort, local_id, name FROM hol_namespace_export
             WHERE namespace_id = ?1 ORDER BY export_id",
        )
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?;
    let actual_exports = exports
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?;
    let expected_exports = vec![
        (
            0,
            "context".to_owned(),
            context.get(),
            "empty-context".to_owned(),
        ),
        (
            1,
            "term".to_owned(),
            conclusion.get(),
            "not-surjective-successor".to_owned(),
        ),
        (2, "type".to_owned(), source.ind.get(), "ind".to_owned()),
        (
            3,
            "term".to_owned(),
            source.property.get(),
            "dedekind-endomap-property".to_owned(),
        ),
        (
            4,
            "term".to_owned(),
            source.successor.get(),
            "successor".to_owned(),
        ),
    ];
    if actual_exports != expected_exports {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-profile-checked",
            "derived exports differ from the exact slot/sort/name/value profile",
        ));
    }
    let mut judgements = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?;
    let actual_judgements = judgements
        .query_map([], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-profile-checked", error))?;
    let mut expected_judgements = vec![
        (context.get(), inherited.get()),
        (context.get(), conclusion.get()),
    ];
    expected_judgements.sort_unstable();
    if actual_judgements != expected_judgements {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-profile-checked",
            "kernel state must contain exactly inherited PROPERTY successor and derived q",
        ));
    }
    Ok(())
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 123,
        contexts: 1,
        members: 0,
        untrusted_judgement_rows: 2,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 4,
        namespace_exports: 19,
        import_references: 2,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 2,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-image-validated",
            "derived image differs from the frozen complete-state profile",
        ));
    }
    Ok(())
}

/// Derives, persists, exports, and signs the exact inherited right conjunct.
///
/// # Errors
///
/// Returns the first source, branded-rule, persistence, export, validation, or signing error.
pub fn produce_signed_nonsurjective_conjunct(
    producer: &Kernel,
) -> Result<SignedNonsurjectiveConjunct, SignedHolRoundTripError> {
    let source_artifact = produce_signed_natlike_artifact(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-staging-opened", error))?;
    let (owner, retained) =
        retain_signed_natlike_artifact(producer, &mut staging, &source_artifact)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, owner, &retained, AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("nonsurjective-source-opened", error))?;
    let source_namespace =
        covalence_nucleus::NamespaceId::from_i64(source_artifact.artifact().namespace_id());
    let source = resolve_source(
        &mut connection,
        source_namespace,
        source_artifact.context(),
        source_artifact.infinity(),
    )?;
    let plan = prepare_conjunct_plan(&mut connection, source)?;
    derive_right_conjunct(
        &mut connection,
        source_artifact.context(),
        source_artifact.infinity(),
        source,
        plan,
    )?;
    let namespace = export_namespace(
        &mut connection,
        source_artifact.context(),
        plan.right_conjunct,
        source,
    )?;
    let snapshot = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-signed", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(snapshot.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("nonsurjective-image-copied", error))?;
    verify_raw_profile(
        &raw,
        namespace,
        source_artifact.context(),
        source_artifact.infinity(),
        plan.right_conjunct,
        source,
    )?;
    let validated = ValidatedHolImage::validate(snapshot.image().bytes())
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let attestation = snapshot.attestation();
    Ok(SignedNonsurjectiveConjunct {
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image: validated.bytes().to_vec(),
            schema: attestation.schema(),
            image_hash: attestation.image(),
            signer: attestation.signer(),
            public_key: attestation.public_key().to_vec(),
            signature: attestation.signature().to_vec(),
        },
        natlike_namespace: source_namespace,
        context: source_artifact.context(),
        inherited_infinity: source_artifact.infinity(),
        conclusion: plan.right_conjunct,
    })
}

/// Produces and retains the signed conjunct derivation in a fresh receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_nonsurjective_conjunct(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<
    (
        SignedNonsurjectiveConjunct,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    let artifact = produce_signed_nonsurjective_conjunct(producer)?;
    let (owner, retained) = retain_signed_nonsurjective_conjunct(producer, directory, &artifact)?;
    Ok((artifact, owner, retained))
}

/// Authenticates and retains one already-produced signed conjunct derivation.
///
/// # Errors
///
/// Returns the first authentication, trust, import, receiver, or directory error.
pub fn retain_signed_nonsurjective_conjunct(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: &SignedNonsurjectiveConjunct,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-signer-selected", error))?;
    let independent = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("nonsurjective-signer-selected", error))?;
    if expected != independent {
        return Err(SignedHolRoundTripError::invalid(
            "nonsurjective-signer-selected",
            "REPL local endpoint key differs from the conjunct signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("nonsurjective-receiver-opened", error))?;
    let (owner, retained) = trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        i64::MAX,
    )?;
    Ok((owner, retained))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;

    #[test]
    fn derives_persists_signs_receives_and_reopens_right_conjunct() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_nonsurjective_conjunct(&kernel, &mut directory).unwrap();
        assert_eq!(artifact.kind(), "signed-nonsurjective-conjunct");
        assert!(artifact.attestation_text().starts_with(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\n"
        ));
        assert!(
            artifact
                .attestation_text()
                .contains("signature-meaning=authentication-not-proof")
        );
        assert_eq!(
            ValidatedHolImage::validate(artifact.artifact().image())
                .unwrap()
                .counts()
                .untrusted_judgement_rows,
            2
        );
        assert_eq!(retained.received().context_id(), artifact.context().get());
        assert_eq!(
            retained.received().conclusion_id(),
            artifact.conclusion().get()
        );
        let opened =
            open_retained_trusted_hol_as_managed_state(&mut directory, owner, &retained, AllowAll)
                .unwrap();
        assert_eq!(opened.context_id(), artifact.context().get());
        assert_eq!(opened.conclusion_id(), artifact.conclusion().get());
        let child = directory
            .get_mut(opened.connection())
            .unwrap()
            .hol_mut()
            .unwrap();
        let (inherited_loaded, derived_loaded) = child
            .with_proof_session(|mut proof| {
                Ok::<_, ProofError>((
                    proof
                        .load_theorem(artifact.context(), artifact.inherited_infinity())?
                        .is_some(),
                    proof
                        .load_theorem(artifact.context(), artifact.conclusion())?
                        .is_some(),
                ))
            })
            .unwrap();
        assert!(inherited_loaded);
        assert!(derived_loaded);
    }
}
