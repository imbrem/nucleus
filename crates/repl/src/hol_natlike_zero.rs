use super::{
    AllIntroApplied, AllowAll, AndElim, Connection, ConnectionId, ContextId,
    ExpectedKernelIdentity, Hol, ImpIntro, KernelId, LocalConnection, Repl,
    RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact, prepare_retained_trusted_hol_state,
    produce_signed_nonsurjective_conjunct, retain_signed_nonsurjective_conjunct,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, NamespaceId, TermError, TermId, TypeId,
    ValidatedHolImage,
};

#[derive(Clone, Copy)]
struct SourceSyntax {
    ind: TypeId,
    successor: TermId,
    zero: TermId,
    successor_closed: TermId,
    natlike: TermId,
}

#[derive(Clone, Copy)]
struct ProofGraph {
    successor_closed: TermId,
    natlike: TermId,
    zero: TermId,
    predicate: TermId,
    closed_predicate: TermId,
    closed_body: TermId,
    candidate: TermId,
    candidate_instance: TermId,
    universal: TermId,
    implication: TermId,
    conclusion: TermId,
}

struct ProofPlan {
    graph: ProofGraph,
    left_elimination: AndElim,
    implication_introduction: ImpIntro,
    universal_introduction: AllIntroApplied,
}

fn named_export(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: NamespaceId,
    name: &str,
) -> Result<NamespaceExport, SignedHolRoundTripError> {
    connection
        .resolve_export_name(namespace, name)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
        .map(|(_, export)| export.value)
        .ok_or_else(|| {
            SignedHolRoundTripError::at(
                "natlike-zero-source-resolved",
                format_args!("missing exact source export {name}"),
            )
        })
}

fn resolve_source(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: NamespaceId,
    expected_context: ContextId,
    expected_infinity: TermId,
) -> Result<SourceSyntax, SignedHolRoundTripError> {
    let NamespaceExport::Context(context) =
        named_export(connection, namespace, "empty-assumption-context")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike context export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(infinity) =
        named_export(connection, namespace, "dedekind-infinity-assumption")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike infinity export has the wrong sort",
        ));
    };
    let NamespaceExport::Type(ind) = named_export(connection, namespace, "ind")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike individual type export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor) = named_export(connection, namespace, "successor")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike successor export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(zero) = named_export(connection, namespace, "zero")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike zero export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor_closed) =
        named_export(connection, namespace, "successor-closed")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike closure export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(natlike) = named_export(connection, namespace, "nat-like")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike predicate export has the wrong sort",
        ));
    };
    if context != expected_context || infinity != expected_infinity {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "typed source coordinates differ from the exact NatLike exports",
        ));
    }
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?;
    let predicate_type = connection
        .insert_arrow_type(ind, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?;
    let endomap_type = connection
        .insert_arrow_type(ind, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?;
    if connection
        .term_type(successor_closed)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
        != connection
            .insert_arrow_type(predicate_type, bool_type)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
        || connection
            .term_type(natlike)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
            != predicate_type
        || connection
            .term_type(zero)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
            != ind
        || connection
            .term_type(successor)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
            != endomap_type
        || !connection
            .term_is_locally_closed(successor_closed)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
        || !connection
            .term_is_locally_closed(natlike)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-resolved", error))?
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "NatLike source exports have the wrong checked types",
        ));
    }
    Ok(SourceSyntax {
        ind,
        successor,
        zero,
        successor_closed,
        natlike,
    })
}

fn apply2(
    connection: &mut Connection<Hol<AllowAll>>,
    function: TermId,
    first: TermId,
    second: TermId,
) -> Result<TermId, TermError> {
    let partial = connection.insert_application(function, first)?;
    connection.insert_application(partial, second)
}

fn conjunction(
    connection: &mut Connection<Hol<AllowAll>>,
    bool_type: TypeId,
    truth: TermId,
) -> Result<TermId, TermError> {
    let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type)?;
    let binary = connection.insert_arrow_type(bool_type, bool_to_bool)?;
    let choice = connection.insert_bound_term(0, binary)?;
    let left = connection.insert_bound_term(2, bool_type)?;
    let right = connection.insert_bound_term(1, bool_type)?;
    let selected = apply2(connection, choice, left, right)?;
    let selected_truth = apply2(connection, choice, truth, truth)?;
    let selected = connection.insert_lambda(binary, selected)?;
    let selected_truth = connection.insert_lambda(binary, selected_truth)?;
    let body = connection.insert_equality(selected, selected_truth)?;
    let body = connection.insert_lambda(bool_type, body)?;
    connection.insert_lambda(bool_type, body)
}

fn implication(
    connection: &mut Connection<Hol<AllowAll>>,
    and: TermId,
    antecedent: TermId,
    consequent: TermId,
) -> Result<TermId, TermError> {
    let both = apply2(connection, and, antecedent, consequent)?;
    connection.insert_equality(both, antecedent)
}

fn prepare_proof(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    source: SourceSyntax,
) -> Result<ProofPlan, SignedHolRoundTripError> {
    let stage = "natlike-zero-proof-prepared";
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate_type = connection
        .insert_arrow_type(source.ind, bool_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let truth = connection
        .insert_bool_term(true)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let and = conjunction(connection, bool_type, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate = connection
        .insert_free_term(0x4e_41_54, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let closed_predicate = connection
        .insert_application(source.successor_closed, predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let base = connection
        .insert_application(predicate, source.zero)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let point = connection
        .insert_bound_term(0, source.ind)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let premise = connection
        .insert_application(predicate, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let successor_point = connection
        .insert_application(source.successor, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let successor_case = connection
        .insert_application(predicate, successor_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_body = implication(connection, and, premise, successor_case)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_predicate = connection
        .insert_lambda(source.ind, step_body)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let constant_truth = connection
        .insert_lambda(source.ind, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step = connection
        .insert_equality(step_predicate, constant_truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let candidate_bound = connection
        .insert_bound_term(0, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let candidate_closed = connection
        .insert_application(source.successor_closed, candidate_bound)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let candidate_base = connection
        .insert_application(candidate_bound, source.zero)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let candidate_body = implication(connection, and, candidate_closed, candidate_base)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let candidate = connection
        .insert_lambda(predicate_type, candidate_body)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let candidate_instance = connection
        .insert_application(candidate, predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let all_truth = connection
        .insert_lambda(predicate_type, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let universal = connection
        .insert_equality(candidate, all_truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let conclusion = connection
        .insert_application(source.natlike, source.zero)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let closed_body = apply2(connection, and, base, step)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let exact_implication = implication(connection, and, closed_predicate, base)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let graph = ProofGraph {
        successor_closed: source.successor_closed,
        natlike: source.natlike,
        zero: source.zero,
        predicate,
        closed_predicate,
        closed_body,
        candidate,
        candidate_instance,
        universal,
        implication: exact_implication,
        conclusion,
    };
    Ok(ProofPlan {
        graph,
        left_elimination: AndElim::left(connection, base, step)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        implication_introduction: ImpIntro::prepare(connection, context, closed_predicate, base)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        universal_introduction: AllIntroApplied::prepare(connection, candidate, predicate)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
    })
}

fn derive(
    connection: &mut Connection<Hol<AllowAll>>,
    plan: &ProofPlan,
) -> Result<(), SignedHolRoundTripError> {
    connection.with_proof_session(|mut proof| {
        let closed = proof
            .prove_hypothesis(
                plan.implication_introduction.premise_context(),
                plan.graph.closed_predicate,
            )
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-hypothesis", error))?;
        let closed_beta = proof
            .conversion_beta(plan.graph.successor_closed, plan.graph.predicate)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-closed-beta", error))?;
        if closed_beta.left() != plan.graph.closed_predicate
            || closed_beta.right() != plan.graph.closed_body
        {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-zero-closed-beta",
                "closed P did not reduce to the exact applied AND graph",
            ));
        }
        let conjunction = proof
            .convert_theorem(&closed, &closed_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-closed-beta", error))?;
        let base = plan
            .left_elimination
            .apply(&mut proof, &conjunction)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-and-elim", error))?;
        let implication = plan
            .implication_introduction
            .apply(&mut proof, &base)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-imp-intro", error))?;
        if implication.conclusion() != plan.graph.implication {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-zero-imp-intro",
                "implication introduction returned the wrong exact graph",
            ));
        }
        let candidate_beta = proof
            .conversion_beta(plan.graph.candidate, plan.graph.predicate)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-candidate-beta", error))?;
        if candidate_beta.left() != plan.graph.candidate_instance
            || candidate_beta.right() != plan.graph.implication
        {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-zero-candidate-beta",
                "candidate P did not reduce to the exact implication graph",
            ));
        }
        let candidate_reverse = proof
            .conversion_symmetry(&candidate_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-candidate-beta", error))?;
        let candidate_instance = proof
            .convert_theorem(&implication, &candidate_reverse)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-candidate-beta", error))?;
        let universal = plan
            .universal_introduction
            .apply(&mut proof, &candidate_instance)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-all-intro", error))?;
        if universal.conclusion() != plan.graph.universal {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-zero-all-intro",
                "universal introduction returned the wrong exact graph",
            ));
        }
        let natlike_beta = proof
            .conversion_beta(plan.graph.natlike, plan.graph.zero)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-final-beta", error))?;
        if natlike_beta.left() != plan.graph.conclusion
            || natlike_beta.right() != plan.graph.universal
        {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-zero-final-beta",
                "NatLike zero did not reduce to the exact universal graph",
            ));
        }
        let natlike_reverse = proof
            .conversion_symmetry(&natlike_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-final-beta", error))?;
        let conclusion = proof
            .convert_theorem(&universal, &natlike_reverse)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-final-beta", error))?;
        proof
            .persist_theorem(&conclusion)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-persisted", error))?;
        Ok(())
    })
}

/// Signed extension proving that the selected `zero` satisfies `NatLike`.
pub struct SignedNatLikeZero {
    artifact: SignedHolArtifact,
    natlike_namespace: NamespaceId,
    context: ContextId,
    inherited_infinity: TermId,
    inherited_nonsurjective: TermId,
    conclusion: TermId,
}

impl SignedNatLikeZero {
    /// Returns the exact signed image.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the inherited `NatLike` syntax namespace.
    #[must_use]
    pub const fn natlike_namespace(&self) -> NamespaceId {
        self.natlike_namespace
    }

    /// Returns the empty theorem context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the inherited Dedekind-infinity assumption.
    #[must_use]
    pub const fn inherited_infinity(&self) -> TermId {
        self.inherited_infinity
    }

    /// Returns the previously derived nonsurjectivity conjunct.
    #[must_use]
    pub const fn inherited_nonsurjective(&self) -> TermId {
        self.inherited_nonsurjective
    }

    /// Returns exact applied `NatLike zero`.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Returns the authority-safe artifact label.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-natlike-zero"
    }

    /// Renders an authority-safe sidecar for the exact signed state.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\nprior-theorem=not-surjective-successor\ntheorem=nat-like-zero\nsignature-scope=exact-database-bytes\nsignature-meaning=authentication-not-proof\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn verify_source_judgements(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    infinity: TermId,
    nonsurjective: TermId,
) -> Result<(), SignedHolRoundTripError> {
    connection.with_proof_session(|mut proof| {
        for (name, conclusion) in [
            ("inherited infinity", infinity),
            ("prior nonsurjectivity", nonsurjective),
        ] {
            let present = proof
                .load_theorem(context, conclusion)
                .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-loaded", error))?
                .is_some();
            if !present {
                return Err(SignedHolRoundTripError::at(
                    "natlike-zero-source-loaded",
                    format_args!("missing exact {name} judgement"),
                ));
            }
        }
        Ok(())
    })
}

fn export_namespace(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    conclusion: TermId,
) -> Result<NamespaceId, SignedHolRoundTripError> {
    let namespace = connection
        .create_namespace(None, Some("natlike-zero-v1"))
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-exported", error))?;
    for (slot, value, name) in [
        (0, NamespaceExport::Context(context), "empty-context"),
        (1, NamespaceExport::Term(conclusion), "nat-like-zero"),
    ] {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-exported", error))?;
    }
    Ok(namespace)
}

fn verify_raw_profile(
    raw: &covalence_neutron::Connection,
    namespace: NamespaceId,
    context: ContextId,
    infinity: TermId,
    nonsurjective: TermId,
    conclusion: TermId,
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
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?;
    if namespace_profile != ("natlike-zero-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-profile-checked",
            "derived namespace differs from the exact local profile",
        ));
    }
    let mut exports = connection
        .prepare(
            "SELECT export_id, sort, local_id, name FROM hol_namespace_export
             WHERE namespace_id = ?1 ORDER BY export_id",
        )
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?;
    let actual_exports = exports
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?;
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
            "nat-like-zero".to_owned(),
        ),
    ];
    if actual_exports != expected_exports {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-profile-checked",
            "derived exports differ from the exact slot/sort/name/value profile",
        ));
    }
    let mut judgements = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?;
    let actual_judgements = judgements
        .query_map([], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-profile-checked", error))?;
    let mut expected_judgements = vec![
        (context.get(), infinity.get()),
        (context.get(), nonsurjective.get()),
        (context.get(), conclusion.get()),
    ];
    expected_judgements.sort_unstable();
    if actual_judgements != expected_judgements {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-profile-checked",
            "state must contain exactly infinity, prior q, and NatLike zero",
        ));
    }
    Ok(())
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 266,
        contexts: 3,
        members: 2,
        untrusted_judgement_rows: 3,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 5,
        namespace_exports: 21,
        import_references: 3,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 3,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::at(
            "natlike-zero-image-validated",
            format_args!(
                "complete-state profile differs: actual {:?}, expected {:?}",
                validated.counts(),
                expected
            ),
        ));
    }
    Ok(())
}

/// Derives, persists, exports, and signs exact `empty |- NatLike zero`.
///
/// # Errors
///
/// Returns the first source, proof, persistence, export, validation, or signing error.
pub fn produce_signed_natlike_zero(
    producer: &Kernel,
) -> Result<SignedNatLikeZero, SignedHolRoundTripError> {
    let source_artifact = produce_signed_nonsurjective_conjunct(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-staging-opened", error))?;
    let (owner, retained) =
        retain_signed_nonsurjective_conjunct(producer, &mut staging, &source_artifact)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, owner, &retained, AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("natlike-zero-source-opened", error))?;
    let context = source_artifact.context();
    let infinity = source_artifact.inherited_infinity();
    let nonsurjective = source_artifact.conclusion();
    let source_namespace = NamespaceId::from_i64(source_artifact.artifact().namespace_id());
    let NamespaceExport::Term(exported_nonsurjective) = named_export(
        &mut connection,
        source_namespace,
        "not-surjective-successor",
    )?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "prior derived theorem export has the wrong sort",
        ));
    };
    if exported_nonsurjective != nonsurjective {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-source-resolved",
            "prior derived theorem differs from its exact named export",
        ));
    }
    verify_source_judgements(&mut connection, context, infinity, nonsurjective)?;
    let source = resolve_source(
        &mut connection,
        source_artifact.natlike_namespace(),
        context,
        infinity,
    )?;
    let plan = prepare_proof(&mut connection, context, source)?;
    derive(&mut connection, &plan)?;
    let namespace = export_namespace(&mut connection, context, plan.graph.conclusion)?;
    let snapshot = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-signed", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(snapshot.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-zero-image-copied", error))?;
    verify_raw_profile(
        &raw,
        namespace,
        context,
        infinity,
        nonsurjective,
        plan.graph.conclusion,
    )?;
    let validated = ValidatedHolImage::validate(snapshot.image().bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-image-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let attestation = snapshot.attestation();
    Ok(SignedNatLikeZero {
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image: validated.bytes().to_vec(),
            schema: attestation.schema(),
            image_hash: attestation.image(),
            signer: attestation.signer(),
            public_key: attestation.public_key().to_vec(),
            signature: attestation.signature().to_vec(),
        },
        natlike_namespace: source_artifact.natlike_namespace(),
        context,
        inherited_infinity: infinity,
        inherited_nonsurjective: nonsurjective,
        conclusion: plan.graph.conclusion,
    })
}

/// Authenticates and retains one already-produced signed NatLike-zero derivation.
///
/// # Errors
///
/// Returns the first authentication, trust, import, receiver, or directory error.
pub fn retain_signed_natlike_zero(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: &SignedNatLikeZero,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-signer-selected", error))?;
    let independent = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-zero-signer-selected", error))?;
    if expected != independent {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-zero-signer-selected",
            "REPL local endpoint key differs from the NatLike-zero signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("natlike-zero-receiver-opened", error))?;
    trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        i64::MAX,
    )
}

/// Produces and retains the signed NatLike-zero derivation in a fresh receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_natlike_zero(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<(SignedNatLikeZero, ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError>
{
    let artifact = produce_signed_natlike_zero(producer)?;
    let (owner, retained) = retain_signed_natlike_zero(producer, directory, &artifact)?;
    Ok((artifact, owner, retained))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;
    use covalence_nucleus::TermView;

    #[test]
    fn derives_signs_receives_and_reopens_exact_natlike_zero_state() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_natlike_zero(&kernel, &mut directory).unwrap();
        assert_eq!(artifact.kind(), "signed-natlike-zero");
        assert!(artifact.attestation_text().starts_with(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\n\
             prior-theorem=not-surjective-successor\ntheorem=nat-like-zero\n"
        ));
        assert!(
            artifact
                .attestation_text()
                .contains("signature-meaning=authentication-not-proof")
        );
        assert_eq!(retained.received().context_id(), artifact.context().get());
        assert_eq!(
            retained.received().conclusion_id(),
            artifact.conclusion().get()
        );

        let opened =
            open_retained_trusted_hol_as_managed_state(&mut directory, owner, &retained, AllowAll)
                .unwrap();
        assert_ne!(owner, opened.connection());
        assert_eq!(opened.context_id(), artifact.context().get());
        assert_eq!(opened.conclusion_id(), artifact.conclusion().get());
        let child = directory
            .get_mut(opened.connection())
            .unwrap()
            .hol_mut()
            .unwrap();
        for conclusion in [
            artifact.inherited_infinity(),
            artifact.inherited_nonsurjective(),
            artifact.conclusion(),
        ] {
            let present = child.with_proof_session(|mut proof| {
                proof
                    .load_theorem(artifact.context(), conclusion)
                    .map(|theorem| theorem.is_some())
            });
            assert!(present.unwrap());
        }
        let NamespaceExport::Term(natlike) =
            named_export(child, artifact.natlike_namespace(), "nat-like").unwrap()
        else {
            panic!("nat-like export changed sort")
        };
        let NamespaceExport::Term(zero) =
            named_export(child, artifact.natlike_namespace(), "zero").unwrap()
        else {
            panic!("zero export changed sort")
        };
        assert_eq!(
            child.term(artifact.conclusion()).unwrap(),
            TermView::Application {
                function: natlike,
                argument: zero
            }
        );
        let validated = ValidatedHolImage::validate(artifact.artifact().image()).unwrap();
        assert_eq!(validated.counts().untrusted_judgement_rows, 3);
        assert_eq!(validated.counts().import_references, 3);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 3);
    }

    #[test]
    fn derivation_consumes_no_inherited_theorem_handle() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(0x4e_41_54).unwrap();
        let point = connection.insert_bound_term(0, ind).unwrap();
        let successor = connection.insert_lambda(ind, point).unwrap();
        let syntax = crate::build_natlike_syntax(&mut connection, ind, successor).unwrap();
        let source = SourceSyntax {
            ind,
            successor,
            zero: syntax.zero(),
            successor_closed: syntax.successor_closed(),
            natlike: syntax.natlike(),
        };
        let plan = prepare_proof(&mut connection, ContextId::empty(), source).unwrap();
        let before = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(before.image().counts().untrusted_judgement_rows, 0);
        derive(&mut connection, &plan).unwrap();
        let after = Kernel::ephemeral().export_hol(&mut connection).unwrap();
        assert_eq!(after.image().counts().untrusted_judgement_rows, 1);
        assert!(
            connection
                .proved_judgement(ContextId::empty(), plan.graph.conclusion)
                .unwrap()
        );
    }

    #[test]
    fn signed_receive_rejects_tamper_and_wrong_signer_without_directory_mutation() {
        let producer = Kernel::ephemeral();
        let mut artifact = produce_signed_natlike_zero(&producer).unwrap();
        artifact.artifact.image[0] ^= 1;
        let mut directory = Repl::new(producer.verifying_key().as_bytes()).unwrap();
        assert!(retain_signed_natlike_zero(&producer, &mut directory, &artifact).is_err());
        assert!(directory.connections().unwrap().is_empty());
        assert_eq!(directory.active().unwrap(), None);

        let artifact = produce_signed_natlike_zero(&producer).unwrap();
        let other = Kernel::ephemeral();
        let mut wrong_directory = Repl::new(other.verifying_key().as_bytes()).unwrap();
        assert!(retain_signed_natlike_zero(&producer, &mut wrong_directory, &artifact).is_err());
        assert!(wrong_directory.connections().unwrap().is_empty());
        assert_eq!(wrong_directory.active().unwrap(), None);
    }
}
