use super::{
    AllowAll, AndElim, Connection, ConnectionId, ContextId, ExpectedKernelIdentity, Hol, KernelId,
    LocalConnection, MissingZeroPlan, Repl, RetainedReceivedHolSnapshot, SignedHolArtifact,
    SignedHolRoundTripError, authenticate_pinned_signed_hol_artifact, build_canonical_false,
    prepare_retained_trusted_hol_state, produce_signed_natlike_artifact,
    retain_signed_natlike_artifact, trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, NamespaceId, TermId, TermView, TypeId,
    ValidatedHolImage,
};

const MISSING_ZERO_ORACLE: &str = "(APP missing zero)";

#[derive(Clone, Copy)]
struct SourceSyntax {
    ind: TypeId,
    property: TermId,
    successor: TermId,
    left_conjunct: TermId,
    nonsurjective: TermId,
    surjective: TermId,
    surjective_function: TermId,
    universal: TermId,
    q_transport: TermId,
    predicate: TermId,
    missing: TermId,
    zero: TermId,
}

struct ProofPlan {
    nonsurjective_elimination: AndElim,
    missing_zero: MissingZeroPlan,
}

fn named_export(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: NamespaceId,
    name: &str,
) -> Result<NamespaceExport, SignedHolRoundTripError> {
    connection
        .resolve_export_name(namespace, name)
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-source-resolved", error))?
        .map(|(_, export)| export.value)
        .ok_or_else(|| {
            SignedHolRoundTripError::at(
                "missing-zero-source-resolved",
                format_args!("missing exact source export {name}"),
            )
        })
}

#[allow(clippy::too_many_lines)]
fn resolve_source(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: NamespaceId,
    expected_context: ContextId,
    expected_infinity: TermId,
) -> Result<SourceSyntax, SignedHolRoundTripError> {
    let stage = "missing-zero-source-resolved";
    let NamespaceExport::Context(context) =
        named_export(connection, namespace, "empty-assumption-context")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source context export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(infinity) =
        named_export(connection, namespace, "dedekind-infinity-assumption")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source infinity export has the wrong sort",
        ));
    };
    let NamespaceExport::Type(ind) = named_export(connection, namespace, "ind")? else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source individual type export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(property) =
        named_export(connection, namespace, "dedekind-endomap-property")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source property export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor) = named_export(connection, namespace, "successor")? else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source successor export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(missing) = named_export(connection, namespace, "missing-preimage")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source missing predicate export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(zero) = named_export(connection, namespace, "zero")? else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source zero export has the wrong sort",
        ));
    };
    if context != expected_context || infinity != expected_infinity {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source coordinates differ from the signed NatLike namespace",
        ));
    }

    let TermView::Application { function, argument } = connection
        .term(infinity)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "infinity conclusion is not an application",
        ));
    };
    if function != property || argument != successor {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "infinity conclusion is not exact PROPERTY successor",
        ));
    }
    let property_reduct = connection
        .with_proof_session(|mut proof| {
            proof
                .conversion_beta(property, successor)
                .map(|conversion| conversion.right())
        })
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let TermView::Application {
        function: partial,
        argument: nonsurjective,
    } = connection
        .term(property_reduct)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "property reduct is not curried conjunction",
        ));
    };
    let TermView::Application {
        function: _,
        argument: left_conjunct,
    } = connection
        .term(partial)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "property reduct is not curried conjunction",
        ));
    };

    let falsehood = build_canonical_false(connection)?;
    let TermView::Equality {
        left: surjective,
        right,
    } = connection
        .term(nonsurjective)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "nonsurjectivity is not canonical negation",
        ));
    };
    if right != falsehood {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "nonsurjectivity does not use canonical false",
        ));
    }
    let TermView::Application { function, argument } = connection
        .term(surjective)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "surjectivity is not applied to the selected successor",
        ));
    };
    if argument != successor {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "surjectivity is applied to a different successor",
        ));
    }
    let universal = connection
        .with_proof_session(|mut proof| {
            proof
                .conversion_beta(function, successor)
                .map(|conversion| conversion.right())
        })
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let TermView::Equality {
        left: predicate,
        right: constant_truth,
    } = connection
        .term(universal)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "surjectivity beta endpoint is not a universal",
        ));
    };
    let TermView::Lambda {
        parameter_type,
        body,
    } = connection
        .term(constant_truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "universal right endpoint is not constant truth",
        ));
    };
    if parameter_type != ind
        || !matches!(
            connection
                .term(body)
                .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
            TermView::Bool(true)
        )
    {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "universal right endpoint differs from lambda ind. true",
        ));
    }
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let q_variable = connection
        .insert_bound_term(0, bool_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let q_body = connection
        .insert_equality(q_variable, falsehood)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let q_transport = connection
        .insert_lambda(bool_type, q_body)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate_type = connection
        .insert_arrow_type(ind, bool_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    if connection
        .term_type(predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
        != predicate_type
        || connection
            .term_type(missing)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?
            != predicate_type
        || connection
            .term_type(zero)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?
            != ind
    {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "source predicate, missing, or zero has the wrong checked type",
        ));
    }
    Ok(SourceSyntax {
        ind,
        property,
        successor,
        left_conjunct,
        nonsurjective,
        surjective,
        surjective_function: function,
        universal,
        q_transport,
        predicate,
        missing,
        zero,
    })
}

fn prepare_plan(
    connection: &mut Connection<Hol<AllowAll>>,
    source: SourceSyntax,
) -> Result<ProofPlan, SignedHolRoundTripError> {
    let stage = "missing-zero-plan-prepared";
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let witness = connection
        .insert_free_term(0x4e_41_54_5a, source.ind)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let mut fresh = Vec::with_capacity(3);
    for name in [0x4e_41_54_5b, 0x4e_41_54_5c, 0x4e_41_54_5d] {
        fresh.push(
            connection
                .insert_free_term(name, bool_type)
                .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        );
    }
    let missing_zero = MissingZeroPlan::prepare(
        connection,
        source.predicate,
        source.missing,
        source.zero,
        witness,
        fresh
            .try_into()
            .map_err(|_| SignedHolRoundTripError::invalid(stage, "wrong fresh-variable arity"))?,
    )
    .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let nonsurjective_elimination =
        AndElim::right(connection, source.left_conjunct, source.nonsurjective)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    Ok(ProofPlan {
        nonsurjective_elimination,
        missing_zero,
    })
}

fn derive(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    source_infinity: TermId,
    source: SourceSyntax,
    plan: &ProofPlan,
) -> Result<(), SignedHolRoundTripError> {
    let persisted = connection
        .with_proof_session(|mut proof| {
            let Some(infinity) = proof.load_theorem(context, source_infinity)? else {
                return Ok::<_, super::DerivedRuleError>(false);
            };
            let property_beta = proof.conversion_beta(source.property, source.successor)?;
            let conjunction = proof.convert_theorem(&infinity, &property_beta)?;
            let nonsurjective = plan
                .nonsurjective_elimination
                .apply(&mut proof, &conjunction)?;
            let surjective_beta =
                proof.conversion_beta(source.surjective_function, source.successor)?;
            if surjective_beta.left() != source.surjective
                || surjective_beta.right() != source.universal
            {
                return Err(super::DerivedRuleError::UnexpectedConclusion {
                    expected: source.universal,
                    actual: surjective_beta.right(),
                });
            }
            let surjective_equality = proof.prove_conversion_equality(context, &surjective_beta)?;
            let left_beta = proof.conversion_beta(source.q_transport, source.surjective)?;
            let left_beta = proof.conversion_symmetry(&left_beta)?;
            let transported_premise = proof.convert_theorem(&nonsurjective, &left_beta)?;
            let transported = proof.equality_substitution(
                &surjective_equality,
                source.q_transport,
                &transported_premise,
            )?;
            let right_beta = proof.conversion_beta(source.q_transport, source.universal)?;
            let normalized = proof.convert_theorem(&transported, &right_beta)?;
            let result = plan.missing_zero.apply(&mut proof, &normalized)?;
            proof.persist_theorem(&result)?;
            Ok(true)
        })
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-derived", error))?;
    if !persisted {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-derived",
            "exact inherited infinity theorem is absent",
        ));
    }
    Ok(())
}

/// Signed exact theorem that the epsilon-selected point satisfies `missing`.
pub struct SignedNatLikeMissingZero {
    artifact: SignedHolArtifact,
    context: ContextId,
    inherited_infinity: TermId,
    conclusion: TermId,
}

impl SignedNatLikeMissingZero {
    /// Returns the exact signed image.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the empty theorem context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the transitive Dedekind-infinity source assumption.
    #[must_use]
    pub const fn inherited_infinity(&self) -> TermId {
        self.inherited_infinity
    }

    /// Returns exact `missing zero`.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Returns the pinned structural theorem oracle.
    #[must_use]
    pub const fn theorem_oracle(&self) -> &'static str {
        MISSING_ZERO_ORACLE
    }

    /// Returns the authority-safe presentation label.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-natlike-missing-zero"
    }

    /// Renders an authority-safe sidecar for the exact signed state.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\nfalsehood=all-bool-identity\ntheorem=natlike-missing-zero\ntheorem-oracle={MISSING_ZERO_ORACLE}\nintermediate-persistence=none\nsignature-scope=exact-database-bytes\nsignature-meaning=authentication-not-proof\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn export_namespace(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    conclusion: TermId,
) -> Result<NamespaceId, SignedHolRoundTripError> {
    let namespace = connection
        .create_namespace(None, Some("natlike-missing-zero-v1"))
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-exported", error))?;
    for (slot, value, name) in [
        (0, NamespaceExport::Context(context), "empty-context"),
        (1, NamespaceExport::Term(conclusion), "missing-zero"),
    ] {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("missing-zero-exported", error))?;
    }
    Ok(namespace)
}

fn verify_no_primitive_false(
    connection: &sqlite::Connection,
) -> Result<(), SignedHolRoundTripError> {
    let rows = connection
        .query_row(
            "SELECT count(*) FROM hol_node WHERE tag = 'MBOOL' AND lhs = 0",
            [],
            |row| row.get::<_, i64>(0),
        )
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
    if rows != 0 {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-profile-checked",
            "complete derived image contains primitive Boolean false",
        ));
    }
    Ok(())
}

fn verify_raw_profile(
    raw: &covalence_neutron::Connection,
    namespace: NamespaceId,
    context: ContextId,
    infinity: TermId,
    conclusion: TermId,
) -> Result<(), SignedHolRoundTripError> {
    let connection = raw.sqlite();
    verify_no_primitive_false(connection)?;
    let profile = connection
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
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
    if profile != ("natlike-missing-zero-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-profile-checked",
            "derived namespace differs from the exact local profile",
        ));
    }
    let mut exports = connection
        .prepare(
            "SELECT export_id, sort, local_id, name FROM hol_namespace_export
             WHERE namespace_id = ?1 ORDER BY export_id",
        )
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
    let actual_exports = exports
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
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
            "missing-zero".to_owned(),
        ),
    ];
    if actual_exports != expected_exports {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-profile-checked",
            "derived exports differ from the exact slot/sort/name/value profile",
        ));
    }
    let mut judgements = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
    let actual_judgements = judgements
        .query_map([], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-profile-checked", error))?;
    let mut expected_judgements = vec![
        (context.get(), infinity.get()),
        (context.get(), conclusion.get()),
    ];
    expected_judgements.sort_unstable();
    if actual_judgements != expected_judgements {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-profile-checked",
            "state must contain exactly inherited infinity and final missing-zero",
        ));
    }
    Ok(())
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 1956,
        contexts: 50,
        members: 125,
        untrusted_judgement_rows: 2,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 4,
        namespace_exports: 16,
        import_references: 2,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 2,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::at(
            "missing-zero-image-validated",
            format_args!(
                "derived image differs from the frozen complete-state profile: {:?}",
                validated.counts()
            ),
        ));
    }
    Ok(())
}

/// Derives and signs exact `missing zero`, persisting no new intermediate theorem.
///
/// # Errors
///
/// Returns the first source, proof, persistence, export, validation, or signing error.
pub fn produce_signed_natlike_missing_zero(
    producer: &Kernel,
) -> Result<SignedNatLikeMissingZero, SignedHolRoundTripError> {
    let source_artifact = produce_signed_natlike_artifact(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-staging-opened", error))?;
    let (owner, retained) =
        retain_signed_natlike_artifact(producer, &mut staging, &source_artifact)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, owner, &retained, AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("missing-zero-source-opened", error))?;
    let source_namespace = NamespaceId::from_i64(source_artifact.artifact().namespace_id());
    let source = resolve_source(
        &mut connection,
        source_namespace,
        source_artifact.context(),
        source_artifact.infinity(),
    )?;
    let plan = prepare_plan(&mut connection, source)?;
    let conclusion = plan.missing_zero.conclusion();
    derive(
        &mut connection,
        source_artifact.context(),
        source_artifact.infinity(),
        source,
        &plan,
    )?;
    let namespace = export_namespace(&mut connection, source_artifact.context(), conclusion)?;
    let snapshot = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-signed", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(snapshot.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("missing-zero-image-copied", error))?;
    verify_raw_profile(
        &raw,
        namespace,
        source_artifact.context(),
        source_artifact.infinity(),
        conclusion,
    )?;
    let validated = ValidatedHolImage::validate(snapshot.image().bytes())
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let attestation = snapshot.attestation();
    Ok(SignedNatLikeMissingZero {
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image: validated.bytes().to_vec(),
            schema: attestation.schema(),
            image_hash: attestation.image(),
            signer: attestation.signer(),
            public_key: attestation.public_key().to_vec(),
            signature: attestation.signature().to_vec(),
        },
        context: source_artifact.context(),
        inherited_infinity: source_artifact.infinity(),
        conclusion,
    })
}

/// Produces and retains the signed missing-zero derivation in a fresh receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_natlike_missing_zero(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<
    (
        SignedNatLikeMissingZero,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    let artifact = produce_signed_natlike_missing_zero(producer)?;
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-signer-selected", error))?;
    let independent = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("missing-zero-signer-selected", error))?;
    if expected != independent {
        return Err(SignedHolRoundTripError::invalid(
            "missing-zero-signer-selected",
            "REPL local endpoint key differs from the missing-zero signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("missing-zero-receiver-opened", error))?;
    let (owner, retained) = trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        i64::MAX,
    )?;
    Ok((artifact, owner, retained))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;
    use covalence_nucleus::ProofError;

    #[test]
    fn derives_signs_receives_and_reopens_exact_missing_zero() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_natlike_missing_zero(&kernel, &mut directory).unwrap();
        assert_eq!(artifact.kind(), "signed-natlike-missing-zero");
        assert_eq!(artifact.theorem_oracle(), "(APP missing zero)");
        assert!(artifact.attestation_text().starts_with(
            "authority=kernel-derived-theorem\nsource-assumption=dedekind-infinity\n\
             falsehood=all-bool-identity\ntheorem=natlike-missing-zero\n"
        ));
        assert!(
            artifact
                .attestation_text()
                .contains("intermediate-persistence=none")
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
        let child = directory
            .get_mut(opened.connection())
            .unwrap()
            .hol_mut()
            .unwrap();
        let TermView::Application { function, argument } =
            child.term(artifact.conclusion()).unwrap()
        else {
            panic!("derived theorem must be exact missing zero application")
        };
        let TermView::Epsilon { predicate } = child.term(argument).unwrap() else {
            panic!("zero must be epsilon-selected from missing")
        };
        assert_eq!(predicate, function);
        let (infinity_loaded, final_loaded) = child
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
        assert!(infinity_loaded);
        assert!(final_loaded);
        let raw = covalence_neutron::Connection::deserialize(
            &covalence_neutron::Bytes::copy_from_slice(artifact.artifact().image()),
        )
        .unwrap();
        assert_eq!(
            raw.sqlite()
                .query_row(
                    "SELECT count(*) FROM hol_node WHERE tag = 'MBOOL' AND lhs = 0",
                    [],
                    |row| row.get::<_, i64>(0),
                )
                .unwrap(),
            0
        );
    }

    #[test]
    fn complete_profile_rejects_unreachable_primitive_false() {
        let kernel = Kernel::ephemeral();
        let artifact = produce_signed_natlike_missing_zero(&kernel).unwrap();
        let raw = covalence_neutron::Connection::deserialize(
            &covalence_neutron::Bytes::copy_from_slice(artifact.artifact().image()),
        )
        .unwrap();
        raw.sqlite()
            .execute(
                "INSERT INTO hol_node(tag, lhs, ty)
                 SELECT 'MBOOL', 0, node_id FROM hol_node WHERE tag = 'TBOOL'",
                [],
            )
            .unwrap();
        let error = verify_no_primitive_false(raw.sqlite()).unwrap_err();
        assert!(error.to_string().contains("primitive Boolean false"));
    }
}
