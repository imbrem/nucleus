use super::{
    AllowAll, Connection, ConnectionId, ContextId, ExpectedKernelIdentity, Hol, KernelId,
    LocalConnection, Repl, RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact, prepare_retained_trusted_hol_state,
    produce_signed_natlike_successor, retain_signed_natlike_successor,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, NamespaceId, Signer as _, TermId, TermView,
    TypeId, ValidatedHolImage, schema_valid_snapshot_statement,
};

const FALSE_BRIDGE_ORACLE: &str = "(EQ false (EQ (LAM:B #0:B) (LAM:B true)))";

/// Exact checked syntax for the explicit primitive-to-derived false bridge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FalseBridgeSyntax {
    bool_type: TypeId,
    primitive_false: TermId,
    canonical_false: TermId,
    conclusion: TermId,
}

impl FalseBridgeSyntax {
    /// Returns the Boolean type used by both sides.
    #[must_use]
    pub const fn bool_type(self) -> TypeId {
        self.bool_type
    }

    /// Returns the primitive `MBOOL(false)` term.
    #[must_use]
    pub const fn primitive_false(self) -> TermId {
        self.primitive_false
    }

    /// Returns `ALL_B (lambda p. p)` in the equality-based universal encoding.
    #[must_use]
    pub const fn canonical_false(self) -> TermId {
        self.canonical_false
    }

    /// Returns `MBOOL(false) = ALL_B (lambda p. p)`.
    #[must_use]
    pub const fn conclusion(self) -> TermId {
        self.conclusion
    }
}

fn render_false_bridge(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
    bool_type: TypeId,
) -> Result<String, SignedHolRoundTripError> {
    let stage = "false-bridge-exact-oracle";
    match connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
    {
        TermView::Bool(value) => Ok(value.to_string()),
        TermView::Bound { index } => {
            if connection
                .term_type(term)
                .map_err(|error| SignedHolRoundTripError::at(stage, error))?
                != bool_type
            {
                return Err(SignedHolRoundTripError::invalid(
                    stage,
                    "false bridge contains a non-Boolean bound term",
                ));
            }
            Ok(format!("#{index}:B"))
        }
        TermView::Lambda {
            parameter_type,
            body,
        } if parameter_type == bool_type => Ok(format!(
            "(LAM:B {})",
            render_false_bridge(connection, body, bool_type)?
        )),
        TermView::Equality { left, right } => Ok(format!(
            "(EQ {} {})",
            render_false_bridge(connection, left, bool_type)?,
            render_false_bridge(connection, right, bool_type)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            stage,
            "false bridge contains a term outside its pinned fragment",
        )),
    }
}

/// Builds the bridge syntax through checked HOL constructors without adding authority.
///
/// `ALL_B P` is represented as `P = (lambda _. true)`. Consequently the
/// canonical false proposition is `(lambda p. p) = (lambda _. true)`.
///
/// # Errors
///
/// Returns if a checked constructor, type check, closure check, or exact graph
/// oracle rejects the term.
pub fn build_false_bridge_syntax(
    connection: &mut Connection<Hol<AllowAll>>,
) -> Result<FalseBridgeSyntax, SignedHolRoundTripError> {
    let stage = "false-bridge-syntax-checked";
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let truth = connection
        .insert_bool_term(true)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let primitive_false = connection
        .insert_bool_term(false)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let bound = connection
        .insert_bound_term(0, bool_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let identity = connection
        .insert_lambda(bool_type, bound)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let constant_truth = connection
        .insert_lambda(bool_type, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let canonical_false = connection
        .insert_equality(identity, constant_truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let conclusion = connection
        .insert_equality(primitive_false, canonical_false)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    for term in [primitive_false, canonical_false, conclusion] {
        if connection
            .term_type(term)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?
            != bool_type
            || !connection
                .term_is_locally_closed(term)
                .map_err(|error| SignedHolRoundTripError::at(stage, error))?
        {
            return Err(SignedHolRoundTripError::invalid(
                stage,
                "false bridge is not a closed Boolean proposition",
            ));
        }
    }
    if render_false_bridge(connection, conclusion, bool_type)? != FALSE_BRIDGE_ORACLE {
        return Err(SignedHolRoundTripError::invalid(
            "false-bridge-exact-oracle",
            "false bridge differs from the pinned structural literal",
        ));
    }
    Ok(FalseBridgeSyntax {
        bool_type,
        primitive_false,
        canonical_false,
        conclusion,
    })
}

/// One explicit signed assumption extending the inherited `NatLike` state.
///
/// The only new judgement is the bridge from primitive false to the canonical
/// equality-based false proposition. The signature authenticates exact bytes;
/// it does not prove the admitted row.
pub struct SignedFalseBridge {
    artifact: SignedHolArtifact,
    natlike_namespace: NamespaceId,
    context: ContextId,
    inherited: [TermId; 4],
    syntax: FalseBridgeSyntax,
}

impl SignedFalseBridge {
    /// Returns the exact signed database artifact.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the inherited predicate-NatLike syntax namespace.
    #[must_use]
    pub const fn natlike_namespace(&self) -> NamespaceId {
        self.natlike_namespace
    }

    /// Returns the empty theorem context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the inherited infinity assumption.
    #[must_use]
    pub const fn inherited_infinity(&self) -> TermId {
        self.inherited[0]
    }

    /// Returns the inherited non-surjectivity theorem.
    #[must_use]
    pub const fn inherited_nonsurjective(&self) -> TermId {
        self.inherited[1]
    }

    /// Returns the inherited `NatLike zero` theorem.
    #[must_use]
    pub const fn inherited_zero(&self) -> TermId {
        self.inherited[2]
    }

    /// Returns the inherited universal successor-closure theorem.
    #[must_use]
    pub const fn inherited_successor_closure(&self) -> TermId {
        self.inherited[3]
    }

    /// Returns the checked primitive/canonical false syntax.
    #[must_use]
    pub const fn syntax(&self) -> FalseBridgeSyntax {
        self.syntax
    }

    /// Returns the explicitly admitted equality.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.syntax.conclusion()
    }

    /// Returns an authority-safe artifact classification.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-assumption"
    }

    /// Renders an explicit assumption sidecar for the exact signed state.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=signed-assumption\nassumption=primitive-false-equals-canonical-false\ncanonical-false=all-bool-identity\ninherited-theorems-used=none\nsignature-scope=exact-database-bytes\nsignature-meaning=authentication-not-proof\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn export_namespace(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    syntax: FalseBridgeSyntax,
) -> Result<NamespaceId, SignedHolRoundTripError> {
    let stage = "false-bridge-exported";
    let namespace = connection
        .create_namespace(None, Some("primitive-false-bridge-v1"))
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    for (slot, value, name) in [
        (0, NamespaceExport::Context(context), "empty-context"),
        (
            1,
            NamespaceExport::Term(syntax.conclusion()),
            "primitive-false-equals-canonical-false",
        ),
        (
            2,
            NamespaceExport::Term(syntax.primitive_false()),
            "primitive-false",
        ),
        (
            3,
            NamespaceExport::Term(syntax.canonical_false()),
            "canonical-false",
        ),
        (4, NamespaceExport::Type(syntax.bool_type()), "bool"),
    ] {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    }
    Ok(namespace)
}

fn verify_judgements(
    connection: &sqlite::Connection,
    context: ContextId,
    inherited: [TermId; 4],
    assumption: Option<TermId>,
) -> Result<(), SignedHolRoundTripError> {
    let stage = "false-bridge-profile-checked";
    let mut statement = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let actual = statement
        .query_map([], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let mut expected = inherited
        .into_iter()
        .chain(assumption)
        .map(|term| (context.get(), term.get()))
        .collect::<Vec<_>>();
    expected.sort_unstable();
    if actual != expected {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "judgements differ from the four inherited rows and optional bridge assumption",
        ));
    }
    Ok(())
}

fn verify_raw_profile(
    raw: &covalence_neutron::Connection,
    namespace: NamespaceId,
    context: ContextId,
    inherited: [TermId; 4],
    syntax: FalseBridgeSyntax,
    inserted: bool,
) -> Result<(), SignedHolRoundTripError> {
    let stage = "false-bridge-profile-checked";
    let connection = raw.sqlite();
    let namespace_row = connection
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
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    if namespace_row != ("primitive-false-bridge-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "bridge namespace differs from the exact local profile",
        ));
    }
    let mut exports = connection
        .prepare("SELECT export_id, sort, local_id, name FROM hol_namespace_export WHERE namespace_id = ?1 ORDER BY export_id")
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let actual = exports
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let expected = vec![
        (
            0,
            "context".to_owned(),
            context.get(),
            "empty-context".to_owned(),
        ),
        (
            1,
            "term".to_owned(),
            syntax.conclusion().get(),
            "primitive-false-equals-canonical-false".to_owned(),
        ),
        (
            2,
            "term".to_owned(),
            syntax.primitive_false().get(),
            "primitive-false".to_owned(),
        ),
        (
            3,
            "term".to_owned(),
            syntax.canonical_false().get(),
            "canonical-false".to_owned(),
        ),
        (
            4,
            "type".to_owned(),
            syntax.bool_type().get(),
            "bool".to_owned(),
        ),
    ];
    if actual != expected {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "bridge exports differ from the exact slot/sort/name/value profile",
        ));
    }
    verify_judgements(
        connection,
        context,
        inherited,
        inserted.then_some(syntax.conclusion()),
    )
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 604,
        contexts: 7,
        members: 8,
        untrusted_judgement_rows: 5,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 7,
        namespace_exports: 28,
        import_references: 5,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 5,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::at(
            "false-bridge-image-validated",
            format_args!(
                "complete-state profile differs: actual {:?}, expected {:?}",
                validated.counts(),
                expected
            ),
        ));
    }
    Ok(())
}

/// Extends the signed successor-closure state with exactly one explicit false bridge assumption.
///
/// Checked APIs build and export all syntax. A disposable raw copy inserts the
/// sole new judgement; detached validation precedes the schema-qualified
/// signature. No proof rule admits the row.
///
/// # Errors
///
/// Returns the first source, checked syntax, profile, insertion, validation, or
/// signing error.
pub fn produce_signed_false_bridge(
    producer: &Kernel,
) -> Result<SignedFalseBridge, SignedHolRoundTripError> {
    let source = produce_signed_natlike_successor(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-staging-opened", error))?;
    let (owner, retained) = retain_signed_natlike_successor(producer, &mut staging, &source)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, owner, &retained, AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("false-bridge-source-opened", error))?;
    let context = source.context();
    let inherited = [
        source.inherited_infinity(),
        source.inherited_nonsurjective(),
        source.inherited_zero(),
        source.conclusion(),
    ];
    connection.with_proof_session(|mut proof| {
        for conclusion in inherited {
            if proof
                .load_theorem(context, conclusion)
                .map_err(|error| SignedHolRoundTripError::at("false-bridge-source-loaded", error))?
                .is_none()
            {
                return Err(SignedHolRoundTripError::invalid(
                    "false-bridge-source-loaded",
                    "an exact inherited judgement is absent",
                ));
            }
        }
        Ok(())
    })?;
    let syntax = build_false_bridge_syntax(&mut connection)?;
    let namespace = export_namespace(&mut connection, context, syntax)?;

    // The checked export is used only to serialize the syntax extension. Its
    // preliminary signature is discarded and conveys no new authority.
    let checked = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-syntax-serialized", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(checked.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("false-bridge-image-copied", error))?;
    verify_raw_profile(&raw, namespace, context, inherited, syntax, false)?;
    let inserted = raw
        .sqlite()
        .execute(
            "INSERT INTO hol_judgement(ctx_id, term_id) VALUES (?1, ?2)",
            [context.get(), syntax.conclusion().get()],
        )
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-assumption-inserted", error))?;
    if inserted != 1 {
        return Err(SignedHolRoundTripError::invalid(
            "false-bridge-assumption-inserted",
            "bridge insertion did not add exactly one judgement",
        ));
    }
    verify_raw_profile(&raw, namespace, context, inherited, syntax, true)?;
    let bytes = raw
        .serialize()
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-image-serialized", error))?;
    let validated = ValidatedHolImage::validate(&bytes)
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-image-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let schema = validated.schema();
    let image_hash = validated.hash();
    let signer = producer.key_id();
    let signature = producer
        .signer()
        .sign(signer, schema_valid_snapshot_statement(schema, image_hash))
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-signed", error))?;
    Ok(SignedFalseBridge {
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image: validated.bytes().to_vec(),
            schema,
            image_hash,
            signer,
            public_key: producer.verifying_key().as_bytes().to_vec(),
            signature: signature.to_vec(),
        },
        natlike_namespace: source.natlike_namespace(),
        context,
        inherited,
        syntax,
    })
}

/// Authenticates and retains one already-produced signed false bridge.
///
/// # Errors
///
/// Returns the first authentication, trust, import, receiver, or directory error.
pub fn retain_signed_false_bridge(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: &SignedFalseBridge,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-signer-selected", error))?;
    let independent = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("false-bridge-signer-selected", error))?;
    if expected != independent {
        return Err(SignedHolRoundTripError::invalid(
            "false-bridge-signer-selected",
            "REPL local endpoint key differs from the false-bridge signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("false-bridge-receiver-opened", error))?;
    trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        i64::MAX,
    )
}

/// Produces and retains the signed false bridge in a fresh receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_false_bridge(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<(SignedFalseBridge, ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError>
{
    let artifact = produce_signed_false_bridge(producer)?;
    let (owner, retained) = retain_signed_false_bridge(producer, directory, &artifact)?;
    Ok((artifact, owner, retained))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;

    #[test]
    fn builds_the_exact_closed_typed_bridge_without_authority() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let syntax = build_false_bridge_syntax(&mut connection).unwrap();
        assert_eq!(
            render_false_bridge(&mut connection, syntax.conclusion(), syntax.bool_type()).unwrap(),
            FALSE_BRIDGE_ORACLE
        );
        assert!(
            !connection
                .proved_judgement(ContextId::empty(), syntax.conclusion())
                .unwrap()
        );
    }

    #[test]
    fn signs_receives_reopens_and_reloads_exact_assumption_state() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_false_bridge(&kernel, &mut directory).unwrap();
        assert_eq!(artifact.kind(), "signed-assumption");
        assert!(artifact.attestation_text().starts_with(
            "authority=signed-assumption\nassumption=primitive-false-equals-canonical-false\n"
        ));
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
        for conclusion in artifact
            .inherited
            .into_iter()
            .chain([artifact.conclusion()])
        {
            assert!(
                child
                    .with_proof_session(|mut proof| proof
                        .load_theorem(artifact.context(), conclusion)
                        .map(|theorem| theorem.is_some()))
                    .unwrap()
            );
        }
        let validated = ValidatedHolImage::validate(artifact.artifact().image()).unwrap();
        assert_eq!(validated.counts().untrusted_judgement_rows, 5);
    }

    #[test]
    fn receive_rejects_tamper_and_wrong_signer_without_directory_mutation() {
        let producer = Kernel::ephemeral();
        let mut artifact = produce_signed_false_bridge(&producer).unwrap();
        artifact.artifact.image[0] ^= 1;
        let mut directory = Repl::new(producer.verifying_key().as_bytes()).unwrap();
        assert!(retain_signed_false_bridge(&producer, &mut directory, &artifact).is_err());
        assert!(directory.connections().unwrap().is_empty());
        assert_eq!(directory.active().unwrap(), None);

        let artifact = produce_signed_false_bridge(&producer).unwrap();
        let other = Kernel::ephemeral();
        let mut wrong_directory = Repl::new(other.verifying_key().as_bytes()).unwrap();
        assert!(retain_signed_false_bridge(&producer, &mut wrong_directory, &artifact).is_err());
        assert!(wrong_directory.connections().unwrap().is_empty());
        assert_eq!(wrong_directory.active().unwrap(), None);
    }
}
