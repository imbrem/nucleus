use super::{
    AllowAll, Connection, ConnectionId, ContextId, ExpectedKernelIdentity, Hol, KernelId,
    LocalConnection, Repl, RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, Signer as _, TermError, TermId, TermView,
    TypeId, ValidatedHolImage, schema_valid_snapshot_statement,
};

const IND_TYPE_SYMBOL: i64 = 100;
const DEDEKIND_INFINITY_GRAPH: &str = r"(APP (LAM:(I->I) (APP (APP (LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true))))) (APP (LAM:(I->I) (EQ (LAM:I (EQ (LAM:I (EQ (APP (APP (LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true))))) (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I))) (EQ #1:I #0:I)) (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I)))) (LAM:I true))) (LAM:I true))) #0:(I->I))) (EQ (APP (LAM:(I->I) (EQ (LAM:I (APP (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I)) (EPS (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I))))) (LAM:I true))) #0:(I->I)) false))) (EPS (LAM:(I->I) (APP (APP (LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true))))) (APP (LAM:(I->I) (EQ (LAM:I (EQ (LAM:I (EQ (APP (APP (LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true))))) (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I))) (EQ #1:I #0:I)) (EQ (APP #2:(I->I) #1:I) (APP #2:(I->I) #0:I)))) (LAM:I true))) (LAM:I true))) #0:(I->I))) (EQ (APP (LAM:(I->I) (EQ (LAM:I (APP (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I)) (EPS (LAM:I (EQ (APP #2:(I->I) #0:I) #1:I))))) (LAM:I true))) #0:(I->I)) false)))))";

/// Checked syntax coordinate for the fully expanded Dedekind-infinity assumption.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DedekindInfinitySyntax {
    conclusion: TermId,
    ind: TypeId,
    property: TermId,
    witness: TermId,
}

impl DedekindInfinitySyntax {
    /// Returns the closed Boolean proposition.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Returns the opaque base type conventionally named `ind` by this fixture.
    #[must_use]
    pub const fn ind_type(&self) -> TypeId {
        self.ind
    }

    /// Returns the closed predicate selecting injective non-surjective endomaps.
    #[must_use]
    pub const fn property(&self) -> TermId {
        self.property
    }

    /// Returns `MEPS(property)`, the exact witness used by the conclusion.
    #[must_use]
    pub const fn witness(&self) -> TermId {
        self.witness
    }
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

fn logical_not(
    connection: &mut Connection<Hol<AllowAll>>,
    proposition: TermId,
    falsehood: TermId,
) -> Result<TermId, TermError> {
    connection.insert_equality(proposition, falsehood)
}

fn logical_all(
    connection: &mut Connection<Hol<AllowAll>>,
    parameter_type: TypeId,
    predicate: TermId,
    truth: TermId,
) -> Result<TermId, TermError> {
    let constant_truth = connection.insert_lambda(parameter_type, truth)?;
    connection.insert_equality(predicate, constant_truth)
}

fn logical_exists(
    connection: &mut Connection<Hol<AllowAll>>,
    predicate: TermId,
) -> Result<TermId, TermError> {
    let witness = connection.insert_epsilon(predicate)?;
    connection.insert_application(predicate, witness)
}

#[derive(Clone, Copy)]
struct FixtureBasis {
    bool_type: TypeId,
    ind: TypeId,
    endomap: TypeId,
    truth: TermId,
    falsehood: TermId,
    conjunction: TermId,
}

fn build_fixture_basis(
    connection: &mut Connection<Hol<AllowAll>>,
) -> Result<FixtureBasis, SignedHolRoundTripError> {
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let ind = connection
        .insert_base_type(IND_TYPE_SYMBOL)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let bool_to_bool = connection
        .insert_arrow_type(bool_type, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let bool_binary = connection
        .insert_arrow_type(bool_type, bool_to_bool)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let endomap = connection
        .insert_arrow_type(ind, ind)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let truth = connection
        .insert_bool_term(true)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let falsehood = connection
        .insert_bool_term(false)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let choice = connection
        .insert_bound_term(0, bool_binary)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let left = connection
        .insert_bound_term(2, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let right = connection
        .insert_bound_term(1, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let select_arguments = apply2(connection, choice, left, right)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let select_truth = apply2(connection, choice, truth, truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let select_arguments = connection
        .insert_lambda(bool_binary, select_arguments)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let select_truth = connection
        .insert_lambda(bool_binary, select_truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let body = connection
        .insert_equality(select_arguments, select_truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let body = connection
        .insert_lambda(bool_type, body)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let conjunction = connection
        .insert_lambda(bool_type, body)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    Ok(FixtureBasis {
        bool_type,
        ind,
        endomap,
        truth,
        falsehood,
        conjunction,
    })
}

fn build_injective(
    connection: &mut Connection<Hol<AllowAll>>,
    basis: FixtureBasis,
) -> Result<TermId, SignedHolRoundTripError> {
    let function = connection
        .insert_bound_term(2, basis.endomap)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let left = connection
        .insert_bound_term(1, basis.ind)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let right = connection
        .insert_bound_term(0, basis.ind)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let left_image = connection
        .insert_application(function, left)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let right_image = connection
        .insert_application(function, right)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let antecedent = connection
        .insert_equality(left_image, right_image)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let consequent = connection
        .insert_equality(left, right)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let both = apply2(connection, basis.conjunction, antecedent, consequent)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let implication = connection
        .insert_equality(both, antecedent)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let right_predicate = connection
        .insert_lambda(basis.ind, implication)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let all_right = logical_all(connection, basis.ind, right_predicate, basis.truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let left_predicate = connection
        .insert_lambda(basis.ind, all_right)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let all_left = logical_all(connection, basis.ind, left_predicate, basis.truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    connection
        .insert_lambda(basis.endomap, all_left)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))
}

fn build_surjective(
    connection: &mut Connection<Hol<AllowAll>>,
    basis: FixtureBasis,
) -> Result<TermId, SignedHolRoundTripError> {
    let function = connection
        .insert_bound_term(2, basis.endomap)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let argument = connection
        .insert_bound_term(0, basis.ind)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let target = connection
        .insert_bound_term(1, basis.ind)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let image = connection
        .insert_application(function, argument)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let hits_target = connection
        .insert_equality(image, target)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let argument_predicate = connection
        .insert_lambda(basis.ind, hits_target)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let exists_argument = logical_exists(connection, argument_predicate)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let target_predicate = connection
        .insert_lambda(basis.ind, exists_argument)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let all_targets = logical_all(connection, basis.ind, target_predicate, basis.truth)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    connection
        .insert_lambda(basis.endomap, all_targets)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))
}

/// Builds the closed, monomorphic Dedekind-infinity proposition using only checked syntax APIs.
///
/// The expansion fixes `EX(P) = P (MEPS P)`, equality-based `ALL`, `NOT`, `AND`, and `IMP`,
/// then states that an injective, non-surjective endomap on `ind` exists. It introduces no
/// judgement or theorem authority.
///
/// # Errors
///
/// Returns if any checked type or term constructor rejects the exact graph.
pub fn build_dedekind_infinity_syntax(
    connection: &mut Connection<Hol<AllowAll>>,
) -> Result<DedekindInfinitySyntax, SignedHolRoundTripError> {
    let basis = build_fixture_basis(connection)?;
    let injective = build_injective(connection, basis)?;
    let surjective = build_surjective(connection, basis)?;
    let FixtureBasis {
        bool_type,
        ind,
        endomap,
        falsehood,
        conjunction: and,
        ..
    } = basis;

    // PROPERTY = λf. AND (INJ f) (NOT (SURJ f)); root = EX PROPERTY.
    let f = connection
        .insert_bound_term(0, endomap)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let is_injective = connection
        .insert_application(injective, f)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let is_surjective = connection
        .insert_application(surjective, f)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let not_surjective = logical_not(connection, is_surjective, falsehood)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let property_body = apply2(connection, and, is_injective, not_surjective)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let property = connection
        .insert_lambda(endomap, property_body)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let witness = connection
        .insert_epsilon(property)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;
    let conclusion = connection
        .insert_application(property, witness)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?;

    if connection
        .term_type(conclusion)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?
        != bool_type
        || !connection
            .term_is_locally_closed(conclusion)
            .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?
    {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-syntax-checked",
            "Dedekind-infinity root is not a closed Boolean term",
        ));
    }
    let TermView::Application { function, argument } = connection
        .term(conclusion)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-syntax-checked",
            "Dedekind-infinity root is not an application",
        ));
    };
    let TermView::Epsilon { predicate } = connection
        .term(argument)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-checked", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-syntax-checked",
            "Dedekind-infinity witness is not epsilon",
        ));
    };
    if function != property || predicate != property {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-syntax-checked",
            "EX must reuse the exact PROPERTY term as function and epsilon predicate",
        ));
    }
    if render_term(connection, conclusion)? != DEDEKIND_INFINITY_GRAPH {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "Dedekind-infinity graph differs from the pinned exact profile",
        ));
    }

    Ok(DedekindInfinitySyntax {
        conclusion,
        ind,
        property,
        witness,
    })
}

/// One explicitly signed assumption-set database containing Dedekind infinity.
///
/// The signature authenticates exact structurally valid bytes. It is not a
/// proof of the stored judgement. Receiving records accepted signer/import
/// evidence and returns inert integer coordinates, but mints no branded
/// theorem. `OpenTrustedSnapshotAsState` is the separate explicit logical
/// origin assumption; only a scoped child `load_theorem` then mints authority.
pub struct SignedInfinityAssumption {
    artifact: SignedHolArtifact,
    context: ContextId,
    conclusion: TermId,
}

impl SignedInfinityAssumption {
    /// Returns `signed-assumption`, never a proof-oriented label.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-assumption"
    }

    /// Returns the exact signed database artifact.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the empty assumption context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the checked Dedekind-infinity proposition admitted as an assumption.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }

    /// Separates the transport artifact from inert source coordinates.
    #[must_use]
    pub fn into_parts(self) -> (SignedHolArtifact, ContextId, TermId) {
        (self.artifact, self.context, self.conclusion)
    }

    /// Renders the demo-local sidecar with an explicit authority classification.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=signed-assumption\nassumption=dedekind-infinity\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn verify_namespace_profile(
    connection: &sqlite::Connection,
    namespace: covalence_nucleus::NamespaceId,
    syntax: DedekindInfinitySyntax,
) -> Result<(), SignedHolRoundTripError> {
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
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?;
    if namespace_row != ("dedekind-infinity-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "fixture namespace differs from the exact local profile",
        ));
    }
    let mut statement = connection
        .prepare(
            "SELECT export_id, sort, local_id, name
             FROM hol_namespace_export WHERE namespace_id = ?1 ORDER BY export_id",
        )
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?;
    let exports = statement
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?;
    let expected = vec![
        (
            0,
            "context".to_owned(),
            0,
            "empty-assumption-context".to_owned(),
        ),
        (
            1,
            "term".to_owned(),
            syntax.conclusion().get(),
            "dedekind-infinity-assumption".to_owned(),
        ),
        (
            2,
            "type".to_owned(),
            syntax.ind_type().get(),
            "ind".to_owned(),
        ),
        (
            3,
            "term".to_owned(),
            syntax.property().get(),
            "dedekind-endomap-property".to_owned(),
        ),
        (
            4,
            "term".to_owned(),
            syntax.witness().get(),
            "dedekind-endomap".to_owned(),
        ),
    ];
    if exports != expected {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "fixture namespace exports differ from the exact named profile",
        ));
    }
    Ok(())
}

fn verify_raw_assumption_profile(
    raw: &covalence_neutron::Connection,
    namespace: covalence_nucleus::NamespaceId,
    syntax: DedekindInfinitySyntax,
) -> Result<(), SignedHolRoundTripError> {
    let connection = raw.sqlite();
    let authority_rows = connection
        .query_row(
            "SELECT
                 (SELECT count(*) FROM hol_judgement) +
                 (SELECT count(*) FROM hol_import) +
                 (SELECT count(*) FROM hol_trusted_import) +
                 (SELECT count(*) FROM hol_context_member) +
                 (SELECT count(*) FROM hol_context_implication) +
                 (SELECT count(*) FROM hol_context_exact_union)",
            [],
            |row| row.get::<_, i64>(0),
        )
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?;
    if authority_rows != 0 {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "fixture has preexisting authority, context, import, implication, or union rows",
        ));
    }

    verify_namespace_profile(connection, namespace, syntax)?;

    let base_types = connection
        .query_row(
            "SELECT count(*), coalesce(min(lhs), -1) FROM hol_node WHERE tag = 'TBASE'",
            [],
            |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)),
        )
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?;
    if base_types != (1, IND_TYPE_SYMBOL) {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "fixture must contain exactly the single ind base declaration",
        ));
    }
    Ok(())
}

fn verify_validated_assumption_counts(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 55,
        contexts: 1,
        members: 0,
        untrusted_judgement_rows: 1,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 2,
        namespace_exports: 5,
        import_references: 0,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 0,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-image-detached-validated",
            "fixture database differs from the frozen complete-state profile",
        ));
    }
    Ok(())
}

fn export_assumption_namespace(
    checked: &mut Connection<Hol<AllowAll>>,
    syntax: DedekindInfinitySyntax,
) -> Result<covalence_nucleus::NamespaceId, SignedHolRoundTripError> {
    let namespace = checked
        .create_namespace(None, Some("dedekind-infinity-v1"))
        .map_err(|error| SignedHolRoundTripError::at("assumption-namespace-exported", error))?;
    let exports = [
        (
            0,
            NamespaceExport::Context(ContextId::empty()),
            "empty-assumption-context",
        ),
        (2, NamespaceExport::Type(syntax.ind_type()), "ind"),
        (
            3,
            NamespaceExport::Term(syntax.property()),
            "dedekind-endomap-property",
        ),
        (
            4,
            NamespaceExport::Term(syntax.witness()),
            "dedekind-endomap",
        ),
        (
            1,
            NamespaceExport::Term(syntax.conclusion()),
            "dedekind-infinity-assumption",
        ),
    ];
    for (slot, value, name) in exports {
        checked
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("assumption-namespace-exported", error))?;
    }
    Ok(namespace)
}

/// Constructs, independently validates, and signs the explicit infinity assumption fixture.
///
/// All syntax and namespace rows are first created through checked HOL APIs. A
/// disposable raw Neutron copy then inserts exactly one returned judgement,
/// `(empty, infinity)`. The resulting bytes are detached-validated before the
/// schema-qualified signature is created. No proof rule admits the row.
///
/// # Errors
///
/// Returns the named boundary which rejected syntax, namespace export, raw
/// assumption insertion, detached validation, or signing.
pub fn produce_signed_dedekind_infinity_assumption(
    producer: &Kernel,
) -> Result<SignedInfinityAssumption, SignedHolRoundTripError> {
    let mut checked = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("assumption-store-opened", error))?;
    let syntax = build_dedekind_infinity_syntax(&mut checked)?;
    let context = ContextId::empty();
    let namespace = export_assumption_namespace(&mut checked, syntax)?;

    // Export is used only to obtain an already validated serialization of the
    // checked syntax store. Its preliminary signature is neither retained nor
    // presented as authority.
    let checked_image = producer
        .export_hol(&mut checked)
        .map_err(|error| SignedHolRoundTripError::at("assumption-syntax-serialized", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(checked_image.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("assumption-store-copied", error))?;
    verify_raw_assumption_profile(&raw, namespace, syntax)?;
    let inserted = raw
        .sqlite()
        .execute(
            "INSERT INTO hol_judgement(ctx_id, term_id) VALUES (?1, ?2)",
            [context.get(), syntax.conclusion().get()],
        )
        .map_err(|error| SignedHolRoundTripError::at("assumption-row-inserted", error))?;
    let exact_row = raw
        .sqlite()
        .query_row(
            "SELECT count(*) FROM hol_judgement WHERE ctx_id = ?1 AND term_id = ?2",
            [context.get(), syntax.conclusion().get()],
            |row| row.get::<_, i64>(0),
        )
        .map_err(|error| SignedHolRoundTripError::at("assumption-row-inserted", error))?;
    let all_rows = raw
        .sqlite()
        .query_row("SELECT count(*) FROM hol_judgement", [], |row| {
            row.get::<_, i64>(0)
        })
        .map_err(|error| SignedHolRoundTripError::at("assumption-row-inserted", error))?;
    if inserted != 1 || exact_row != 1 || all_rows != 1 {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-row-inserted",
            "fixture must insert exactly one assumption judgement",
        ));
    }

    let bytes = raw
        .serialize()
        .map_err(|error| SignedHolRoundTripError::at("assumption-image-serialized", error))?;
    let validated = ValidatedHolImage::validate(&bytes).map_err(|error| {
        SignedHolRoundTripError::at("assumption-image-detached-validated", error)
    })?;
    verify_validated_assumption_counts(&validated)?;
    let schema = validated.schema();
    let image_hash = validated.hash();
    let signer = producer.key_id();
    let signature = producer
        .signer()
        .sign(signer, schema_valid_snapshot_statement(schema, image_hash))
        .map_err(|error| SignedHolRoundTripError::at("assumption-signed", error))?;
    let artifact = SignedHolArtifact {
        namespace_id: namespace.get(),
        image: validated.bytes().to_vec(),
        schema,
        image_hash,
        signer,
        public_key: producer.verifying_key().as_bytes().to_vec(),
        signature: signature.to_vec(),
    };
    Ok(SignedInfinityAssumption {
        artifact,
        context,
        conclusion: syntax.conclusion(),
    })
}

/// Produces the signed assumption and retains its explicitly trusted import receiver in a REPL.
///
/// This is the single transport-neutral trust/import action used by terminal
/// and browser frontends. Its returned receipt and integer coordinates are
/// inert presentation/runtime evidence, even though the receiver records the
/// accepted signer/import evidence. The existing trusted-state open action is
/// the separate logical-origin assumption.
///
/// # Errors
///
/// Returns the first producer, endpoint-pin, receiver, trust, import, or
/// directory boundary which rejects the fixture.
pub fn produce_and_retain_signed_dedekind_infinity_assumption(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<
    (
        SignedInfinityAssumption,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    produce_and_retain_signed_dedekind_infinity_assumption_bounded(producer, directory, i64::MAX)
}

pub(crate) fn produce_and_retain_signed_dedekind_infinity_assumption_bounded(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    maximum_connection_id: i64,
) -> Result<
    (
        SignedInfinityAssumption,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    let assumption = produce_signed_dedekind_infinity_assumption(producer)?;
    let (owner, retained) = retain_signed_dedekind_infinity_assumption_bounded(
        producer,
        directory,
        &assumption,
        maximum_connection_id,
    )?;
    Ok((assumption, owner, retained))
}

/// Authenticates and retains one already-produced signed infinity assumption.
///
/// This operation exposes no theorem authority. It records accepted
/// signer/import evidence in a fresh selected receiver; opening a scoped
/// trusted state remains a separate explicit logical-origin assumption.
///
/// # Errors
///
/// Returns the first endpoint-pin, authentication, receiver, trust, import, or
/// directory boundary which rejects the fixture.
pub fn retain_signed_dedekind_infinity_assumption(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    assumption: &SignedInfinityAssumption,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    retain_signed_dedekind_infinity_assumption_bounded(producer, directory, assumption, i64::MAX)
}

fn retain_signed_dedekind_infinity_assumption_bounded(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    assumption: &SignedInfinityAssumption,
    maximum_connection_id: i64,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("assumption-signer-selected", error))?;
    let independently_expected = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("assumption-signer-selected", error))?;
    if expected != independently_expected {
        return Err(SignedHolRoundTripError::invalid(
            "assumption-signer-selected",
            "REPL local endpoint key differs from the assumption signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, assumption.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("assumption-receiver-opened", error))?;
    let (owner, retained) = trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        maximum_connection_id,
    )?;
    Ok((owner, retained))
}

fn render_type(
    connection: &mut Connection<Hol<AllowAll>>,
    ty: TypeId,
) -> Result<String, SignedHolRoundTripError> {
    match connection
        .type_view(ty)
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?
    {
        covalence_nucleus::TypeView::Bool => Ok("B".to_owned()),
        covalence_nucleus::TypeView::Base { symbol } if symbol == IND_TYPE_SYMBOL => {
            Ok("I".to_owned())
        }
        covalence_nucleus::TypeView::Arrow { domain, codomain } => Ok(format!(
            "({}->{})",
            render_type(connection, domain)?,
            render_type(connection, codomain)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "formula contains a non-profile type constructor",
        )),
    }
}

fn render_term(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
) -> Result<String, SignedHolRoundTripError> {
    match connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at("assumption-profile-checked", error))?
    {
        TermView::Bool(true) => Ok("true".to_owned()),
        TermView::Bool(false) => Ok("false".to_owned()),
        TermView::Bound { index } => {
            let ty = connection.term_type(term).map_err(|error| {
                SignedHolRoundTripError::at("assumption-profile-checked", error)
            })?;
            Ok(format!("#{index}:{}", render_type(connection, ty)?))
        }
        TermView::Application { function, argument } => Ok(format!(
            "(APP {} {})",
            render_term(connection, function)?,
            render_term(connection, argument)?
        )),
        TermView::Lambda {
            parameter_type,
            body,
        } => Ok(format!(
            "(LAM:{} {})",
            render_type(connection, parameter_type)?,
            render_term(connection, body)?
        )),
        TermView::Equality { left, right } => Ok(format!(
            "(EQ {} {})",
            render_term(connection, left)?,
            render_term(connection, right)?
        )),
        TermView::Epsilon { predicate } => {
            Ok(format!("(EPS {})", render_term(connection, predicate)?))
        }
        TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::TypeLambda { .. }
        | TermView::TypeApplication { .. } => Err(SignedHolRoundTripError::invalid(
            "assumption-profile-checked",
            "formula contains a non-profile term constructor",
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;

    #[test]
    fn signed_fixture_has_frozen_validated_counts() {
        let kernel = Kernel::ephemeral();
        let assumption = produce_signed_dedekind_infinity_assumption(&kernel).unwrap();
        let validated = ValidatedHolImage::validate(assumption.artifact().image()).unwrap();
        verify_validated_assumption_counts(&validated).unwrap();
    }

    #[test]
    fn bounded_receive_rolls_back_and_full_trust_open_retries() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let assumption = produce_signed_dedekind_infinity_assumption(&kernel).unwrap();

        let Err(error) = retain_signed_dedekind_infinity_assumption_bounded(
            &kernel,
            &mut directory,
            &assumption,
            0,
        ) else {
            panic!("zero connection-ID bound must reject the receiver");
        };
        assert!(
            error.to_string().contains("receiver-retained"),
            "unexpected error: {error}"
        );
        assert!(directory.connections().unwrap().is_empty());
        assert_eq!(directory.active().unwrap(), None);

        let (owner, retained) = retain_signed_dedekind_infinity_assumption_bounded(
            &kernel,
            &mut directory,
            &assumption,
            i64::from(u32::MAX),
        )
        .unwrap();
        assert_eq!(directory.active().unwrap(), Some(owner));
        assert_eq!(retained.received().context_id(), assumption.context().get());
        assert_eq!(
            retained.received().conclusion_id(),
            assumption.conclusion().get()
        );

        directory
            .state()
            .sqlite()
            .execute_batch(
                "CREATE TEMP TRIGGER reject_assumption_child
                 BEFORE INSERT ON main.repl_connection
                 BEGIN SELECT RAISE(FAIL, 'reject assumption child'); END;",
            )
            .unwrap();
        let before = directory.connections().unwrap();
        let error =
            open_retained_trusted_hol_as_managed_state(&mut directory, owner, &retained, AllowAll)
                .unwrap_err();
        assert!(error.to_string().contains("child-retained"));
        assert_eq!(directory.connections().unwrap(), before);
        assert_eq!(directory.active().unwrap(), Some(owner));

        directory
            .state()
            .sqlite()
            .execute_batch("DROP TRIGGER temp.reject_assumption_child")
            .unwrap();
        let opened =
            open_retained_trusted_hol_as_managed_state(&mut directory, owner, &retained, AllowAll)
                .unwrap();
        assert_eq!(opened.context_id(), assumption.context().get());
        assert_eq!(opened.conclusion_id(), assumption.conclusion().get());
        directory
            .get_mut(opened.connection())
            .unwrap()
            .hol_mut()
            .unwrap()
            .insert_bool_term(false)
            .unwrap();
    }

    #[test]
    fn exact_graph_matches_the_independent_literal_oracle() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let syntax = build_dedekind_infinity_syntax(&mut connection).unwrap();
        assert_eq!(
            render_term(&mut connection, syntax.conclusion()).unwrap(),
            DEDEKIND_INFINITY_GRAPH
        );
        let TermView::Application { function, argument } =
            connection.term(syntax.conclusion()).unwrap()
        else {
            panic!("root must be application")
        };
        let TermView::Epsilon { predicate } = connection.term(argument).unwrap() else {
            panic!("root argument must be epsilon")
        };
        assert_eq!(function, syntax.property());
        assert_eq!(predicate, syntax.property());
        assert_eq!(argument, syntax.witness());
    }
}
