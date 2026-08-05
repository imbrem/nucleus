use super::{
    AllowAll, Connection, ConnectionId, ContextId, ExpectedKernelIdentity, Hol, KernelId,
    LocalConnection, Repl, RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact, build_canonical_false,
    prepare_retained_trusted_hol_state, produce_signed_dedekind_infinity_assumption,
    retain_signed_dedekind_infinity_assumption,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, TermError, TermId, TermView, TypeId,
    TypeView, ValidatedHolImage,
};
use std::collections::HashSet;

const MISSING_ORACLE: &str =
    "(LAM:I (EQ (APP (LAM:I (EQ (APP s #0:I) #1:I)) (EPS (LAM:I (EQ (APP s #0:I) #1:I)))) F))";
const FALSE_ORACLE: &str = "(EQ (LAM:B #0:B) (LAM:B true))";
const CONJUNCTION_ORACLE: &str = "(LAM:B (LAM:B (EQ (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) #2:B) #1:B)) (LAM:(B->(B->B)) (APP (APP #0:(B->(B->B)) true) true)))))";
const ZERO_ORACLE: &str = "(EPS missing)";
const CLOSED_ORACLE: &str = "(LAM:(I->B) (APP (APP AND (APP #0:(I->B) zero)) (EQ (LAM:I (EQ (APP (APP AND (APP #1:(I->B) #0:I)) (APP #1:(I->B) (APP s #0:I))) (APP #1:(I->B) #0:I))) (LAM:I true))))";
const NATLIKE_ORACLE: &str = "(LAM:I (EQ (LAM:(I->B) (EQ (APP (APP AND (APP closed #0:(I->B))) (APP #0:(I->B) #1:I)) (APP closed #0:(I->B)))) (LAM:(I->B) true)))";

/// Checked coordinates for the syntax-only `NatLike` predicate extension.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NatLikeSyntax {
    missing: TermId,
    zero: TermId,
    successor_closed: TermId,
    natlike: TermId,
}

impl NatLikeSyntax {
    /// Returns `lambda y. not (exists x. succ x = y)`.
    #[must_use]
    pub const fn missing(self) -> TermId {
        self.missing
    }

    /// Returns the epsilon-selected missing point.
    #[must_use]
    pub const fn zero(self) -> TermId {
        self.zero
    }

    /// Returns the predicate-of-predicates containing zero and closed under successor.
    #[must_use]
    pub const fn successor_closed(self) -> TermId {
        self.successor_closed
    }

    /// Returns the impredicative induction predicate over the selected `zero` and `succ`.
    #[must_use]
    pub const fn natlike(self) -> TermId {
        self.natlike
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

fn logical_all(
    connection: &mut Connection<Hol<AllowAll>>,
    parameter_type: TypeId,
    predicate: TermId,
    truth: TermId,
) -> Result<TermId, TermError> {
    let constant_truth = connection.insert_lambda(parameter_type, truth)?;
    connection.insert_equality(predicate, constant_truth)
}

fn build_conjunction(
    connection: &mut Connection<Hol<AllowAll>>,
    bool_type: TypeId,
    truth: TermId,
) -> Result<TermId, TermError> {
    let bool_to_bool = connection.insert_arrow_type(bool_type, bool_type)?;
    let bool_binary = connection.insert_arrow_type(bool_type, bool_to_bool)?;
    let choice = connection.insert_bound_term(0, bool_binary)?;
    let left = connection.insert_bound_term(2, bool_type)?;
    let right = connection.insert_bound_term(1, bool_type)?;
    let selected = apply2(connection, choice, left, right)?;
    let selected_truth = apply2(connection, choice, truth, truth)?;
    let selected = connection.insert_lambda(bool_binary, selected)?;
    let selected_truth = connection.insert_lambda(bool_binary, selected_truth)?;
    let body = connection.insert_equality(selected, selected_truth)?;
    let body = connection.insert_lambda(bool_type, body)?;
    connection.insert_lambda(bool_type, body)
}

fn implication(
    connection: &mut Connection<Hol<AllowAll>>,
    conjunction: TermId,
    antecedent: TermId,
    consequent: TermId,
) -> Result<TermId, TermError> {
    let both = apply2(connection, conjunction, antecedent, consequent)?;
    connection.insert_equality(both, antecedent)
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
        .map_err(|error| SignedHolRoundTripError::at("natlike-exact-oracle", error))?
    {
        TypeView::Bool => Ok("B".to_owned()),
        TypeView::Arrow { domain, codomain } => Ok(format!(
            "({}->{})",
            render_type(connection, domain, ind)?,
            render_type(connection, codomain, ind)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            "natlike-exact-oracle",
            "NatLike syntax contains a non-profile type",
        )),
    }
}

#[derive(Clone, Copy)]
struct OracleAtoms {
    successor: TermId,
    conjunction: TermId,
    falsehood: TermId,
    missing: TermId,
    zero: TermId,
    closed: TermId,
}

fn render_term(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
    ind: TypeId,
    root: TermId,
    atoms: OracleAtoms,
) -> Result<String, SignedHolRoundTripError> {
    if term != root {
        if term == atoms.successor {
            return Ok("s".to_owned());
        }
        if term == atoms.conjunction {
            return Ok("AND".to_owned());
        }
        if term == atoms.falsehood {
            return Ok("F".to_owned());
        }
        if term == atoms.missing {
            return Ok("missing".to_owned());
        }
        if term == atoms.zero {
            return Ok("zero".to_owned());
        }
        if term == atoms.closed {
            return Ok("closed".to_owned());
        }
    }
    match connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at("natlike-exact-oracle", error))?
    {
        TermView::Bool(true) => Ok("true".to_owned()),
        TermView::Bool(false) => Ok("false".to_owned()),
        TermView::Bound { index } => {
            let ty = connection
                .term_type(term)
                .map_err(|error| SignedHolRoundTripError::at("natlike-exact-oracle", error))?;
            Ok(format!("#{index}:{}", render_type(connection, ty, ind)?))
        }
        TermView::Application { function, argument } => Ok(format!(
            "(APP {} {})",
            render_term(connection, function, ind, root, atoms)?,
            render_term(connection, argument, ind, root, atoms)?
        )),
        TermView::Lambda {
            parameter_type,
            body,
        } => Ok(format!(
            "(LAM:{} {})",
            render_type(connection, parameter_type, ind)?,
            render_term(connection, body, ind, root, atoms)?
        )),
        TermView::Equality { left, right } => Ok(format!(
            "(EQ {} {})",
            render_term(connection, left, ind, root, atoms)?,
            render_term(connection, right, ind, root, atoms)?
        )),
        TermView::Epsilon { predicate } => Ok(format!(
            "(EPS {})",
            render_term(connection, predicate, ind, root, atoms)?
        )),
        TermView::Free { .. }
        | TermView::Constant { .. }
        | TermView::TypeLambda { .. }
        | TermView::TypeApplication { .. } => Err(SignedHolRoundTripError::invalid(
            "natlike-exact-oracle",
            "NatLike syntax contains a non-profile term",
        )),
    }
}

fn verify_exact_natlike_oracle(
    connection: &mut Connection<Hol<AllowAll>>,
    ind: TypeId,
    successor: TermId,
    conjunction: TermId,
    falsehood: TermId,
    syntax: NatLikeSyntax,
) -> Result<(), SignedHolRoundTripError> {
    let atoms = OracleAtoms {
        successor,
        conjunction,
        falsehood,
        missing: syntax.missing(),
        zero: syntax.zero(),
        closed: syntax.successor_closed(),
    };
    let terms = [
        (falsehood, FALSE_ORACLE),
        (conjunction, CONJUNCTION_ORACLE),
        (syntax.missing(), MISSING_ORACLE),
        (syntax.zero(), ZERO_ORACLE),
        (syntax.successor_closed(), CLOSED_ORACLE),
        (syntax.natlike(), NATLIKE_ORACLE),
    ];
    for (term, expected) in terms {
        if render_term(connection, term, ind, term, atoms)? != expected {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-exact-oracle",
                "NatLike syntax differs from the pinned structural literal oracle",
            ));
        }
    }
    Ok(())
}

fn build_missing_and_zero(
    connection: &mut Connection<Hol<AllowAll>>,
    ind: TypeId,
    successor: TermId,
    falsehood: TermId,
) -> Result<(TermId, TermId), SignedHolRoundTripError> {
    let argument = connection
        .insert_bound_term(0, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let target = connection
        .insert_bound_term(1, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let image = connection
        .insert_application(successor, argument)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let hits_target = connection
        .insert_equality(image, target)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let preimage = connection
        .insert_lambda(ind, hits_target)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let witness = connection
        .insert_epsilon(preimage)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let exists = connection
        .insert_application(preimage, witness)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let absent = connection
        .insert_equality(exists, falsehood)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let missing = connection
        .insert_lambda(ind, absent)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let zero = connection
        .insert_epsilon(missing)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    Ok((missing, zero))
}

/// Builds `missing`, `zero`, and the impredicative `NatLike` predicate through checked APIs.
///
/// This creates syntax only. It inserts no judgement and invokes no primitive proof rule.
///
/// # Errors
///
/// Returns if a checked type or term constructor rejects the graph.
fn build_natlike_syntax_with_falsehood(
    connection: &mut Connection<Hol<AllowAll>>,
    ind: TypeId,
    succ: TermId,
    falsehood: TermId,
) -> Result<NatLikeSyntax, SignedHolRoundTripError> {
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let predicate_type = connection
        .insert_arrow_type(ind, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let truth = connection
        .insert_bool_term(true)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let conjunction = build_conjunction(connection, bool_type, truth)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;

    let (missing, zero) = build_missing_and_zero(connection, ind, succ, falsehood)?;

    // closed = λP. AND (P zero) (ALL y. IMP (P y) (P (succ y))).
    let step_predicate = connection
        .insert_bound_term(1, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let step_point = connection
        .insert_bound_term(0, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let premise = connection
        .insert_application(step_predicate, step_point)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let successor = connection
        .insert_application(succ, step_point)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let successor_case = connection
        .insert_application(step_predicate, successor)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let step = implication(connection, conjunction, premise, successor_case)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let step = connection
        .insert_lambda(ind, step)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let step = logical_all(connection, ind, step, truth)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let closed_predicate = connection
        .insert_bound_term(0, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let base = connection
        .insert_application(closed_predicate, zero)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let closed_body = apply2(connection, conjunction, base, step)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let successor_closed = connection
        .insert_lambda(predicate_type, closed_body)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;

    // NatLike = λx. ALL P. IMP (closed P) (P x).
    let candidate_predicate = connection
        .insert_bound_term(0, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let point = connection
        .insert_bound_term(1, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let is_closed = connection
        .insert_application(successor_closed, candidate_predicate)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let contains_point = connection
        .insert_application(candidate_predicate, point)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let candidate = implication(connection, conjunction, is_closed, contains_point)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let candidate = connection
        .insert_lambda(predicate_type, candidate)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let all_candidates = logical_all(connection, predicate_type, candidate, truth)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let natlike = connection
        .insert_lambda(ind, all_candidates)
        .map_err(|error| SignedHolRoundTripError::at("natlike-syntax-checked", error))?;
    let syntax = NatLikeSyntax {
        missing,
        zero,
        successor_closed,
        natlike,
    };
    verify_exact_natlike_oracle(connection, ind, succ, conjunction, falsehood, syntax)?;
    Ok(syntax)
}

/// Builds `missing`, `zero`, and the impredicative `NatLike` predicate through checked APIs.
///
/// Logical false is the canonical definition `ALL_B (lambda p. p)`. This
/// creates syntax only: it inserts no judgement and invokes no proof rule.
///
/// # Errors
///
/// Returns if a checked type or term constructor rejects the graph.
pub fn build_natlike_syntax(
    connection: &mut Connection<Hol<AllowAll>>,
    ind: TypeId,
    succ: TermId,
) -> Result<NatLikeSyntax, SignedHolRoundTripError> {
    let falsehood = build_canonical_false(connection)?;
    build_natlike_syntax_with_falsehood(connection, ind, succ, falsehood)
}

/// Signed syntax extension whose sole judgement is the inherited infinity assumption.
pub struct SignedNatLikeArtifact {
    artifact: SignedHolArtifact,
    context: ContextId,
    infinity: TermId,
    syntax: NatLikeSyntax,
}

impl SignedNatLikeArtifact {
    /// Returns the exact signed image and schema-qualified signature.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Returns the inherited empty context.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }

    /// Returns the inherited Dedekind-infinity judgement conclusion.
    #[must_use]
    pub const fn infinity(&self) -> TermId {
        self.infinity
    }

    /// Returns the syntax-only extension coordinates.
    #[must_use]
    pub const fn syntax(&self) -> NatLikeSyntax {
        self.syntax
    }

    /// Classifies this artifact without presenting `NatLike` as proved.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-natlike-syntax"
    }

    /// Renders an explicit authority sidecar for the exact signed bytes.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=signed-assumption\nassumption=dedekind-infinity\nfalsehood=all-bool-identity\nextension=predicate-natlike-syntax\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn named_export(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: covalence_nucleus::NamespaceId,
    name: &str,
) -> Result<NamespaceExport, SignedHolRoundTripError> {
    connection
        .resolve_export_name(namespace, name)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-export-resolved", error))?
        .map(|(_, export)| export.value)
        .ok_or_else(|| {
            SignedHolRoundTripError::at(
                "natlike-inherited-export-resolved",
                format_args!("missing inherited export {name}"),
            )
        })
}

fn verify_inherited_infinity_shape(
    connection: &mut Connection<Hol<AllowAll>>,
    infinity: TermId,
    property: TermId,
    successor: TermId,
) -> Result<(), SignedHolRoundTripError> {
    let root = connection
        .term(infinity)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let witness = connection
        .term(successor)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    if root
        != (TermView::Application {
            function: property,
            argument: successor,
        })
        || witness
            != (TermView::Epsilon {
                predicate: property,
            })
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-shape-checked",
            "inherited conclusion must apply PROPERTY to its exact epsilon witness",
        ));
    }
    Ok(())
}

fn term_reaches(
    connection: &mut Connection<Hol<AllowAll>>,
    root: TermId,
    needle: TermId,
) -> Result<bool, SignedHolRoundTripError> {
    fn walk(
        connection: &mut Connection<Hol<AllowAll>>,
        term: TermId,
        needle: TermId,
        visited: &mut HashSet<TermId>,
    ) -> Result<bool, SignedHolRoundTripError> {
        if term == needle {
            return Ok(true);
        }
        if !visited.insert(term) {
            return Ok(false);
        }
        let children = match connection.term(term).map_err(|error| {
            SignedHolRoundTripError::at("natlike-inherited-shape-checked", error)
        })? {
            TermView::Application { function, argument }
            | TermView::Equality {
                left: function,
                right: argument,
            } => [Some(function), Some(argument)],
            TermView::Lambda { body, .. }
            | TermView::Epsilon { predicate: body }
            | TermView::TypeLambda { body } => [Some(body), None],
            TermView::TypeApplication { function, .. } => [Some(function), None],
            TermView::Bool(_)
            | TermView::Bound { .. }
            | TermView::Free { .. }
            | TermView::Constant { .. } => [None, None],
        };
        for child in children.into_iter().flatten() {
            if walk(connection, child, needle, visited)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    walk(connection, root, needle, &mut HashSet::new())
}

#[derive(Clone, Copy)]
struct InheritedInfinitySyntax {
    ind: TypeId,
    property: TermId,
    successor: TermId,
    falsehood: TermId,
}

fn resolve_inherited_infinity_syntax(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: covalence_nucleus::NamespaceId,
    expected_context: ContextId,
    conclusion: TermId,
) -> Result<InheritedInfinitySyntax, SignedHolRoundTripError> {
    let NamespaceExport::Context(context) =
        named_export(connection, namespace, "empty-assumption-context")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "inherited empty context export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(exported_conclusion) =
        named_export(connection, namespace, "dedekind-infinity-assumption")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "inherited infinity export has the wrong sort",
        ));
    };
    if context != expected_context || exported_conclusion != conclusion {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "typed Stage-A coordinates differ from their exact named exports",
        ));
    }
    let NamespaceExport::Type(ind) = named_export(connection, namespace, "ind")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "inherited ind export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(property) =
        named_export(connection, namespace, "dedekind-endomap-property")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "inherited property export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor) = named_export(connection, namespace, "dedekind-endomap")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-export-resolved",
            "inherited endomap export has the wrong sort",
        ));
    };
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let endomap = connection
        .insert_arrow_type(ind, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let property_type = connection
        .insert_arrow_type(endomap, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let successor_type = connection
        .term_type(successor)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let actual_property_type = connection
        .term_type(property)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let conclusion_type = connection
        .term_type(conclusion)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    let conclusion_closed = connection
        .term_is_locally_closed(conclusion)
        .map_err(|error| SignedHolRoundTripError::at("natlike-inherited-shape-checked", error))?;
    if successor_type != endomap
        || actual_property_type != property_type
        || conclusion_type != bool_type
        || !conclusion_closed
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-shape-checked",
            "inherited successor, property, or conclusion has the wrong checked type/closure",
        ));
    }
    verify_inherited_infinity_shape(connection, conclusion, property, successor)?;
    let falsehood = build_canonical_false(connection)?;
    if !term_reaches(connection, property, falsehood)? {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-inherited-shape-checked",
            "inherited property does not contain the canonical logical false node",
        ));
    }
    Ok(InheritedInfinitySyntax {
        ind,
        property,
        successor,
        falsehood,
    })
}

fn export_natlike_namespace(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    infinity: TermId,
    ind: TypeId,
    property: TermId,
    succ: TermId,
    syntax: NatLikeSyntax,
) -> Result<covalence_nucleus::NamespaceId, SignedHolRoundTripError> {
    let namespace = connection
        .create_namespace(None, Some("predicate-natlike-v1"))
        .map_err(|error| SignedHolRoundTripError::at("natlike-namespace-exported", error))?;
    let exports = [
        (
            0,
            NamespaceExport::Context(context),
            "empty-assumption-context",
        ),
        (
            1,
            NamespaceExport::Term(infinity),
            "dedekind-infinity-assumption",
        ),
        (2, NamespaceExport::Type(ind), "ind"),
        (
            3,
            NamespaceExport::Term(property),
            "dedekind-endomap-property",
        ),
        (4, NamespaceExport::Term(succ), "successor"),
        (
            5,
            NamespaceExport::Term(syntax.missing()),
            "missing-preimage",
        ),
        (6, NamespaceExport::Term(syntax.zero()), "zero"),
        (
            7,
            NamespaceExport::Term(syntax.successor_closed()),
            "successor-closed",
        ),
        (8, NamespaceExport::Term(syntax.natlike()), "nat-like"),
    ];
    for (slot, value, name) in exports {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("natlike-namespace-exported", error))?;
    }
    Ok(namespace)
}

fn verify_no_primitive_false(
    connection: &sqlite::Connection,
) -> Result<(), SignedHolRoundTripError> {
    let primitive_false_rows = connection
        .query_row(
            "SELECT count(*) FROM hol_node WHERE tag = 'MBOOL' AND lhs = 0",
            [],
            |row| row.get::<_, i64>(0),
        )
        .map_err(|error| SignedHolRoundTripError::at("natlike-export-profile-checked", error))?;
    if primitive_false_rows != 0 {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-export-profile-checked",
            "complete NatLike image contains primitive Boolean false",
        ));
    }
    Ok(())
}

fn verify_raw_natlike_namespace(
    raw: &covalence_neutron::Connection,
    namespace: covalence_nucleus::NamespaceId,
    context: ContextId,
    infinity: TermId,
    inherited: InheritedInfinitySyntax,
    syntax: NatLikeSyntax,
) -> Result<(), SignedHolRoundTripError> {
    let connection = raw.sqlite();
    verify_no_primitive_false(connection)?;
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
        .map_err(|error| SignedHolRoundTripError::at("natlike-export-profile-checked", error))?;
    if namespace_profile != ("predicate-natlike-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-export-profile-checked",
            "NatLike namespace differs from the exact local profile",
        ));
    }
    let mut statement = connection
        .prepare(
            "SELECT export_id, sort, local_id, name FROM hol_namespace_export
             WHERE namespace_id = ?1 ORDER BY export_id",
        )
        .map_err(|error| SignedHolRoundTripError::at("natlike-export-profile-checked", error))?;
    let actual = statement
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("natlike-export-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("natlike-export-profile-checked", error))?;
    let expected = vec![
        (
            0,
            "context".to_owned(),
            context.get(),
            "empty-assumption-context".to_owned(),
        ),
        (
            1,
            "term".to_owned(),
            infinity.get(),
            "dedekind-infinity-assumption".to_owned(),
        ),
        (2, "type".to_owned(), inherited.ind.get(), "ind".to_owned()),
        (
            3,
            "term".to_owned(),
            inherited.property.get(),
            "dedekind-endomap-property".to_owned(),
        ),
        (
            4,
            "term".to_owned(),
            inherited.successor.get(),
            "successor".to_owned(),
        ),
        (
            5,
            "term".to_owned(),
            syntax.missing().get(),
            "missing-preimage".to_owned(),
        ),
        (6, "term".to_owned(), syntax.zero().get(), "zero".to_owned()),
        (
            7,
            "term".to_owned(),
            syntax.successor_closed().get(),
            "successor-closed".to_owned(),
        ),
        (
            8,
            "term".to_owned(),
            syntax.natlike().get(),
            "nat-like".to_owned(),
        ),
    ];
    if actual != expected {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-export-profile-checked",
            "NatLike exports differ from the exact slot/sort/name/value profile",
        ));
    }
    Ok(())
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 89,
        contexts: 1,
        members: 0,
        untrusted_judgement_rows: 1,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 3,
        namespace_exports: 14,
        import_references: 1,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 1,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-image-validated",
            "NatLike image differs from the frozen complete-state profile",
        ));
    }
    Ok(())
}

/// Extends the signed infinity snapshot with `NatLike` syntax and signs the exact result.
///
/// The inherited `(empty, infinity)` row remains the only judgement. The first
/// trusted reopen authorizes using that signed assumption as kernel state; the
/// newly constructed `NatLike` terms and exports carry no theorem authority.
///
/// # Errors
///
/// Returns the first rejected inherited-artifact, checked syntax, export,
/// detached validation, or signing boundary.
pub fn produce_signed_natlike_artifact(
    producer: &Kernel,
) -> Result<SignedNatLikeArtifact, SignedHolRoundTripError> {
    let infinity_artifact = produce_signed_dedekind_infinity_assumption(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-staging-opened", error))?;
    let (source, retained) =
        retain_signed_dedekind_infinity_assumption(producer, &mut staging, &infinity_artifact)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, source, &retained, AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("natlike-infinity-state-opened", error))?;
    let inherited_namespace =
        covalence_nucleus::NamespaceId::from_i64(infinity_artifact.artifact().namespace_id());
    let inherited = resolve_inherited_infinity_syntax(
        &mut connection,
        inherited_namespace,
        infinity_artifact.context(),
        infinity_artifact.conclusion(),
    )?;
    let syntax = build_natlike_syntax_with_falsehood(
        &mut connection,
        inherited.ind,
        inherited.successor,
        inherited.falsehood,
    )?;
    let namespace = export_natlike_namespace(
        &mut connection,
        infinity_artifact.context(),
        infinity_artifact.conclusion(),
        inherited.ind,
        inherited.property,
        inherited.successor,
        syntax,
    )?;
    let preliminary = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("natlike-image-serialized", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(preliminary.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-image-copied", error))?;
    verify_raw_natlike_namespace(
        &raw,
        namespace,
        infinity_artifact.context(),
        infinity_artifact.conclusion(),
        inherited,
        syntax,
    )?;
    let judgement = raw
        .sqlite()
        .query_row(
            "SELECT count(*), min(ctx_id), min(term_id) FROM hol_judgement",
            [],
            |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, i64>(2)?,
                ))
            },
        )
        .map_err(|error| SignedHolRoundTripError::at("natlike-sole-judgement-checked", error))?;
    if judgement
        != (
            1,
            infinity_artifact.context().get(),
            infinity_artifact.conclusion().get(),
        )
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-sole-judgement-checked",
            "NatLike extension must preserve exactly the inherited infinity judgement",
        ));
    }
    let validated = ValidatedHolImage::validate(preliminary.image().bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-image-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let attestation = preliminary.attestation();
    Ok(SignedNatLikeArtifact {
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image: validated.bytes().to_vec(),
            schema: attestation.schema(),
            image_hash: attestation.image(),
            signer: attestation.signer(),
            public_key: attestation.public_key().to_vec(),
            signature: attestation.signature().to_vec(),
        },
        context: infinity_artifact.context(),
        infinity: infinity_artifact.conclusion(),
        syntax,
    })
}

/// Produces and retains the signed syntax extension in a fresh selected receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_natlike_artifact(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<
    (
        SignedNatLikeArtifact,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    let artifact = produce_signed_natlike_artifact(producer)?;
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("natlike-signer-selected", error))?;
    let independently_expected = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-signer-selected", error))?;
    if expected != independently_expected {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-signer-selected",
            "REPL local endpoint key differs from the NatLike artifact signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("natlike-receiver-opened", error))?;
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

    #[test]
    fn signed_natlike_extension_has_one_inherited_judgement_and_reopens() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_natlike_artifact(&kernel, &mut directory).unwrap();
        let opened =
            open_retained_trusted_hol_as_managed_state(&mut directory, owner, &retained, AllowAll)
                .unwrap();
        assert_eq!(artifact.kind(), "signed-natlike-syntax");
        assert_eq!(retained.received().context_id(), artifact.context().get());
        assert_eq!(
            retained.received().conclusion_id(),
            artifact.infinity().get()
        );
        assert_eq!(opened.context_id(), artifact.context().get());
        assert_eq!(opened.conclusion_id(), artifact.infinity().get());
        assert_ne!(owner, opened.connection());
        assert!(artifact.attestation_text().starts_with(
            "authority=signed-assumption\nassumption=dedekind-infinity\n\
                     falsehood=all-bool-identity\nextension=predicate-natlike-syntax\n"
        ));
        let child = directory
            .get_mut(opened.connection())
            .unwrap()
            .hol_mut()
            .unwrap();
        let TermView::Lambda { body, .. } = child.term(artifact.syntax().missing()).unwrap() else {
            panic!("missing-preimage must be a lambda")
        };
        let TermView::Equality { right, .. } = child.term(body).unwrap() else {
            panic!("missing-preimage body must be logical negation")
        };
        assert_eq!(right, build_canonical_false(child).unwrap());
        let natlike_zero = child
            .insert_application(artifact.syntax().natlike(), artifact.syntax().zero())
            .unwrap();
        let natlike_is_not_a_theorem = child
            .with_proof_session(|mut proof| {
                proof
                    .load_theorem(artifact.context(), natlike_zero)
                    .map(|theorem| theorem.is_some())
            })
            .unwrap();
        assert!(!natlike_is_not_a_theorem);
        let validated = ValidatedHolImage::validate(artifact.artifact().image()).unwrap();
        assert_eq!(validated.counts().untrusted_judgement_rows, 1);
        assert_eq!(validated.counts().import_references, 1);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);
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
        let profile = raw
            .sqlite()
            .query_row(
                "SELECT group_concat(export_id || ':' || sort || ':' || name, '|')
                 FROM (
                     SELECT export_id, sort, name FROM hol_namespace_export
                     WHERE namespace_id = ?1 ORDER BY export_id
                 )",
                [artifact.artifact().namespace_id()],
                |row| row.get::<_, String>(0),
            )
            .unwrap();
        assert_eq!(
            profile,
            "0:context:empty-assumption-context|1:term:dedekind-infinity-assumption|\
             2:type:ind|3:term:dedekind-endomap-property|4:term:successor|\
             5:term:missing-preimage|6:term:zero|7:term:successor-closed|8:term:nat-like"
        );
    }

    #[test]
    fn complete_image_profile_rejects_even_unreachable_primitive_false() {
        let kernel = Kernel::ephemeral();
        let artifact = produce_signed_natlike_artifact(&kernel).unwrap();
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
