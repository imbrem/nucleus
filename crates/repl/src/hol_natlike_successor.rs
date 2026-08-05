use super::{
    AllElim, AllIntroApplied, AllowAll, AndElim, Connection, ConnectionId, ContextId,
    ExpectedKernelIdentity, Hol, ImpElim, ImpIntro, KernelId, LocalConnection, Repl,
    RetainedReceivedHolSnapshot, SignedHolArtifact, SignedHolRoundTripError,
    authenticate_pinned_signed_hol_artifact, prepare_retained_trusted_hol_state,
    produce_signed_natlike_zero, retain_signed_natlike_zero,
    trust_receive_and_retain_bounded_selected_managed_hol_artifact,
};
use covalence_lib_sqlite as sqlite;
use covalence_nucleus::{
    ExportId, HolImageCounts, Kernel, NamespaceExport, NamespaceId, TermError, TermId, TermView,
    TypeId, TypeView, ValidatedHolImage,
};

const SUCCESSOR_CLOSURE_ORACLE: &str =
    "(EQ (LAM:I (EQ (APP (APP AND (APP N #0:I)) (APP N (APP s #0:I))) (APP N #0:I))) (LAM:I true))";

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
    conjunction: TermId,
    successor: TermId,
    successor_closed: TermId,
    natlike: TermId,
    point: TermId,
    predicate: TermId,
    natlike_point: TermId,
    successor_point: TermId,
    natlike_successor: TermId,
    closed_predicate: TermId,
    point_candidate: TermId,
    point_candidate_instance: TermId,
    point_universal: TermId,
    point_implication: TermId,
    step_predicate: TermId,
    step_instance: TermId,
    step_implication: TermId,
    closed_body: TermId,
    successor_candidate: TermId,
    successor_candidate_instance: TermId,
    successor_universal: TermId,
    closed_to_successor: TermId,
    outer_predicate: TermId,
    outer_instance: TermId,
    outer_implication: TermId,
    conclusion: TermId,
}

struct ProofPlan {
    graph: ProofGraph,
    outer_implication: ImpIntro,
    inner_implication: ImpIntro,
    point_all_elimination: AllElim,
    point_implication_elimination: ImpElim,
    closure_step_elimination: AndElim,
    step_all_elimination: AllElim,
    step_implication_elimination: ImpElim,
    successor_all_introduction: AllIntroApplied,
    outer_all_introduction: AllIntroApplied,
}

fn named_export(
    connection: &mut Connection<Hol<AllowAll>>,
    namespace: NamespaceId,
    name: &str,
) -> Result<NamespaceExport, SignedHolRoundTripError> {
    connection
        .resolve_export_name(namespace, name)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?
        .map(|(_, export)| export.value)
        .ok_or_else(|| {
            SignedHolRoundTripError::at(
                "natlike-successor-source-resolved",
                format_args!("missing exact source export {name}"),
            )
        })
}

// Keeping the complete named-source contract together makes the trust-boundary
// checks easier to audit against the exported NatLike profile.
#[allow(clippy::too_many_lines)]
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
            "natlike-successor-source-resolved",
            "NatLike context export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(infinity) =
        named_export(connection, namespace, "dedekind-infinity-assumption")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike infinity export has the wrong sort",
        ));
    };
    let NamespaceExport::Type(ind) = named_export(connection, namespace, "ind")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike individual type export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor) = named_export(connection, namespace, "successor")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike successor export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(zero) = named_export(connection, namespace, "zero")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike zero export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(successor_closed) =
        named_export(connection, namespace, "successor-closed")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike closure export has the wrong sort",
        ));
    };
    let NamespaceExport::Term(natlike) = named_export(connection, namespace, "nat-like")? else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "NatLike predicate export has the wrong sort",
        ));
    };
    if context != expected_context || infinity != expected_infinity {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "typed source coordinates differ from the exact NatLike exports",
        ));
    }
    let bool_type = connection
        .insert_bool_type()
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?;
    let predicate_type = connection
        .insert_arrow_type(ind, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?;
    let endomap_type = connection
        .insert_arrow_type(ind, ind)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?;
    let closure_type = connection
        .insert_arrow_type(predicate_type, bool_type)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?;
    if connection
        .term_type(successor)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-source-resolved", error))?
        != endomap_type
        || connection.term_type(zero).map_err(|error| {
            SignedHolRoundTripError::at("natlike-successor-source-resolved", error)
        })? != ind
        || connection.term_type(successor_closed).map_err(|error| {
            SignedHolRoundTripError::at("natlike-successor-source-resolved", error)
        })? != closure_type
        || connection.term_type(natlike).map_err(|error| {
            SignedHolRoundTripError::at("natlike-successor-source-resolved", error)
        })? != predicate_type
        || !connection
            .term_is_locally_closed(successor_closed)
            .map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-source-resolved", error)
            })?
        || !connection
            .term_is_locally_closed(natlike)
            .map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-source-resolved", error)
            })?
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
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

fn universal(
    connection: &mut Connection<Hol<AllowAll>>,
    parameter_type: TypeId,
    predicate: TermId,
    truth: TermId,
) -> Result<TermId, TermError> {
    let constant_truth = connection.insert_lambda(parameter_type, truth)?;
    connection.insert_equality(predicate, constant_truth)
}

fn natlike_candidate(
    connection: &mut Connection<Hol<AllowAll>>,
    source: SourceSyntax,
    and: TermId,
    predicate_type: TypeId,
    point: TermId,
) -> Result<TermId, TermError> {
    let predicate = connection.insert_bound_term(0, predicate_type)?;
    let closed = connection.insert_application(source.successor_closed, predicate)?;
    let contains = connection.insert_application(predicate, point)?;
    let body = implication(connection, and, closed, contains)?;
    connection.insert_lambda(predicate_type, body)
}

// This deliberately spells out the complete checked object-language graph. A
// compressed term DSL would hide more of the exact theorem than it removes.
#[allow(clippy::too_many_lines)]
fn prepare_proof(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    source: SourceSyntax,
) -> Result<ProofPlan, SignedHolRoundTripError> {
    let stage = "natlike-successor-proof-prepared";
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

    let point = connection
        .insert_free_term(0x53_55_43_58, source.ind)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate = connection
        .insert_free_term(0x53_55_43_50, predicate_type)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let natlike_point = connection
        .insert_application(source.natlike, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let successor_point = connection
        .insert_application(source.successor, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let natlike_successor = connection
        .insert_application(source.natlike, successor_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let closed_predicate = connection
        .insert_application(source.successor_closed, predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate_at_point = connection
        .insert_application(predicate, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate_at_successor = connection
        .insert_application(predicate, successor_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let point_candidate = natlike_candidate(connection, source, and, predicate_type, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let point_candidate_instance = connection
        .insert_application(point_candidate, predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let point_universal = universal(connection, predicate_type, point_candidate, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let point_implication = implication(connection, and, closed_predicate, predicate_at_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let step_point = connection
        .insert_bound_term(0, source.ind)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_premise = connection
        .insert_application(predicate, step_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_successor = connection
        .insert_application(source.successor, step_point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_consequent = connection
        .insert_application(predicate, step_successor)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_body = implication(connection, and, step_premise, step_consequent)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_predicate = connection
        .insert_lambda(source.ind, step_body)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_instance = connection
        .insert_application(step_predicate, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_universal = universal(connection, source.ind, step_predicate, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let step_implication = implication(connection, and, predicate_at_point, predicate_at_successor)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let predicate_at_zero = connection
        .insert_application(predicate, source.zero)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let closed_body = apply2(connection, and, predicate_at_zero, step_universal)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let successor_candidate =
        natlike_candidate(connection, source, and, predicate_type, successor_point)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let successor_candidate_instance = connection
        .insert_application(successor_candidate, predicate)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let successor_universal = universal(connection, predicate_type, successor_candidate, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let closed_to_successor =
        implication(connection, and, closed_predicate, predicate_at_successor)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let outer_bound = connection
        .insert_bound_term(0, source.ind)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_natlike = connection
        .insert_application(source.natlike, outer_bound)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_successor = connection
        .insert_application(source.successor, outer_bound)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_natlike_successor = connection
        .insert_application(source.natlike, outer_successor)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_body = implication(connection, and, outer_natlike, outer_natlike_successor)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_predicate = connection
        .insert_lambda(source.ind, outer_body)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_instance = connection
        .insert_application(outer_predicate, point)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let outer_implication = implication(connection, and, natlike_point, natlike_successor)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let conclusion = universal(connection, source.ind, outer_predicate, truth)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;

    let graph = ProofGraph {
        conjunction: and,
        successor: source.successor,
        successor_closed: source.successor_closed,
        natlike: source.natlike,
        point,
        predicate,
        natlike_point,
        successor_point,
        natlike_successor,
        closed_predicate,
        point_candidate,
        point_candidate_instance,
        point_universal,
        point_implication,
        step_predicate,
        step_instance,
        step_implication,
        closed_body,
        successor_candidate,
        successor_candidate_instance,
        successor_universal,
        closed_to_successor,
        outer_predicate,
        outer_instance,
        outer_implication,
        conclusion,
    };

    let outer_implication_plan =
        ImpIntro::prepare(connection, context, natlike_point, natlike_successor)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    let inner_implication = ImpIntro::prepare(
        connection,
        outer_implication_plan.premise_context(),
        closed_predicate,
        predicate_at_successor,
    )
    .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    Ok(ProofPlan {
        graph,
        outer_implication: outer_implication_plan,
        inner_implication,
        point_all_elimination: AllElim::prepare(connection, point_candidate, predicate)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        point_implication_elimination: ImpElim::prepare(
            connection,
            closed_predicate,
            predicate_at_point,
        )
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        closure_step_elimination: AndElim::right(connection, predicate_at_zero, step_universal)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        step_all_elimination: AllElim::prepare(connection, step_predicate, point)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        step_implication_elimination: ImpElim::prepare(
            connection,
            predicate_at_point,
            predicate_at_successor,
        )
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        successor_all_introduction: AllIntroApplied::prepare(
            connection,
            successor_candidate,
            predicate,
        )
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
        outer_all_introduction: AllIntroApplied::prepare(connection, outer_predicate, point)
            .map_err(|error| SignedHolRoundTripError::at(stage, error))?,
    })
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
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-exact-oracle", error))?
    {
        TypeView::Bool => Ok("B".to_owned()),
        TypeView::Arrow { domain, codomain } => Ok(format!(
            "({}->{})",
            render_type(connection, domain, ind)?,
            render_type(connection, codomain, ind)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            "natlike-successor-exact-oracle",
            "successor-closure target contains a non-profile type",
        )),
    }
}

fn render_target(
    connection: &mut Connection<Hol<AllowAll>>,
    term: TermId,
    root: TermId,
    ind: TypeId,
    graph: &ProofGraph,
) -> Result<String, SignedHolRoundTripError> {
    if term != root {
        if term == graph.conjunction {
            return Ok("AND".to_owned());
        }
        if term == graph.natlike {
            return Ok("N".to_owned());
        }
        if term == graph.successor {
            return Ok("s".to_owned());
        }
    }
    match connection
        .term(term)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-exact-oracle", error))?
    {
        TermView::Bool(true) => Ok("true".to_owned()),
        TermView::Bound { index } => {
            let ty = connection.term_type(term).map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-exact-oracle", error)
            })?;
            Ok(format!("#{index}:{}", render_type(connection, ty, ind)?))
        }
        TermView::Application { function, argument } => Ok(format!(
            "(APP {} {})",
            render_target(connection, function, root, ind, graph)?,
            render_target(connection, argument, root, ind, graph)?
        )),
        TermView::Lambda {
            parameter_type,
            body,
        } => Ok(format!(
            "(LAM:{} {})",
            render_type(connection, parameter_type, ind)?,
            render_target(connection, body, root, ind, graph)?
        )),
        TermView::Equality { left, right } => Ok(format!(
            "(EQ {} {})",
            render_target(connection, left, root, ind, graph)?,
            render_target(connection, right, root, ind, graph)?
        )),
        _ => Err(SignedHolRoundTripError::invalid(
            "natlike-successor-exact-oracle",
            "successor-closure target contains a non-profile term",
        )),
    }
}

fn verify_exact_target(
    connection: &mut Connection<Hol<AllowAll>>,
    ind: TypeId,
    graph: &ProofGraph,
) -> Result<(), SignedHolRoundTripError> {
    if render_target(connection, graph.conclusion, graph.conclusion, ind, graph)?
        != SUCCESSOR_CLOSURE_ORACLE
    {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-exact-oracle",
            "successor-closure target differs from the pinned structural literal",
        ));
    }
    Ok(())
}

fn exact_beta<'brand, P: covalence_nucleus::Policy>(
    proof: &mut covalence_nucleus::ProofSession<'brand, P>,
    abstraction: TermId,
    argument: TermId,
    expected_left: TermId,
    expected_right: TermId,
    stage: &'static str,
) -> Result<covalence_nucleus::Conversion<'brand>, SignedHolRoundTripError> {
    let beta = proof
        .conversion_beta(abstraction, argument)
        .map_err(|error| SignedHolRoundTripError::at(stage, error))?;
    if beta.left() != expected_left || beta.right() != expected_right {
        return Err(SignedHolRoundTripError::invalid(
            stage,
            "beta conversion differs from the exact prepared graph",
        ));
    }
    Ok(beta)
}

// Keep the linear LCF derivation visible in one place so every conversion and
// premise can be compared directly with the prepared graph above.
#[allow(clippy::too_many_lines)]
fn derive(
    connection: &mut Connection<Hol<AllowAll>>,
    plan: &ProofPlan,
) -> Result<(), SignedHolRoundTripError> {
    connection.with_proof_session(|mut proof| {
        let inner_context = plan.inner_implication.premise_context();
        let natlike_point = proof
            .prove_hypothesis(inner_context, plan.graph.natlike_point)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-point-hyp", error))?;
        let point_beta = exact_beta(
            &mut proof,
            plan.graph.natlike,
            plan.graph.point,
            plan.graph.natlike_point,
            plan.graph.point_universal,
            "natlike-successor-point-beta",
        )?;
        let point_universal = proof
            .convert_theorem(&natlike_point, &point_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-point-beta", error))?;
        let point_instance = plan
            .point_all_elimination
            .apply(&mut proof, &point_universal)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-point-all", error))?;
        let point_candidate_beta = exact_beta(
            &mut proof,
            plan.graph.point_candidate,
            plan.graph.predicate,
            plan.graph.point_candidate_instance,
            plan.graph.point_implication,
            "natlike-successor-point-candidate-beta",
        )?;
        let point_implication = proof
            .convert_theorem(&point_instance, &point_candidate_beta)
            .map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-point-candidate-beta", error)
            })?;
        let closed = proof
            .prove_hypothesis(inner_context, plan.graph.closed_predicate)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-closed-hyp", error))?;
        let predicate_at_point = plan
            .point_implication_elimination
            .apply(&mut proof, &point_implication, &closed)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-point-mp", error))?;

        let closed_beta = exact_beta(
            &mut proof,
            plan.graph.successor_closed,
            plan.graph.predicate,
            plan.graph.closed_predicate,
            plan.graph.closed_body,
            "natlike-successor-closed-beta",
        )?;
        let closed_body = proof
            .convert_theorem(&closed, &closed_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-closed-beta", error))?;
        let step_universal = plan
            .closure_step_elimination
            .apply(&mut proof, &closed_body)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-closed-and", error))?;
        let step_instance = plan
            .step_all_elimination
            .apply(&mut proof, &step_universal)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-step-all", error))?;
        let step_beta = exact_beta(
            &mut proof,
            plan.graph.step_predicate,
            plan.graph.point,
            plan.graph.step_instance,
            plan.graph.step_implication,
            "natlike-successor-step-beta",
        )?;
        let step_implication = proof
            .convert_theorem(&step_instance, &step_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-step-beta", error))?;
        let predicate_at_successor = plan
            .step_implication_elimination
            .apply(&mut proof, &step_implication, &predicate_at_point)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-step-mp", error))?;

        let closed_to_successor = plan
            .inner_implication
            .apply(&mut proof, &predicate_at_successor)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-inner-imp", error))?;
        if closed_to_successor.conclusion() != plan.graph.closed_to_successor {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-successor-inner-imp",
                "inner implication introduction returned the wrong exact graph",
            ));
        }
        let successor_candidate_beta = exact_beta(
            &mut proof,
            plan.graph.successor_candidate,
            plan.graph.predicate,
            plan.graph.successor_candidate_instance,
            plan.graph.closed_to_successor,
            "natlike-successor-candidate-beta",
        )?;
        let successor_candidate_reverse = proof
            .conversion_symmetry(&successor_candidate_beta)
            .map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-candidate-beta", error)
            })?;
        let successor_instance = proof
            .convert_theorem(&closed_to_successor, &successor_candidate_reverse)
            .map_err(|error| {
                SignedHolRoundTripError::at("natlike-successor-candidate-beta", error)
            })?;
        let successor_universal = plan
            .successor_all_introduction
            .apply(&mut proof, &successor_instance)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-inner-all", error))?;
        if successor_universal.conclusion() != plan.graph.successor_universal {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-successor-inner-all",
                "inner universal introduction returned the wrong exact graph",
            ));
        }
        let natlike_successor_beta = exact_beta(
            &mut proof,
            plan.graph.natlike,
            plan.graph.successor_point,
            plan.graph.natlike_successor,
            plan.graph.successor_universal,
            "natlike-successor-result-beta",
        )?;
        let natlike_successor_reverse = proof
            .conversion_symmetry(&natlike_successor_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-result-beta", error))?;
        let natlike_successor = proof
            .convert_theorem(&successor_universal, &natlike_successor_reverse)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-result-beta", error))?;
        let outer_implication = plan
            .outer_implication
            .apply(&mut proof, &natlike_successor)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-outer-imp", error))?;
        if outer_implication.conclusion() != plan.graph.outer_implication {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-successor-outer-imp",
                "outer implication introduction returned the wrong exact graph",
            ));
        }
        let outer_beta = exact_beta(
            &mut proof,
            plan.graph.outer_predicate,
            plan.graph.point,
            plan.graph.outer_instance,
            plan.graph.outer_implication,
            "natlike-successor-outer-beta",
        )?;
        let outer_reverse = proof
            .conversion_symmetry(&outer_beta)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-outer-beta", error))?;
        let outer_instance = proof
            .convert_theorem(&outer_implication, &outer_reverse)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-outer-beta", error))?;
        let conclusion = plan
            .outer_all_introduction
            .apply(&mut proof, &outer_instance)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-outer-all", error))?;
        if conclusion.conclusion() != plan.graph.conclusion {
            return Err(SignedHolRoundTripError::invalid(
                "natlike-successor-outer-all",
                "outer universal introduction returned the wrong exact graph",
            ));
        }
        proof
            .persist_theorem(&conclusion)
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-persisted", error))
    })
}

/// Signed extension proving that `NatLike` is closed under the selected successor.
pub struct SignedNatLikeSuccessor {
    artifact: SignedHolArtifact,
    natlike_namespace: NamespaceId,
    context: ContextId,
    inherited_infinity: TermId,
    inherited_nonsurjective: TermId,
    inherited_zero: TermId,
    conclusion: TermId,
}

impl SignedNatLikeSuccessor {
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
    /// Returns the inherited nonsurjectivity theorem.
    #[must_use]
    pub const fn inherited_nonsurjective(&self) -> TermId {
        self.inherited_nonsurjective
    }
    /// Returns the inherited `NatLike zero` theorem.
    #[must_use]
    pub const fn inherited_zero(&self) -> TermId {
        self.inherited_zero
    }
    /// Returns exact universal successor closure.
    #[must_use]
    pub const fn conclusion(&self) -> TermId {
        self.conclusion
    }
    /// Returns the authority-safe artifact label.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-natlike-successor"
    }
    /// Renders an authority-safe sidecar for the exact signed state.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "authority=kernel-derived-theorem\ntheorem=nat-like-successor-closure\nproof-dependencies=positive-hol-rules-and-predicate-natlike-definition\ninherited-theorems-used=none\nsignature-scope=exact-database-bytes\nsignature-meaning=authentication-not-proof\n{}",
            self.artifact.attestation_text()
        )
    }
}

fn verify_source_judgements(
    connection: &mut Connection<Hol<AllowAll>>,
    context: ContextId,
    conclusions: [TermId; 3],
) -> Result<(), SignedHolRoundTripError> {
    connection.with_proof_session(|mut proof| {
        for conclusion in conclusions {
            if proof
                .load_theorem(context, conclusion)
                .map_err(|error| {
                    SignedHolRoundTripError::at("natlike-successor-source-loaded", error)
                })?
                .is_none()
            {
                return Err(SignedHolRoundTripError::invalid(
                    "natlike-successor-source-loaded",
                    "an exact inherited judgement is absent",
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
        .create_namespace(None, Some("natlike-successor-v1"))
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-exported", error))?;
    for (slot, value, name) in [
        (0, NamespaceExport::Context(context), "empty-context"),
        (
            1,
            NamespaceExport::Term(conclusion),
            "nat-like-successor-closure",
        ),
    ] {
        connection
            .export_value(namespace, ExportId::from_i64(slot), value, Some(name))
            .map_err(|error| SignedHolRoundTripError::at("natlike-successor-exported", error))?;
    }
    Ok(namespace)
}

fn verify_raw_profile(
    raw: &covalence_neutron::Connection,
    namespace: NamespaceId,
    context: ContextId,
    inherited: [TermId; 3],
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
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?;
    if namespace_profile != ("natlike-successor-v1".to_owned(), None, None, None) {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-profile-checked",
            "derived namespace differs from the exact local profile",
        ));
    }
    let mut exports = connection
        .prepare("SELECT export_id, sort, local_id, name FROM hol_namespace_export WHERE namespace_id = ?1 ORDER BY export_id")
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?;
    let actual_exports = exports
        .query_map([namespace.get()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, String>(3)?,
            ))
        })
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?;
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
            "nat-like-successor-closure".to_owned(),
        ),
    ];
    if actual_exports != expected_exports {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-profile-checked",
            "derived exports differ from the exact slot/sort/name/value profile",
        ));
    }
    let mut rows = connection
        .prepare("SELECT ctx_id, term_id FROM hol_judgement ORDER BY ctx_id, term_id")
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?;
    let actual = rows
        .query_map([], |row| Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?)))
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?
        .collect::<Result<Vec<_>, sqlite::Error>>()
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-profile-checked", error))?;
    let mut expected = inherited
        .into_iter()
        .chain([conclusion])
        .map(|term| (context.get(), term.get()))
        .collect::<Vec<_>>();
    expected.sort_unstable();
    if actual != expected {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-profile-checked",
            "state must contain exactly the three inherited rows and successor closure",
        ));
    }
    Ok(())
}

fn verify_complete_image_profile(
    validated: &ValidatedHolImage,
) -> Result<(), SignedHolRoundTripError> {
    let expected = HolImageCounts {
        nodes: 602,
        contexts: 7,
        members: 8,
        untrusted_judgement_rows: 4,
        untrusted_context_implication_rows: 0,
        context_exact_unions: 0,
        namespaces: 6,
        namespace_exports: 23,
        import_references: 4,
        imported_namespaces: 0,
        untrusted_trusted_import_rows: 4,
    };
    if validated.counts() != expected {
        return Err(SignedHolRoundTripError::at(
            "natlike-successor-image-validated",
            format_args!(
                "complete-state profile differs: actual {:?}, expected {:?}",
                validated.counts(),
                expected
            ),
        ));
    }
    Ok(())
}

/// Derives, persists, exports, and signs exact successor closure for `NatLike`.
///
/// # Errors
///
/// Returns the first source, proof, persistence, export, validation, or signing error.
pub fn produce_signed_natlike_successor(
    producer: &Kernel,
) -> Result<SignedNatLikeSuccessor, SignedHolRoundTripError> {
    let source_artifact = produce_signed_natlike_zero(producer)?;
    let mut staging = Repl::new(producer.verifying_key().as_bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-staging-opened", error))?;
    let (owner, retained) = retain_signed_natlike_zero(producer, &mut staging, &source_artifact)?;
    let mut connection =
        prepare_retained_trusted_hol_state(&mut staging, owner, &retained, AllowAll).map_err(
            |error| SignedHolRoundTripError::at("natlike-successor-source-opened", error),
        )?;
    let context = source_artifact.context();
    let inherited = [
        source_artifact.inherited_infinity(),
        source_artifact.inherited_nonsurjective(),
        source_artifact.conclusion(),
    ];
    let source_namespace = NamespaceId::from_i64(source_artifact.artifact().namespace_id());
    let NamespaceExport::Term(exported_zero) =
        named_export(&mut connection, source_namespace, "nat-like-zero")?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "prior NatLike-zero export has the wrong sort",
        ));
    };
    if exported_zero != source_artifact.conclusion() {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-source-resolved",
            "prior NatLike-zero theorem differs from its exact export",
        ));
    }
    verify_source_judgements(&mut connection, context, inherited)?;
    let source = resolve_source(
        &mut connection,
        source_artifact.natlike_namespace(),
        context,
        source_artifact.inherited_infinity(),
    )?;
    let plan = prepare_proof(&mut connection, context, source)?;
    verify_exact_target(&mut connection, source.ind, &plan.graph)?;
    derive(&mut connection, &plan)?;
    let namespace = export_namespace(&mut connection, context, plan.graph.conclusion)?;
    let snapshot = producer
        .export_hol(&mut connection)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-signed", error))?;
    let raw = covalence_neutron::Connection::deserialize(
        &covalence_neutron::Bytes::copy_from_slice(snapshot.image().bytes()),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-successor-image-copied", error))?;
    verify_raw_profile(&raw, namespace, context, inherited, plan.graph.conclusion)?;
    let validated = ValidatedHolImage::validate(snapshot.image().bytes())
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-image-validated", error))?;
    verify_complete_image_profile(&validated)?;
    let attestation = snapshot.attestation();
    Ok(SignedNatLikeSuccessor {
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
        inherited_infinity: inherited[0],
        inherited_nonsurjective: inherited[1],
        inherited_zero: inherited[2],
        conclusion: plan.graph.conclusion,
    })
}

/// Authenticates and retains one already-produced signed successor-closure derivation.
///
/// # Errors
///
/// Returns the first authentication, trust, import, receiver, or directory error.
pub fn retain_signed_natlike_successor(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
    artifact: &SignedNatLikeSuccessor,
) -> Result<(ConnectionId, RetainedReceivedHolSnapshot), SignedHolRoundTripError> {
    let expected = directory
        .expected_kernel_identity(KernelId::LOCAL)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-signer-selected", error))?;
    let independent = ExpectedKernelIdentity::from_public_key(
        KernelId::LOCAL,
        producer.verifying_key().as_bytes(),
    )
    .map_err(|error| SignedHolRoundTripError::at("natlike-successor-signer-selected", error))?;
    if expected != independent {
        return Err(SignedHolRoundTripError::invalid(
            "natlike-successor-signer-selected",
            "REPL local endpoint key differs from the successor-closure signer",
        ));
    }
    let pinned = authenticate_pinned_signed_hol_artifact(&expected, artifact.artifact())?;
    let receiver = producer
        .open_hol(AllowAll)
        .map_err(|error| SignedHolRoundTripError::at("natlike-successor-receiver-opened", error))?;
    trust_receive_and_retain_bounded_selected_managed_hol_artifact(
        directory,
        receiver,
        pinned,
        i64::MAX,
    )
}

/// Produces and retains the signed successor-closure derivation in a fresh receiver.
///
/// # Errors
///
/// Returns the first producer, authentication, trust, import, or directory error.
pub fn produce_and_retain_signed_natlike_successor(
    producer: &Kernel,
    directory: &mut Repl<LocalConnection>,
) -> Result<
    (
        SignedNatLikeSuccessor,
        ConnectionId,
        RetainedReceivedHolSnapshot,
    ),
    SignedHolRoundTripError,
> {
    let artifact = produce_signed_natlike_successor(producer)?;
    let (owner, retained) = retain_signed_natlike_successor(producer, directory, &artifact)?;
    Ok((artifact, owner, retained))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::open_retained_trusted_hol_as_managed_state;

    #[test]
    fn derives_signs_receives_and_reopens_exact_successor_closure() {
        let kernel = Kernel::ephemeral();
        let mut directory = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let (artifact, owner, retained) =
            produce_and_retain_signed_natlike_successor(&kernel, &mut directory).unwrap();
        assert_eq!(artifact.kind(), "signed-natlike-successor");
        assert!(
            artifact
                .attestation_text()
                .contains("inherited-theorems-used=none")
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
        for conclusion in [
            artifact.inherited_infinity(),
            artifact.inherited_nonsurjective(),
            artifact.inherited_zero(),
            artifact.conclusion(),
        ] {
            assert!(
                child
                    .with_proof_session(|mut proof| proof
                        .load_theorem(artifact.context(), conclusion)
                        .map(|theorem| theorem.is_some()))
                    .unwrap()
            );
        }
        let validated = ValidatedHolImage::validate(artifact.artifact().image()).unwrap();
        assert_eq!(validated.counts().untrusted_judgement_rows, 4);
        assert_eq!(validated.counts().contexts, 7);
        assert_eq!(validated.counts().members, 8);
    }

    #[test]
    fn derivation_is_independent_of_every_inherited_theorem_handle() {
        let mut connection = Connection::open_hol_in_memory(AllowAll).unwrap();
        let ind = connection.insert_base_type(0x53_55_43).unwrap();
        let bound = connection.insert_bound_term(0, ind).unwrap();
        let successor = connection.insert_lambda(ind, bound).unwrap();
        let syntax = crate::build_natlike_syntax(&mut connection, ind, successor).unwrap();
        let source = SourceSyntax {
            ind,
            successor,
            zero: syntax.zero(),
            successor_closed: syntax.successor_closed(),
            natlike: syntax.natlike(),
        };
        let plan = prepare_proof(&mut connection, ContextId::empty(), source).unwrap();
        verify_exact_target(&mut connection, ind, &plan.graph).unwrap();
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
        let mut artifact = produce_signed_natlike_successor(&producer).unwrap();
        artifact.artifact.image[0] ^= 1;
        let mut directory = Repl::new(producer.verifying_key().as_bytes()).unwrap();
        assert!(retain_signed_natlike_successor(&producer, &mut directory, &artifact).is_err());
        assert!(directory.connections().unwrap().is_empty());
        assert_eq!(directory.active().unwrap(), None);

        let artifact = produce_signed_natlike_successor(&producer).unwrap();
        let other = Kernel::ephemeral();
        let mut wrong_directory = Repl::new(other.verifying_key().as_bytes()).unwrap();
        assert!(
            retain_signed_natlike_successor(&producer, &mut wrong_directory, &artifact).is_err()
        );
        assert!(wrong_directory.connections().unwrap().is_empty());
        assert_eq!(wrong_directory.active().unwrap(), None);
    }
}
