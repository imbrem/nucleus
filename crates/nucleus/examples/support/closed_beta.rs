use std::error::Error;

use covalence_nucleus::{
    AllowAll, Connection, ContextId, ExportId, Hol, NamespaceExport, NamespaceId, TermId,
};

pub struct ClosedBeta {
    pub namespace: NamespaceId,
    pub context: ContextId,
    pub conclusion: TermId,
}

/// Builds, proves, persists, and publishes the closed beta demo using only checked HOL APIs.
///
/// This driver has no filesystem, transport, kernel-key, or signing access. The host decides
/// whether to serialize and sign the resulting database after this function succeeds.
pub fn build(database: &mut Connection<Hol<AllowAll>>) -> Result<ClosedBeta, Box<dyn Error>> {
    let bool_type = database.insert_bool_type()?;
    let bound = database.insert_bound_term(0, bool_type)?;
    let identity = database.insert_lambda(bool_type, bound)?;
    let truth = database.insert_bool_term(true)?;
    let context = ContextId::empty();
    let conclusion = database.with_proof_session(|mut proof| {
        let theorem = proof.prove_beta(context, identity, truth)?;
        let conclusion = theorem.conclusion();
        proof.persist_theorem(&theorem)?;
        Ok::<_, covalence_nucleus::ProofError>(conclusion)
    })?;

    let namespace = database.create_namespace(Some(NamespaceId::root()), Some("demo"))?;
    database.export_value(
        namespace,
        ExportId::from_i64(0),
        NamespaceExport::Term(conclusion),
        Some("identity_true_beta"),
    )?;
    database.export_value(
        namespace,
        ExportId::from_i64(1),
        NamespaceExport::Context(context),
        Some("empty_context"),
    )?;
    Ok(ClosedBeta {
        namespace,
        context,
        conclusion,
    })
}
