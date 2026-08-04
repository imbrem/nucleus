use std::error::Error;

use covalence_nucleus::{
    AllowAll, Connection, ContextId, ExportId, Hol, NamespaceExport, NamespaceId, ProofError,
    TermId,
};

pub struct SuccCongruence {
    pub namespace: NamespaceId,
    pub context: ContextId,
    pub conclusion: TermId,
}

/// Proves and publishes `x = y |- succ x = succ y` through checked branded rules.
pub fn build(database: &mut Connection<Hol<AllowAll>>) -> Result<SuccCongruence, Box<dyn Error>> {
    let ind = database.insert_base_type(100)?;
    let ind_to_ind = database.insert_arrow_type(ind, ind)?;
    let x = database.insert_constant(200, ind)?;
    let y = database.insert_constant(201, ind)?;
    let succ = database.insert_constant(202, ind_to_ind)?;
    let x_equals_y = database.insert_equality(x, y)?;
    let context = database.define_context([x_equals_y])?;

    let succ_x = database.insert_application(succ, x)?;
    let variable = database.insert_bound_term(0, ind)?;
    let succ_variable = database.insert_application(succ, variable)?;
    let predicate_body = database.insert_equality(succ_x, succ_variable)?;
    let predicate = database.insert_lambda(ind, predicate_body)?;
    let succ_y = database.insert_application(succ, y)?;
    let expected = database.insert_equality(succ_x, succ_y)?;

    let conclusion = database.with_proof_session(|mut proof| {
        let equality = proof.prove_hypothesis(context, x_equals_y)?;
        let reflexive = proof.prove_reflexivity(context, succ_x)?;
        let beta_x = proof.conversion_beta(predicate, x)?;
        let reverse_beta_x = proof.conversion_symmetry(&beta_x)?;
        let predicate_x = proof.convert_theorem(&reflexive, &reverse_beta_x)?;
        let predicate_y = proof.equality_substitution(&equality, predicate, &predicate_x)?;
        proof.persist_theorem(&predicate_y)?;
        let beta_y = proof.conversion_beta(predicate, y)?;
        let theorem = proof.convert_theorem(&predicate_y, &beta_y)?;
        assert_eq!(theorem.conclusion(), expected);
        proof.persist_theorem(&theorem)?;
        Ok::<_, ProofError>(theorem.conclusion())
    })?;

    let namespace =
        database.create_namespace(Some(NamespaceId::root()), Some("succ-congruence"))?;
    database.export_value(
        namespace,
        ExportId::from_i64(0),
        NamespaceExport::Term(conclusion),
        Some("succ_congruence"),
    )?;
    database.export_value(
        namespace,
        ExportId::from_i64(1),
        NamespaceExport::Context(context),
        Some("x_equals_y"),
    )?;
    Ok(SuccCongruence {
        namespace,
        context,
        conclusion,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn persists_and_exports_checked_succ_congruence() {
        let mut database = Connection::open_hol_in_memory(AllowAll).unwrap();
        let proof = build(&mut database).unwrap();
        assert!(
            database
                .proved_judgement(proof.context, proof.conclusion)
                .unwrap()
        );
        let export = database
            .resolve_export(proof.namespace, ExportId::from_i64(0))
            .unwrap()
            .unwrap();
        assert_eq!(export.value, NamespaceExport::Term(proof.conclusion));
    }
}
