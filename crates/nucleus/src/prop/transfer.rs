//! Signed export and checked import of propositional databases.

use covalence_lib_error::snafu::ResultExt;
use covalence_lib_hash::O256;
use covalence_neutron::sql::{Param, Transaction};

use super::{
    BoundNotFreeSnafu, ImageSnafu, ImportInvalidSnafu, Operation, Policy, Prop, PropError, PropId,
    SchemaMismatchSnafu, SignSnafu, SnapshotSnafu, StorageSnafu, UntrustedSignerSnafu,
    prop_schema_id,
};
use crate::snapshot::{SignedSnapshotEnvelope, schema_valid_snapshot_statement};
use crate::{Connection, Ed25519Signer, Signer as _};

/// The private schema name used while admitting an import.
const IMPORT_SCHEMA: &str = "prop_source_import";

/// The id translation for one admitted import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PropImportMap {
    /// The `prop_import` provenance row naming this admission.
    pub import_id: i64,
    /// The positive id offset applied to unbound foreign propositions.
    pub offset: i64,
    /// Foreign-to-local variable bindings applied by this admission.
    pub bindings: std::collections::BTreeMap<i64, i64>,
}

impl PropImportMap {
    /// Maps a foreign proposition id to its local id.
    ///
    /// # Panics
    ///
    /// Never in practice: offsets and bindings keep ids positive.
    #[must_use]
    pub fn local(&self, foreign: PropId) -> PropId {
        let raw = self
            .bindings
            .get(&foreign.get())
            .copied()
            .unwrap_or(foreign.get() + self.offset);
        PropId::new(raw).expect("mapped ids are positive")
    }

    /// Maps a foreign literal to its local literal.
    ///
    /// # Panics
    ///
    /// Never in practice: mapped literals stay nonzero.
    #[must_use]
    pub fn local_lit(&self, foreign: super::Lit) -> super::Lit {
        let mapped = self.local(foreign.proposition()).get();
        let value = if foreign.get() > 0 { mapped } else { -mapped };
        super::Lit::new(value).expect("mapped literals are nonzero")
    }
}

impl<P: Policy> Connection<Prop<P>> {
    /// Serializes, hashes, and signs this database with its schema.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses exports, serialization fails, or the
    /// kernel cannot sign.
    pub fn export_signed(
        &self,
        signer: &Ed25519Signer,
    ) -> Result<SignedSnapshotEnvelope, PropError> {
        self.view().authorize(Operation::Export)?;
        let bytes = self.parts().0.serialize().context(ImageSnafu)?;
        let image = O256::from_bytes(&bytes);
        let schema = self.schema_id()?;
        let statement = schema_valid_snapshot_statement(schema, image);
        let signature = signer.sign(signer.key_id(), statement).context(SignSnafu)?;
        Ok(SignedSnapshotEnvelope::new(
            &bytes,
            schema,
            image,
            signer.key_id(),
            signer.verifying_key().to_bytes(),
            &signature,
        ))
    }

    /// Adds a signer to this connection-local trusted set.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses trust changes.
    pub fn trust_signer(&self, signer: O256) -> Result<(), PropError> {
        self.view().authorize(Operation::TrustSigner)?;
        self.protocol().trusted.borrow_mut().insert(signer);
        Ok(())
    }

    /// Whether a signer is in this connection's trusted set.
    #[must_use]
    pub fn signer_is_trusted(&self, signer: O256) -> bool {
        self.protocol().trusted.borrow().contains(&signer)
    }

    /// Verifies and admits an envelope's database.
    ///
    /// # Errors
    ///
    /// Fails — admitting nothing — when authentication fails, the signer
    /// is untrusted, the schema claim or attached manifest is not this
    /// protocol's schema, or the source fails its own validity
    /// assertions.
    pub fn import_signed(
        &mut self,
        envelope: SignedSnapshotEnvelope,
        meaning: &str,
    ) -> Result<PropImportMap, PropError> {
        self.import_signed_bound(envelope, meaning, &[])
    }

    /// [`Self::import_signed`] with variable bindings: each `(foreign,
    /// local)` pair identifies a source variable with a local
    /// proposition instead of a fresh offset id.
    ///
    /// Binding is universal instantiation of the source's free
    /// variables, so it is sound for **any** local target — the gate is
    /// entirely on the foreign side, which must be genuinely free in the
    /// source (no definition, no theory binding). Non-injective maps are
    /// diagonal specializations and are permitted.
    ///
    /// # Errors
    ///
    /// As [`Self::import_signed`], plus a bound foreign id that is
    /// defined or theory-bound in the source.
    pub fn import_signed_bound(
        &mut self,
        envelope: SignedSnapshotEnvelope,
        meaning: &str,
        bindings: &[(PropId, PropId)],
    ) -> Result<PropImportMap, PropError> {
        self.view().authorize(Operation::ImportTable)?;
        let snapshot = envelope.authenticate().context(SnapshotSnafu)?;
        let expected = self.schema_id()?;
        if snapshot.schema() != expected {
            return SchemaMismatchSnafu {
                claimed: snapshot.schema(),
                expected,
            }
            .fail();
        }
        if !self.signer_is_trusted(snapshot.signer()) {
            return UntrustedSignerSnafu {
                signer: snapshot.signer(),
            }
            .fail();
        }
        let bytes = covalence_neutron::Bytes::copy_from_slice(snapshot.bytes());
        self.parts_mut()
            .0
            .attach_deserialized(IMPORT_SCHEMA, &bytes)
            .context(ImageSnafu)?;
        let admitted = self.admit_attached(meaning, bindings);
        let _ = self
            .parts()
            .0
            .execute_batch(&format!("DETACH DATABASE \"{IMPORT_SCHEMA}\""));
        admitted
    }

    /// Verifies and copies the attached source, assuming it is already
    /// authenticated and trusted.
    fn admit_attached(
        &mut self,
        meaning: &str,
        bindings: &[(PropId, PropId)],
    ) -> Result<PropImportMap, PropError> {
        self.verify_attached_source(bindings)?;
        let storage = self.parts().0;
        let offset = storage
            .query_row(
                "SELECT COALESCE(MAX(MAX(abs(lhs), abs(rhs))), 0) FROM prop_row",
                &[],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(super::missing_result_row)
            .context(StorageSnafu)?;
        let import_id = storage
            .query_row(
                "INSERT INTO prop_import(meaning) VALUES (?1) RETURNING import_id",
                &[Param::Text(meaning)],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(super::missing_result_row)
            .context(StorageSnafu)?;
        install_binding_table(storage, bindings)?;
        admit_translated_rows(storage, offset, import_id)?;
        let _ = storage.execute_batch("DROP TABLE IF EXISTS temp.prop_import_binding");
        Ok(PropImportMap {
            import_id,
            offset,
            bindings: bindings
                .iter()
                .map(|(foreign, local)| (foreign.get(), local.get()))
                .collect(),
        })
    }

    /// Confirms the attached schema matches this protocol's identity,
    /// the source satisfies its own W1-W4, and every bound foreign id is
    /// genuinely free in the source (no definitional conjuncts, no
    /// theory binding).
    fn verify_attached_source(&self, bindings: &[(PropId, PropId)]) -> Result<(), PropError> {
        let storage = self.parts().0;
        let attached_manifest =
            crate::manifest::schema_manifest_id_in(storage, IMPORT_SCHEMA).context(StorageSnafu)?;
        let expected_from_attached = prop_schema_id(attached_manifest);
        let expected = self.schema_id()?;
        if expected_from_attached != expected {
            return SchemaMismatchSnafu {
                claimed: expected_from_attached,
                expected,
            }
            .fail();
        }
        let violations = self.view().check_validity_in(IMPORT_SCHEMA)?;
        if !violations.is_empty() {
            return ImportInvalidSnafu { violations }.fail();
        }
        for (foreign, _) in bindings {
            let constrained = storage
                .query_row(
                    &format!(
                        "SELECT lhs FROM \"{IMPORT_SCHEMA}\".prop_row
                     WHERE lhs = ?1 AND model >= 0
                       AND (rhs != 0 OR model > 0)
                     LIMIT 1"
                    ),
                    &[Param::Integer(foreign.get())],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)?;
            if constrained.is_some() {
                return BoundNotFreeSnafu {
                    foreign: foreign.get(),
                }
                .fail();
            }
        }
        Ok(())
    }
}

/// Installs the temp binding table `install_binding_table` and
/// `admit_translated_rows` share.
fn install_binding_table(
    storage: &covalence_neutron::Connection,
    bindings: &[(PropId, PropId)],
) -> Result<(), PropError> {
    storage
        .execute_batch(
            "DROP TABLE IF EXISTS temp.prop_import_binding;
             CREATE TEMP TABLE prop_import_binding (
                 foreign_id INTEGER PRIMARY KEY,
                 local_id   INTEGER NOT NULL
             ) STRICT;",
        )
        .context(StorageSnafu)?;
    for (foreign, local) in bindings {
        storage
            .execute(
                "INSERT OR REPLACE INTO temp.prop_import_binding(foreign_id, local_id)
                 VALUES (?1, ?2)",
                &[Param::Integer(foreign.get()), Param::Integer(local.get())],
            )
            .context(StorageSnafu)?;
    }
    Ok(())
}

/// Copies the attached source's definitional and universal layers into
/// the main table, translating every id through the installed bindings
/// (falling back to `offset`) and re-scoping universal rows to
/// `-import_id`. Theory declarations and world rows are deliberately
/// dropped: forgetting a constraint never strengthens the universal
/// layer, and declaration rows of bound variables are skipped since the
/// local side already governs them.
fn admit_translated_rows(
    storage: &covalence_neutron::Connection,
    offset: i64,
    import_id: i64,
) -> Result<(), PropError> {
    let translate = |column: &str| {
        format!(
            "CASE WHEN {column} = 0 THEN 0 ELSE
                 (CASE WHEN {column} > 0 THEN 1 ELSE -1 END) *
                 COALESCE(
                     (SELECT local_id FROM temp.prop_import_binding
                      WHERE foreign_id = abs({column})),
                     abs({column}) + ?1
                 )
             END"
        )
    };
    let admit_definitional = format!(
        "INSERT INTO prop_row(lhs, rhs, model)
         SELECT {lhs}, {rhs}, 0 FROM \"{IMPORT_SCHEMA}\".prop_row
         WHERE model = 0
           AND NOT (rhs = 0 AND lhs IN
               (SELECT foreign_id FROM temp.prop_import_binding))",
        lhs = translate("lhs"),
        rhs = translate("rhs"),
    );
    let admit_universal = format!(
        "INSERT INTO prop_row(lhs, rhs, model)
         SELECT {lhs}, {rhs}, ?2 FROM \"{IMPORT_SCHEMA}\".prop_row
         WHERE model < 0
         ON CONFLICT(lhs, rhs) DO UPDATE SET model = CASE
             WHEN excluded.model <= 0 AND prop_row.model > 0
             THEN excluded.model
             ELSE prop_row.model
         END",
        lhs = translate("lhs"),
        rhs = translate("rhs"),
    );
    let transaction = Transaction::begin(storage).context(StorageSnafu)?;
    transaction
        .connection()
        .execute(&admit_definitional, &[Param::Integer(offset)])
        .context(StorageSnafu)?;
    transaction
        .connection()
        .execute(
            &admit_universal,
            &[Param::Integer(offset), Param::Integer(-import_id)],
        )
        .context(StorageSnafu)?;
    transaction.commit().context(StorageSnafu)
}

#[cfg(test)]
mod tests {
    use covalence_lib_crypto::ed25519::SigningKey;

    use super::super::{AllowAll, Ant, Lit, PropError, PropId, Target, lrat};
    use super::*;
    use crate::Prop;

    fn prop(value: i64) -> PropId {
        PropId::new(value).expect("positive id")
    }

    fn lit(value: i64) -> Lit {
        Lit::new(value).expect("nonzero literal")
    }

    fn signer(seed: u8) -> Ed25519Signer {
        Ed25519Signer::new(SigningKey::from_bytes(&[seed; 32]))
    }

    /// Builds the pigeonhole-3 formula (variables 1..=6, clause
    /// negations 7..=15, formula 16) and certifies its refutation.
    fn certified_php3() -> Connection<Prop<AllowAll>> {
        let connection = Connection::open_prop_in_memory(AllowAll).expect("open");
        let view = connection.view();
        let clauses: [&[i64]; 9] = [
            &[1, 2],
            &[3, 4],
            &[5, 6],
            &[-1, -3],
            &[-1, -5],
            &[-3, -5],
            &[-2, -4],
            &[-2, -6],
            &[-4, -6],
        ];
        for variable in 1..=6 {
            view.declare_free(prop(variable)).expect("declare");
        }
        for (index, clause) in clauses.iter().enumerate() {
            let negated: Vec<Lit> = clause.iter().map(|l| lit(-l)).collect();
            let id = 7 + i64::try_from(index).expect("clause index");
            view.define(prop(id), &negated).expect("clause");
        }
        let conjuncts: Vec<Lit> = (7..=15).map(|id| lit(-id)).collect();
        view.define(prop(16), &conjuncts).expect("formula");
        let proof = "10 -2 0 7 8 2 3 6 0\n11 1 0 10 1 0\n12 -3 0 11 4 0\n\
                     13 -5 0 11 5 0\n14 4 0 12 2 0\n15 6 0 13 3 0\n16 0 14 15 9 0\n";
        let instructions = lrat::parse_text(proof).expect("parse");
        let clause_ids: Vec<PropId> = (7..=15).map(prop).collect();
        view.lrat_refutation(prop(16), &clause_ids, &instructions, -1)
            .expect("refutation");
        assert!(view.unsat(lit(16)).expect("unsat"));
        connection
    }

    #[test]
    fn signed_export_import_round_trip() {
        // Kernel one proves; kernel two must reject before trust, then
        // admit and reason with the imported fact.
        let source = certified_php3();
        let kernel_one = signer(1);

        let mut receiver = Connection::open_prop_in_memory(AllowAll).expect("open receiver");
        // Local state first, so the import offset is nontrivial.
        receiver
            .view()
            .declare_free(prop(1))
            .expect("local declare");

        let untrusted = source.export_signed(&kernel_one).expect("export");
        assert!(matches!(
            receiver.import_signed(untrusted, "php3 before trust"),
            Err(PropError::UntrustedSigner { .. })
        ));

        receiver.trust_signer(kernel_one.key_id()).expect("trust");
        let envelope = source.export_signed(&kernel_one).expect("export again");
        let map = receiver
            .import_signed(envelope, "php3 from kernel one")
            .expect("import");
        assert!(map.offset >= 1);

        // The imported refutation is usable state: reason with it.
        let view = receiver.view();
        let formula = map.local(prop(16));
        assert!(
            view.implies(Ant::from(formula.lit()), formula.negated())
                .expect("fact")
        );
        view.refl(Target::Universal(-2), formula.negated())
            .expect("refl");
        view.cases(Target::Universal(-2), formula.lit(), formula.negated())
            .expect("cases");
        assert!(view.tautology(formula.negated()).expect("tautology"));
        assert!(view.unsat(formula.lit()).expect("unsat"));
        assert!(view.check_validity().expect("validity").is_empty());

        // Provenance: the admitted universal rows name the import.
        let meaning = receiver
            .parts()
            .0
            .query_row(
                "SELECT i.meaning FROM prop_row r JOIN prop_import i
                 ON r.model = -i.import_id
                 WHERE r.lhs = ?1 AND r.rhs = ?2",
                &[
                    Param::Integer(formula.get()),
                    Param::Integer(-formula.get()),
                ],
                |row| row.text(0),
            )
            .expect("provenance")
            .expect("provenance row");
        assert_eq!(meaning, "php3 from kernel one");
    }

    #[test]
    fn bound_import_composes_two_independent_provers() {
        // The multi-kernel shape: two independent kernels each prove a
        // universal fact about "their" variable 1, which is bound on
        // import to a shared local atom. Neither kernel's proof alone
        // gives the combined conclusion.
        let kernel_a = signer(3);
        let source_a = Connection::open_prop_in_memory(AllowAll).expect("open a");
        {
            let view = source_a.view();
            view.declare_free(prop(1)).expect("declare a.1");
            // a.1 => a.1 (trivial, but exercises the pipeline); the real
            // content is that a.1 is genuinely free, hence bindable.
            view.refl(Target::Universal(-1), lit(1)).expect("refl a");
        }

        let kernel_b = signer(4);
        let source_b = Connection::open_prop_in_memory(AllowAll).expect("open b");
        {
            let view = source_b.view();
            view.declare_free(prop(1)).expect("declare b.1");
            view.refl(Target::Universal(-1), lit(-1)).expect("refl b");
        }

        let mut hub = Connection::open_prop_in_memory(AllowAll).expect("open hub");
        hub.view().declare_free(prop(1)).expect("shared atom");
        hub.trust_signer(kernel_a.key_id()).expect("trust a");
        hub.trust_signer(kernel_b.key_id()).expect("trust b");

        let envelope_a = source_a.export_signed(&kernel_a).expect("export a");
        let map_a = hub
            .import_signed_bound(envelope_a, "from kernel a", &[(prop(1), prop(1))])
            .expect("import a");
        assert!(map_a.bindings.contains_key(&1));

        let envelope_b = source_b.export_signed(&kernel_b).expect("export b");
        let map_b = hub
            .import_signed_bound(envelope_b, "from kernel b", &[(prop(1), prop(1))])
            .expect("import b");
        assert_eq!(map_b.local(prop(1)), prop(1));

        // Both facts now share the same local atom: combine them.
        let view = hub.view();
        assert!(view.implies(Ant::from(lit(1)), lit(1)).expect("a's fact"));
        assert!(view.implies(Ant::from(lit(-1)), lit(-1)).expect("b's fact"));
        assert!(view.check_validity().expect("validity").is_empty());
    }

    #[test]
    fn binding_a_defined_foreign_id_is_rejected() {
        let kernel = signer(5);
        let source = Connection::open_prop_in_memory(AllowAll).expect("open source");
        source.view().declare_free(prop(1)).expect("declare");
        source.view().define(prop(2), &[lit(1)]).expect("define");
        let mut hub = Connection::open_prop_in_memory(AllowAll).expect("open hub");
        hub.view().declare_free(prop(9)).expect("local atom");
        hub.trust_signer(kernel.key_id()).expect("trust");
        let envelope = source.export_signed(&kernel).expect("export");
        assert!(matches!(
            hub.import_signed_bound(envelope, "bad binding", &[(prop(2), prop(9))]),
            Err(PropError::BoundNotFree { foreign: 2 })
        ));
        // Nothing was admitted on the failed binding.
        assert!(!hub.view().tautology(lit(1)).expect("no leakage"));
    }

    #[test]
    fn tampered_envelopes_and_foreign_signers_are_rejected() {
        let source = certified_php3();
        let kernel_one = signer(1);
        let kernel_two = signer(2);
        let mut receiver = Connection::open_prop_in_memory(AllowAll).expect("open receiver");
        receiver
            .trust_signer(kernel_two.key_id())
            .expect("trust other");

        // Right signer, but the receiver trusts someone else.
        let envelope = source.export_signed(&kernel_one).expect("export");
        assert!(matches!(
            receiver.import_signed(envelope, "wrong trust"),
            Err(PropError::UntrustedSigner { .. })
        ));

        // Tampered bytes fail authentication before anything else.
        let honest = source.export_signed(&kernel_one).expect("export");
        let claim = honest.authenticate().expect("authenticate").into_claim();
        let forged = SignedSnapshotEnvelope::new(
            b"not the database",
            claim.schema(),
            claim.image(),
            claim.signer(),
            *claim.public_key(),
            claim.signature(),
        );
        receiver.trust_signer(kernel_one.key_id()).expect("trust");
        assert!(matches!(
            receiver.import_signed(forged, "forged"),
            Err(PropError::Snapshot { .. })
        ));
    }
}
