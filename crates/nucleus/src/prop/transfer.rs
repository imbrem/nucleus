//! Signed export and trusted import of propositional databases.
//!
//! Export serializes the connection's main database, hashes the exact
//! bytes, and signs the schema-qualified `(schema_o256, image_o256)`
//! statement with the kernel's identity — the same envelope family the
//! snapshot layer defines. Import is the trust chain run in order:
//! authenticate the envelope (signature over the exact claim), require
//! the signer in this connection's trusted set (reject-before-trust),
//! attach the bytes privately, verify the attached schema manifest
//! matches the claim, check the source's own W1-W4 validity, and only
//! then admit rows — definitional layer verbatim and universal facts
//! under this import's provenance — through an id offset that maps every
//! foreign proposition above everything local (so define-once, level
//! uniqueness, and acyclicity are preserved by construction). World rows
//! and theory bindings do not transfer: dropping a binding only forgets
//! a constraint, which cannot strengthen the imported universal layer.
//!
//! Everything here is LCF-style calls on the connection — no recipe or
//! replay layer; the import itself is one checked admission rule.

use covalence_lib_error::snafu::ResultExt;
use covalence_lib_hash::O256;
use covalence_neutron::sql::{Param, Transaction};

use super::{
    ImageSnafu, ImportInvalidSnafu, Operation, Policy, Prop, PropError, PropId,
    SchemaMismatchSnafu, SignSnafu, SnapshotSnafu, StorageSnafu, UntrustedSignerSnafu,
    prop_schema_id,
};
use crate::snapshot::{SignedSnapshotEnvelope, schema_valid_snapshot_statement};
use crate::{Connection, Ed25519Signer, Signer as _};

/// The private schema name used while admitting an import.
const IMPORT_SCHEMA: &str = "prop_source_import";

/// The id translation for one admitted import: local = foreign + offset
/// (negated for negative literals).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PropImportMap {
    /// The `prop_import` provenance row naming this admission.
    pub import_id: i64,
    /// The positive id offset applied to every foreign proposition.
    pub offset: i64,
}

impl PropImportMap {
    /// Maps a foreign proposition id to its local id.
    ///
    /// # Panics
    ///
    /// Never in practice: offsets keep ids positive.
    #[must_use]
    pub fn local(&self, foreign: PropId) -> PropId {
        PropId::new(foreign.get() + self.offset).expect("offset ids are positive")
    }

    /// Maps a foreign literal to its local literal.
    ///
    /// # Panics
    ///
    /// Never in practice: offsets keep literals nonzero.
    #[must_use]
    pub fn local_lit(&self, foreign: super::Lit) -> super::Lit {
        let value = foreign.get();
        let shifted = if value > 0 {
            value + self.offset
        } else {
            value - self.offset
        };
        super::Lit::new(shifted).expect("offset literals are nonzero")
    }
}

impl<P: Policy> Connection<Prop<P>> {
    /// Serializes, hashes, and signs this connection's database as a
    /// schema-qualified envelope under `signer`'s identity.
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

    /// Adds a signer to this connection's trusted set.
    ///
    /// Trust is connection-local and never serialized: receiving a
    /// database that trusted a signer does not make this connection
    /// trust it.
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

    /// Runs the import trust chain and admits the envelope's database.
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
        let admitted = self.admit_attached(meaning);
        let _ = self
            .parts()
            .0
            .execute_batch(&format!("DETACH DATABASE \"{IMPORT_SCHEMA}\""));
        admitted
    }

    /// Verifies and copies the attached source, assuming it is already
    /// authenticated and trusted.
    fn admit_attached(&mut self, meaning: &str) -> Result<PropImportMap, PropError> {
        // The signed claim covered the whole image; confirm the attached
        // bytes carry exactly this protocol's physical schema.
        let attached_manifest =
            crate::manifest::schema_manifest_id_in(self.parts().0, IMPORT_SCHEMA)
                .context(StorageSnafu)?;
        let expected = prop_schema_id(attached_manifest);
        if expected != self.schema_id()? {
            return SchemaMismatchSnafu {
                claimed: expected,
                expected: self.schema_id()?,
            }
            .fail();
        }
        // The source must satisfy its own decidable well-formedness.
        let violations = self.view().check_validity_in(IMPORT_SCHEMA)?;
        if !violations.is_empty() {
            return ImportInvalidSnafu { violations }.fail();
        }
        let storage = self.parts().0;
        let offset = storage
            .query_row(
                "SELECT COALESCE(MAX(MAX(abs(lhs), abs(rhs))), 0) FROM prop_row",
                &[],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(super::missing_result_row)?;
        let import_id = storage
            .query_row(
                "INSERT INTO prop_import(meaning) VALUES (?1) RETURNING import_id",
                &[Param::Text(meaning)],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(super::missing_result_row)?;
        // Admit the definitional layer (definitions and free-variable
        // declarations) verbatim under the offset, then the universal
        // layer under this import's provenance. Theory declarations and
        // world rows are deliberately dropped: forgetting a constraint
        // never strengthens the universal layer.
        let shift = |column: &str| {
            format!(
                "CASE WHEN {column} > 0 THEN {column} + ?1
                      WHEN {column} < 0 THEN {column} - ?1
                      ELSE 0 END"
            )
        };
        let admit_definitional = format!(
            "INSERT INTO prop_row(lhs, rhs, model)
             SELECT {lhs}, {rhs}, 0 FROM \"{IMPORT_SCHEMA}\".prop_row
             WHERE model = 0",
            lhs = shift("lhs"),
            rhs = shift("rhs"),
        );
        let admit_universal = format!(
            "INSERT INTO prop_row(lhs, rhs, model)
             SELECT {lhs}, {rhs}, ?2 FROM \"{IMPORT_SCHEMA}\".prop_row
             WHERE model < 0
             ON CONFLICT(lhs, rhs) DO NOTHING",
            lhs = shift("lhs"),
            rhs = shift("rhs"),
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
        transaction.commit().context(StorageSnafu)?;
        Ok(PropImportMap { import_id, offset })
    }
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
