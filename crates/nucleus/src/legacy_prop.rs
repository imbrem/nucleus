//! Mechanical conversion from the former `(lhs, rhs, model)` representation.
//!
//! Conversion produces storage candidates, never checked facts. In particular,
//! a negative legacy `model` was arbitrary metadata, so it is not preserved as
//! a checker identity. Positive-world rows and truth antecedents have no local
//! meaning and are rejected instead of being silently reinterpreted.

use std::num::NonZeroU32;

use crate::local_prop::{AtomId, Literal, SourceId};

/// The positive reason class assigned to former universal consequences.
pub const LEGACY_UNIVERSAL_REASON: NonZeroU32 = NonZeroU32::MIN;

/// One row from the former local proposition table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LegacyRow {
    /// Former implication antecedent (`0` meant truth).
    pub lhs: i64,
    /// Former implication consequent (`0` meant a declaration).
    pub rhs: i64,
    /// Former definition/universal/world discriminator.
    pub model: i64,
}

/// A row classified for the current local proposition table.
///
/// The local source is implicit. These values are non-authoritative input to a
/// checked import; they cannot be converted into [`crate::local_prop::Fact`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MigratedRow {
    /// One conjunct in a complete, reason-zero definition group.
    Definition {
        /// Positive atom being defined.
        atom: AtomId,
        /// One signed conjunct.
        conjunct: Literal,
    },
    /// A former universal consequence, represented as a reason-one candidate.
    Theorem {
        /// Implication premise.
        premise: Literal,
        /// Implication conclusion.
        conclusion: Literal,
        /// Fixed legacy provenance class; never the old arbitrary metadata.
        reason: NonZeroU32,
    },
}

impl MigratedRow {
    /// Returns the source assigned by this local-only migration.
    #[must_use]
    pub const fn source(self) -> SourceId {
        SourceId::LOCAL
    }

    /// Returns the implication premise represented by the new row.
    #[must_use]
    pub const fn premise(self) -> Literal {
        match self {
            Self::Definition { atom, .. } => Literal::positive(atom),
            Self::Theorem { premise, .. } => premise,
        }
    }

    /// Returns the implication conclusion represented by the new row.
    #[must_use]
    pub const fn conclusion(self) -> Literal {
        match self {
            Self::Definition { conjunct, .. } => conjunct,
            Self::Theorem { conclusion, .. } => conclusion,
        }
    }

    /// Returns zero for definitions or the positive theorem reason.
    #[must_use]
    pub const fn reason(self) -> u32 {
        match self {
            Self::Definition { .. } => 0,
            Self::Theorem { reason, .. } => reason.get(),
        }
    }
}

/// Why a former row has no faithful local-table representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MigrationError {
    /// Positive models denoted possible-world evidence, which is not local fact.
    WorldRow,
    /// A truth antecedent requires a judgement absent from the local profile.
    TruthAntecedent,
    /// A zero consequent was a declaration, not a definition or theorem.
    Declaration,
    /// A literal or definition atom is outside the current public atom domain.
    InvalidLiteral,
}

impl std::fmt::Display for MigrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WorldRow => f.write_str("legacy possible-world rows are not local facts"),
            Self::TruthAntecedent => {
                f.write_str("legacy truth antecedents are unsupported by the local profile")
            }
            Self::Declaration => {
                f.write_str("legacy declarations have no proposition-row representation")
            }
            Self::InvalidLiteral => f.write_str("legacy literal is outside the local atom domain"),
        }
    }
}

impl std::error::Error for MigrationError {}

/// Classifies one former row without granting it authority.
///
/// # Errors
///
/// Rejects possible-world evidence, truth antecedents, declarations, and values
/// outside the current nonzero `u32` atom domain.
pub fn migrate_row(row: LegacyRow) -> Result<MigratedRow, MigrationError> {
    if row.model > 0 {
        return Err(MigrationError::WorldRow);
    }
    if row.lhs == 0 {
        return Err(MigrationError::TruthAntecedent);
    }
    if row.rhs == 0 {
        return Err(MigrationError::Declaration);
    }
    let premise = decode_literal(row.lhs)?;
    let conclusion = decode_literal(row.rhs)?;
    if row.model == 0 {
        if row.lhs < 0 {
            return Err(MigrationError::InvalidLiteral);
        }
        Ok(MigratedRow::Definition {
            atom: premise.atom(),
            conjunct: conclusion,
        })
    } else {
        Ok(MigratedRow::Theorem {
            premise,
            conclusion,
            reason: LEGACY_UNIVERSAL_REASON,
        })
    }
}

fn decode_literal(value: i64) -> Result<Literal, MigrationError> {
    let magnitude = u32::try_from(value.unsigned_abs())
        .ok()
        .and_then(AtomId::new)
        .ok_or(MigrationError::InvalidLiteral)?;
    Ok(if value < 0 {
        Literal::negative(magnitude)
    } else {
        Literal::positive(magnitude)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_lines(fixture: &str) -> impl Iterator<Item = &str> {
        fixture
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
    }

    fn encode(literal: Literal) -> i64 {
        let value = i64::from(literal.atom().get());
        if literal == Literal::negative(literal.atom()) {
            -value
        } else {
            value
        }
    }

    #[test]
    fn former_rows_have_an_explicit_mechanical_classification() {
        for line in fixture_lines(include_str!("../fixtures/legacy_prop_migration_v1.tsv")) {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 5, "invalid migration record: {line}");
            let row = LegacyRow {
                lhs: fields[1].parse().expect("lhs"),
                rhs: fields[2].parse().expect("rhs"),
                model: fields[3].parse().expect("model"),
            };
            let actual = match migrate_row(row) {
                Ok(migrated) => {
                    assert_eq!(migrated.source(), SourceId::LOCAL);
                    format!(
                        "row:{},0,{},{}",
                        encode(migrated.premise()),
                        encode(migrated.conclusion()),
                        migrated.reason()
                    )
                }
                Err(MigrationError::WorldRow) => "reject-world".to_owned(),
                Err(MigrationError::TruthAntecedent) => "reject-truth".to_owned(),
                Err(MigrationError::Declaration) => "reject-declaration".to_owned(),
                Err(MigrationError::InvalidLiteral) => "reject-literal".to_owned(),
            };
            assert_eq!(actual, fields[4], "migration fixture: {line}");
        }
    }

    #[test]
    fn legacy_metadata_does_not_become_a_checker_identity() {
        let a = migrate_row(LegacyRow {
            lhs: 1,
            rhs: 2,
            model: -1,
        })
        .expect("universal row");
        let b = migrate_row(LegacyRow {
            lhs: 1,
            rhs: 2,
            model: i64::MIN,
        })
        .expect("universal row");
        assert_eq!(a, b);
    }
}
