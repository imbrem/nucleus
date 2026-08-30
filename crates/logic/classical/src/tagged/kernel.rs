//! Sealed theorem authority for the tagged runtime.

use std::hash::{Hash, Hasher};

use covalence_lib_error::snafu::Snafu;

use super::{Checked, Formula, RuntimeError, Sequent, Side, pack};

/// Failure to apply a canonical theorem-preserving root edit.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum EditError {
    /// The theorem table has no sequent at the requested index.
    #[snafu(display("missing tagged sequent at index {index}"))]
    MissingSequent {
        /// Rejected zero-based index.
        index: usize,
    },
    /// The selected root was not a positive left `AND` or positive right `OR`.
    #[snafu(display("root edit does not apply to the {side:?} side"))]
    InapplicableRoot {
        /// Selected sequent side.
        side: Side,
    },
    /// A proposed root order was not a permutation of the current children.
    #[snafu(display("proposed root order is not a permutation"))]
    NotPermutation,
    /// A crossing rule selected an empty source root.
    #[snafu(display("cannot cross from an empty {side:?} root"))]
    EmptySource {
        /// Selected source side.
        side: Side,
    },
    /// A binary rule selected no theorem member at one input index.
    #[snafu(display("missing {input} tagged sequent at index {index}"))]
    MissingInputSequent {
        /// Input theorem table.
        input: &'static str,
        /// Rejected zero-based index.
        index: usize,
    },
    /// A binary rule requires positive `AND`/`OR` roots on both inputs.
    #[snafu(display("{rule} requires positive AND premises and positive OR conclusions"))]
    InapplicableBinaryRule {
        /// Rule that could not be applied.
        rule: &'static str,
    },
    /// The required first structural pivot occurrence was absent.
    #[snafu(display("{rule} pivot is absent from the {input}"))]
    MissingPivot {
        /// Rule that could not be applied.
        rule: &'static str,
        /// Root in which no occurrence was found.
        input: &'static str,
    },
    /// A compatibility matrix rule received a non-matrix sequent or row.
    #[snafu(display("{rule} requires positive AND-of-OR premises and OR-of-AND conclusions"))]
    InapplicableMatrixRule {
        /// Rule that could not be applied.
        rule: &'static str,
    },
    /// A compatibility matrix row index was absent.
    #[snafu(display("missing matrix row {index} on the {side:?} side"))]
    MissingMatrixRow {
        /// Side containing the requested row.
        side: Side,
        /// Zero-based row index in the decoded matrix.
        index: usize,
    },
    /// Canonical repacking failed after the abstract edit.
    #[snafu(transparent)]
    Runtime {
        /// Underlying runtime failure.
        source: RuntimeError,
    },
}

/// An LCF theorem fact backed by checked tagged-runtime syntax.
///
/// The field is private: validation alone creates [`Checked`] syntax, while
/// only the rule implementations in this module may construct theorem facts.
#[derive(Clone, Debug)]
pub struct Theorem {
    checked: Checked,
}

impl Theorem {
    /// Constructs the primitive identity theorem `formula |- formula`.
    ///
    /// # Errors
    ///
    /// Returns an error when the fixed-width canonical packer cannot represent
    /// the formula.
    pub fn identity(formula: Formula) -> Result<Self, RuntimeError> {
        let sequent = Sequent {
            premise: formula.clone(),
            conclusion: formula,
        };
        Ok(Self {
            checked: pack(&[sequent])?,
        })
    }

    /// Constructs the compatibility matrix identity
    /// `AND[OR[p]] |- OR[AND[p]]`.
    ///
    /// This crate-private introduction exists only to keep the legacy matrix
    /// facade on the same sealed theorem boundary as the tagged runtime.
    pub(crate) fn matrix_identity(literal: Formula) -> Result<Self, EditError> {
        require_literal(&literal, "matrix identity")?;
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![Formula::Or {
                        negative: false,
                        children: vec![literal.clone()],
                    }],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![Formula::And {
                        negative: false,
                        children: vec![literal],
                    }],
                },
            }])?,
        })
    }

    /// Seals an opaque statefully checked RUP/RAT result.
    ///
    /// The certificate type has no public constructor or deserializer. Its
    /// producing state machine is the Rust counterpart of Lean's
    /// `Runtime.Refutation.Checker.Result` boundary.
    pub(crate) fn seal_refutation(
        certificate: &crate::compat::Refutation,
    ) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&[certificate.sequent_for_sealing()])?,
        })
    }

    /// Returns the checked syntax carried by this theorem fact.
    #[must_use]
    pub const fn checked(&self) -> &Checked {
        &self.checked
    }

    /// Canonically combines two theorem tables.
    ///
    /// # Errors
    ///
    /// Returns an error when the combined table exceeds the canonical
    /// packer's fixed-word or host resource bounds.
    pub fn append(&self, other: &Self) -> Result<Self, RuntimeError> {
        let mut sequents = self.checked.sequents().to_vec();
        sequents.extend_from_slice(other.checked.sequents());
        Ok(Self {
            checked: pack(&sequents)?,
        })
    }

    /// Canonically deep-copies this theorem table.
    ///
    /// # Errors
    ///
    /// Returns an error when the decoded table no longer fits the canonical
    /// packer's resource bounds.
    pub fn canonical_copy(&self) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(self.checked.sequents())?,
        })
    }

    /// Cuts the first matching structural pivot from a selected left
    /// conclusion and selected right premise.
    ///
    /// The result is a fresh singleton theorem table. All four selected roots
    /// must use positive `AND` premises and positive `OR` conclusions.
    ///
    /// # Errors
    ///
    /// Returns an error when an index is absent, a selected sequent has the
    /// wrong root shape, either pivot occurrence is absent, or canonical
    /// repacking fails.
    pub fn cut(
        &self,
        left_index: usize,
        right: &Self,
        right_index: usize,
        pivot: &Formula,
    ) -> Result<Self, EditError> {
        let left =
            self.checked
                .sequents()
                .get(left_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "left",
                    index: left_index,
                })?;
        let right =
            right
                .checked
                .sequents()
                .get(right_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "right",
                    index: right_index,
                })?;
        let (left_premise, mut left_conclusion) =
            positive_roots(left).ok_or(EditError::InapplicableBinaryRule { rule: "cut" })?;
        let (mut right_premise, right_conclusion) =
            positive_roots(right).ok_or(EditError::InapplicableBinaryRule { rule: "cut" })?;
        erase_first(&mut left_conclusion, pivot).ok_or(EditError::MissingPivot {
            rule: "cut",
            input: "left conclusion",
        })?;
        erase_first(&mut right_premise, pivot).ok_or(EditError::MissingPivot {
            rule: "cut",
            input: "right premise",
        })?;
        let result = Sequent {
            premise: Formula::And {
                negative: false,
                children: concatenate(left_premise, right_premise),
            },
            conclusion: Formula::Or {
                negative: false,
                children: concatenate(left_conclusion, right_conclusion),
            },
        };
        Ok(Self {
            checked: pack(&[result])?,
        })
    }

    /// Resolves the first pivot and complement in two selected conclusions.
    ///
    /// `SAT` nodes remain closed formulas: this operation compares complete
    /// structural formulas and never treats atoms bound below `SAT` as ambient
    /// variables.
    ///
    /// # Errors
    ///
    /// Returns an error when an index is absent, a selected sequent has the
    /// wrong root shape, either pivot occurrence is absent, or canonical
    /// repacking fails.
    pub fn resolve(
        &self,
        left_index: usize,
        right: &Self,
        right_index: usize,
        pivot: &Formula,
    ) -> Result<Self, EditError> {
        let left =
            self.checked
                .sequents()
                .get(left_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "left",
                    index: left_index,
                })?;
        let right =
            right
                .checked
                .sequents()
                .get(right_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "right",
                    index: right_index,
                })?;
        let (left_premise, mut left_conclusion) =
            positive_roots(left).ok_or(EditError::InapplicableBinaryRule { rule: "resolve" })?;
        let (right_premise, mut right_conclusion) =
            positive_roots(right).ok_or(EditError::InapplicableBinaryRule { rule: "resolve" })?;
        erase_first(&mut left_conclusion, pivot).ok_or(EditError::MissingPivot {
            rule: "resolve",
            input: "left conclusion",
        })?;
        erase_first(&mut right_conclusion, &pivot.clone().negated()).ok_or(
            EditError::MissingPivot {
                rule: "resolve",
                input: "right conclusion",
            },
        )?;
        let result = Sequent {
            premise: Formula::And {
                negative: false,
                children: concatenate(left_premise, right_premise),
            },
            conclusion: Formula::Or {
                negative: false,
                children: concatenate(left_conclusion, right_conclusion),
            },
        };
        Ok(Self {
            checked: pack(&[result])?,
        })
    }

    /// Appends one compatibility clause or cube as matrix weakening.
    pub(crate) fn matrix_weaken_row(
        &self,
        index: usize,
        side: Side,
        row: Vec<Formula>,
    ) -> Result<Self, EditError> {
        require_literal_row(&row, "matrix weakening")?;
        self.edit(index, |sequent| {
            let (premise, conclusion) = matrix_roots_mut(sequent, "matrix weakening")?;
            match side {
                Side::Left => premise.push(Formula::Or {
                    negative: false,
                    children: row,
                }),
                Side::Right => conclusion.push(Formula::And {
                    negative: false,
                    children: row,
                }),
            }
            Ok(())
        })
    }

    /// Cuts the first matching unit cube and clause from two matrix facts.
    pub(crate) fn matrix_unit_cut(
        &self,
        left_index: usize,
        right: &Self,
        right_index: usize,
        pivot: Formula,
    ) -> Result<Self, EditError> {
        require_literal(&pivot, "matrix cut")?;
        let left =
            self.checked
                .sequents()
                .get(left_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "left",
                    index: left_index,
                })?;
        let right =
            right
                .checked
                .sequents()
                .get(right_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "right",
                    index: right_index,
                })?;
        let (mut left_premise, mut left_conclusion) = matrix_roots(left, "matrix cut")?;
        let (mut right_premise, right_conclusion) = matrix_roots(right, "matrix cut")?;
        erase_first(&mut left_conclusion, &matrix_cube(vec![pivot.clone()])).ok_or(
            EditError::MissingPivot {
                rule: "matrix cut",
                input: "left conclusion",
            },
        )?;
        erase_first(&mut right_premise, &matrix_clause(vec![pivot])).ok_or(
            EditError::MissingPivot {
                rule: "matrix cut",
                input: "right premise",
            },
        )?;
        left_premise.extend(right_premise);
        left_conclusion.extend(right_conclusion);
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: left_premise,
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: left_conclusion,
                },
            }])?,
        })
    }

    /// Resolves the first matching complementary unit cubes in two facts.
    pub(crate) fn matrix_unit_resolve(
        &self,
        left_index: usize,
        right: &Self,
        right_index: usize,
        pivot: Formula,
    ) -> Result<Self, EditError> {
        require_literal(&pivot, "matrix resolution")?;
        let left =
            self.checked
                .sequents()
                .get(left_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "left",
                    index: left_index,
                })?;
        let right =
            right
                .checked
                .sequents()
                .get(right_index)
                .ok_or(EditError::MissingInputSequent {
                    input: "right",
                    index: right_index,
                })?;
        let (mut left_premise, mut left_conclusion) = matrix_roots(left, "matrix resolution")?;
        let (right_premise, mut right_conclusion) = matrix_roots(right, "matrix resolution")?;
        erase_first(&mut left_conclusion, &matrix_cube(vec![pivot.clone()])).ok_or(
            EditError::MissingPivot {
                rule: "matrix resolution",
                input: "left conclusion",
            },
        )?;
        erase_first(&mut right_conclusion, &matrix_cube(vec![pivot.negated()])).ok_or(
            EditError::MissingPivot {
                rule: "matrix resolution",
                input: "right conclusion",
            },
        )?;
        left_premise.extend(right_premise);
        left_conclusion.extend(right_conclusion);
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: left_premise,
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: left_conclusion,
                },
            }])?,
        })
    }

    /// Crosses one decoded compatibility row and applies pointwise negation.
    pub(crate) fn matrix_cross_row(
        &self,
        index: usize,
        source_side: Side,
        row_index: usize,
    ) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            let (premise, conclusion) = matrix_roots_mut(sequent, "matrix crossing")?;
            match source_side {
                Side::Left => {
                    let row = take_row(premise, source_side, row_index)?;
                    let Formula::Or { children, .. } = row else {
                        return Err(EditError::InapplicableMatrixRule {
                            rule: "matrix crossing",
                        });
                    };
                    conclusion.push(matrix_cube(
                        children.into_iter().map(Formula::negated).collect(),
                    ));
                }
                Side::Right => {
                    let row = take_row(conclusion, source_side, row_index)?;
                    let Formula::And { children, .. } = row else {
                        return Err(EditError::InapplicableMatrixRule {
                            rule: "matrix crossing",
                        });
                    };
                    premise.push(matrix_clause(
                        children.into_iter().map(Formula::negated).collect(),
                    ));
                }
            }
            Ok(())
        })
    }

    /// Reorders the literals of one decoded compatibility row.
    pub(crate) fn matrix_permute_row(
        &self,
        index: usize,
        side: Side,
        row_index: usize,
        candidate: Vec<Formula>,
    ) -> Result<Self, EditError> {
        require_literal_row(&candidate, "matrix row permutation")?;
        self.edit(index, |sequent| {
            let row = matrix_row_mut(sequent, side, row_index, "matrix row permutation")?;
            if !is_permutation(&candidate, row) {
                return Err(EditError::NotPermutation);
            }
            *row = candidate;
            Ok(())
        })
    }

    /// Removes later duplicate literals from one compatibility row.
    pub(crate) fn matrix_dedupe_row(
        &self,
        index: usize,
        side: Side,
        row_index: usize,
    ) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            let row = matrix_row_mut(sequent, side, row_index, "matrix row deduplication")?;
            let mut unique = Vec::with_capacity(row.len());
            for literal in row.drain(..) {
                if !unique.contains(&literal) {
                    unique.push(literal);
                }
            }
            *row = unique;
            Ok(())
        })
    }

    /// Replaces one supported root's children after checking an actual
    /// structural permutation.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is absent, the side is not a positive
    /// left `AND` or positive right `OR`, the candidate is not a permutation,
    /// or canonical repacking fails.
    pub fn canonical_reorder_root(
        &self,
        index: usize,
        side: Side,
        candidate: Vec<Formula>,
    ) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            let current = editable_children_mut(sequent, side)?;
            if !is_permutation(&candidate, current) {
                return Err(EditError::NotPermutation);
            }
            *current = candidate;
            Ok(())
        })
    }

    /// Stably sorts one supported root by an implementation-supplied key.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is absent, the selected root has the
    /// wrong constructor or polarity, or canonical repacking fails.
    pub fn canonical_sort_root_by_key<K, F>(
        &self,
        index: usize,
        side: Side,
        mut key: F,
    ) -> Result<Self, EditError>
    where
        K: Ord,
        F: FnMut(&Formula) -> K,
    {
        self.edit(index, |sequent| {
            editable_children_mut(sequent, side)?.sort_by_key(&mut key);
            Ok(())
        })
    }

    /// Removes later structural duplicates from one supported root.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is absent, the selected root has the
    /// wrong constructor or polarity, or canonical repacking fails.
    pub fn canonical_dedupe_root(&self, index: usize, side: Side) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            let children = editable_children_mut(sequent, side)?;
            let mut unique = Vec::with_capacity(children.len());
            for child in children.drain(..) {
                if !unique.contains(&child) {
                    unique.push(child);
                }
            }
            *children = unique;
            Ok(())
        })
    }

    /// Weakens one supported sequent by appending an owned formula.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is absent, the selected root has the
    /// wrong constructor or polarity, or canonical repacking fails.
    pub fn canonical_push_root(
        &self,
        index: usize,
        side: Side,
        pushed: Formula,
    ) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            editable_children_mut(sequent, side)?.push(pushed);
            Ok(())
        })
    }

    /// Alias for canonical root push, emphasizing its weakening meaning.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::canonical_push_root`].
    pub fn weaken(&self, index: usize, side: Side, pushed: Formula) -> Result<Self, EditError> {
        self.canonical_push_root(index, side, pushed)
    }

    /// Moves the final child across the turnstile and complements it.
    ///
    /// Both roots must be positive left `AND` and positive right `OR`. The
    /// moved formula retains its connective and children; only its root sign
    /// changes.
    ///
    /// # Errors
    ///
    /// Returns an error if the index is absent, either root has the wrong
    /// constructor or polarity, the selected source is empty, or repacking
    /// fails.
    pub fn canonical_cross_root(&self, index: usize, source_side: Side) -> Result<Self, EditError> {
        self.edit(index, |sequent| {
            let (
                Formula::And {
                    negative: false,
                    children: left,
                },
                Formula::Or {
                    negative: false,
                    children: right,
                },
            ) = (&mut sequent.premise, &mut sequent.conclusion)
            else {
                return Err(EditError::InapplicableRoot { side: source_side });
            };
            match source_side {
                Side::Left => {
                    let moved = left
                        .pop()
                        .ok_or(EditError::EmptySource { side: source_side })?;
                    right.push(moved.negated());
                }
                Side::Right => {
                    let moved = right
                        .pop()
                        .ok_or(EditError::EmptySource { side: source_side })?;
                    left.push(moved.negated());
                }
            }
            Ok(())
        })
    }

    fn edit(
        &self,
        index: usize,
        edit: impl FnOnce(&mut Sequent) -> Result<(), EditError>,
    ) -> Result<Self, EditError> {
        let mut sequents = self.checked.sequents().to_vec();
        let sequent = sequents
            .get_mut(index)
            .ok_or(EditError::MissingSequent { index })?;
        edit(sequent)?;
        Ok(Self {
            checked: pack(&sequents)?,
        })
    }
}

impl PartialEq for Theorem {
    fn eq(&self, other: &Self) -> bool {
        self.checked == other.checked
    }
}

impl Eq for Theorem {}

impl Hash for Theorem {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.checked.hash(state);
    }
}

fn editable_children_mut(
    sequent: &mut Sequent,
    side: Side,
) -> Result<&mut Vec<Formula>, EditError> {
    match (side, &mut sequent.premise, &mut sequent.conclusion) {
        (
            Side::Left,
            Formula::And {
                negative: false,
                children,
            },
            _,
        )
        | (
            Side::Right,
            _,
            Formula::Or {
                negative: false,
                children,
            },
        ) => Ok(children),
        _ => Err(EditError::InapplicableRoot { side }),
    }
}

fn require_literal(formula: &Formula, rule: &'static str) -> Result<(), EditError> {
    if matches!(formula, Formula::Literal { .. }) {
        Ok(())
    } else {
        Err(EditError::InapplicableMatrixRule { rule })
    }
}

fn require_literal_row(row: &[Formula], rule: &'static str) -> Result<(), EditError> {
    if row
        .iter()
        .all(|formula| matches!(formula, Formula::Literal { .. }))
    {
        Ok(())
    } else {
        Err(EditError::InapplicableMatrixRule { rule })
    }
}

fn matrix_clause(children: Vec<Formula>) -> Formula {
    Formula::Or {
        negative: false,
        children,
    }
}

fn matrix_cube(children: Vec<Formula>) -> Formula {
    Formula::And {
        negative: false,
        children,
    }
}

fn matrix_roots(
    sequent: &Sequent,
    rule: &'static str,
) -> Result<(Vec<Formula>, Vec<Formula>), EditError> {
    let (premise, conclusion) =
        positive_roots(sequent).ok_or(EditError::InapplicableMatrixRule { rule })?;
    if premise.iter().all(is_matrix_clause) && conclusion.iter().all(is_matrix_cube) {
        Ok((premise, conclusion))
    } else {
        Err(EditError::InapplicableMatrixRule { rule })
    }
}

fn matrix_roots_mut<'a>(
    sequent: &'a mut Sequent,
    rule: &'static str,
) -> Result<(&'a mut Vec<Formula>, &'a mut Vec<Formula>), EditError> {
    let (
        Formula::And {
            negative: false,
            children: premise,
        },
        Formula::Or {
            negative: false,
            children: conclusion,
        },
    ) = (&mut sequent.premise, &mut sequent.conclusion)
    else {
        return Err(EditError::InapplicableMatrixRule { rule });
    };
    if premise.iter().all(is_matrix_clause) && conclusion.iter().all(is_matrix_cube) {
        Ok((premise, conclusion))
    } else {
        Err(EditError::InapplicableMatrixRule { rule })
    }
}

fn is_matrix_clause(formula: &Formula) -> bool {
    matches!(formula, Formula::Or { negative: false, children }
        if children.iter().all(|child| matches!(child, Formula::Literal { .. })))
}

fn is_matrix_cube(formula: &Formula) -> bool {
    matches!(formula, Formula::And { negative: false, children }
        if children.iter().all(|child| matches!(child, Formula::Literal { .. })))
}

fn take_row(rows: &mut Vec<Formula>, side: Side, index: usize) -> Result<Formula, EditError> {
    if index < rows.len() {
        Ok(rows.remove(index))
    } else {
        Err(EditError::MissingMatrixRow { side, index })
    }
}

fn matrix_row_mut<'a>(
    sequent: &'a mut Sequent,
    side: Side,
    row_index: usize,
    rule: &'static str,
) -> Result<&'a mut Vec<Formula>, EditError> {
    let (premise, conclusion) = matrix_roots_mut(sequent, rule)?;
    let row = match side {
        Side::Left => premise.get_mut(row_index),
        Side::Right => conclusion.get_mut(row_index),
    }
    .ok_or(EditError::MissingMatrixRow {
        side,
        index: row_index,
    })?;
    match (side, row) {
        (
            Side::Left,
            Formula::Or {
                negative: false,
                children,
            },
        )
        | (
            Side::Right,
            Formula::And {
                negative: false,
                children,
            },
        ) => Ok(children),
        _ => Err(EditError::InapplicableMatrixRule { rule }),
    }
}

fn is_permutation(left: &[Formula], right: &[Formula]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut used = vec![false; right.len()];
    for formula in left {
        let Some((index, _)) = right
            .iter()
            .enumerate()
            .find(|(index, candidate)| !used[*index] && *candidate == formula)
        else {
            return false;
        };
        used[index] = true;
    }
    true
}

fn positive_roots(sequent: &Sequent) -> Option<(Vec<Formula>, Vec<Formula>)> {
    let Formula::And {
        negative: false,
        children: premise,
    } = &sequent.premise
    else {
        return None;
    };
    let Formula::Or {
        negative: false,
        children: conclusion,
    } = &sequent.conclusion
    else {
        return None;
    };
    Some((premise.clone(), conclusion.clone()))
}

fn erase_first(values: &mut Vec<Formula>, target: &Formula) -> Option<Formula> {
    let index = values.iter().position(|value| value == target)?;
    Some(values.remove(index))
}

fn concatenate(mut left: Vec<Formula>, right: Vec<Formula>) -> Vec<Formula> {
    left.extend(right);
    left
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(atom: u64) -> Formula {
        Formula::Literal {
            atom,
            negative: false,
        }
    }

    #[test]
    fn canonical_cross_moves_and_complements_the_final_owned_formula() {
        let p = literal(1);
        let checked = pack(&[Sequent {
            premise: Formula::And {
                negative: false,
                children: vec![p.clone()],
            },
            conclusion: Formula::Or {
                negative: false,
                children: vec![p.clone()],
            },
        }])
        .unwrap();
        // This private test sequent is the valid implication `p -> p` in the
        // selected positive-root presentation. Production callers cannot use
        // this constructor.
        let theorem = Theorem { checked };
        let crossed = theorem.canonical_cross_root(0, Side::Left).unwrap();
        let sequent = &crossed.checked().sequents()[0];
        assert_eq!(
            sequent.premise,
            Formula::And {
                negative: false,
                children: vec![]
            }
        );
        assert_eq!(
            sequent.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p.clone(), p.negated()]
            }
        );
    }

    #[test]
    fn cut_and_resolve_remove_first_structural_pivots() {
        let p = literal(1);
        let not_p = p.clone().negated();
        let positive = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![p.clone()],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![p.clone(), p.clone()],
                },
            }])
            .unwrap(),
        };
        let negative = Theorem {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: vec![not_p.clone()],
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: vec![not_p.clone()],
                },
            }])
            .unwrap(),
        };

        let cut = positive.cut(0, &positive, 0, &p).unwrap();
        let cut_result = &cut.checked().sequents()[0];
        assert_eq!(
            cut_result.premise,
            Formula::And {
                negative: false,
                children: vec![p.clone()]
            }
        );
        assert_eq!(
            cut_result.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p.clone(), p.clone(), p.clone()]
            }
        );

        let resolved = positive.resolve(0, &negative, 0, &p).unwrap();
        let resolved_result = &resolved.checked().sequents()[0];
        assert_eq!(
            resolved_result.premise,
            Formula::And {
                negative: false,
                children: vec![p.clone(), not_p]
            }
        );
        assert_eq!(
            resolved_result.conclusion,
            Formula::Or {
                negative: false,
                children: vec![p]
            }
        );
    }
}
