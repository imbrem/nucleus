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

    /// Proves `AND(A) |- SAT(A)`.
    ///
    /// # Errors
    ///
    /// Returns an error if the formulas cannot be represented.
    pub fn sat_intro(children: Vec<Formula>) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: children.clone(),
                },
                conclusion: Formula::Sat {
                    negative: false,
                    children,
                },
            }])?,
        })
    }

    /// Proves `AND([]) |- SAT(A)` from a checked assignment witness.
    ///
    /// # Errors
    ///
    /// Returns an error if the witnessed formulas cannot be represented.
    pub fn prove_sat(witness: &ModelWitness) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: Vec::new(),
                },
                conclusion: Formula::Sat {
                    negative: false,
                    children: witness.children.clone(),
                },
            }])?,
        })
    }

    /// Proves `SAT(A) |- SAT(B)` from checked models of both conjunctions.
    ///
    /// # Errors
    ///
    /// Returns an error if the witnessed formulas cannot be represented.
    pub fn model_sat_implication(
        premise: &ModelWitness,
        conclusion: &ModelWitness,
    ) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::Sat {
                    negative: false,
                    children: premise.children.clone(),
                },
                conclusion: Formula::Sat {
                    negative: false,
                    children: conclusion.children.clone(),
                },
            }])?,
        })
    }

    /// Proves `P |- AND([])`.
    ///
    /// # Errors
    ///
    /// Returns an error if the premise cannot be represented.
    pub fn truth_intro(premise: Formula) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&[Sequent {
                premise,
                conclusion: Formula::And {
                    negative: false,
                    children: Vec::new(),
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
        certificate: &crate::cnf::Refutation,
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

    /// Appends a formula to a positive `AND` premise or positive `OR`
    /// conclusion in place.
    ///
    /// The arena grows the selected array geometrically and keeps its storage
    /// private. This is the primitive weakening operation.
    ///
    /// # Errors
    ///
    /// Returns an error if the sequent is absent, the selected root has the
    /// wrong shape, or the formula cannot be represented.
    pub fn weaken_mut(
        &mut self,
        index: usize,
        side: Side,
        formula: &Formula,
    ) -> Result<(), EditError> {
        let view = self
            .checked
            .view(index)
            .ok_or(EditError::MissingSequent { index })?;
        let selected = match side {
            Side::Left => view.premise,
            Side::Right => view.conclusion,
        };
        let expected = match side {
            Side::Left => 0,
            Side::Right => 1,
        };
        if selected.tag() != expected || selected.is_negative() {
            return Err(EditError::InapplicableRoot { side });
        }
        self.checked.push_root(index, side, formula)?;
        Ok(())
    }

    /// Moves the final owned formula across the turnstile and complements it.
    ///
    /// # Errors
    ///
    /// Returns an error if the sequent is absent, its roots are not a positive
    /// `AND` and positive `OR`, its source is empty, or relocation fails.
    pub fn cross_root_mut(&mut self, index: usize, source: Side) -> Result<(), EditError> {
        let view = self
            .checked
            .view(index)
            .ok_or(EditError::MissingSequent { index })?;
        if view.premise.tag() != 0
            || view.premise.is_negative()
            || view.conclusion.tag() != 1
            || view.conclusion.is_negative()
        {
            return Err(EditError::InapplicableRoot { side: source });
        }
        let selected = match source {
            Side::Left => view.premise,
            Side::Right => view.conclusion,
        };
        if selected.is_empty() {
            return Err(EditError::EmptySource { side: source });
        }
        self.checked.cross_root(index, source)?;
        Ok(())
    }

    /// Pops the final child for the two primitive weakening shapes:
    /// `OR(A, P) |- Q` to `OR(A) |- Q`, and `P |- AND(A, Q)` to
    /// `P |- AND(A)`.
    ///
    /// # Errors
    ///
    /// Returns an error if the sequent is absent, the selected root has the
    /// wrong shape, or it is empty.
    pub fn pop_weaken_mut(&mut self, index: usize, side: Side) -> Result<(), EditError> {
        let view = self
            .checked
            .view(index)
            .ok_or(EditError::MissingSequent { index })?;
        let selected = match side {
            Side::Left => view.premise,
            Side::Right => view.conclusion,
        };
        let expected = match side {
            Side::Left => 1,
            Side::Right => 0,
        };
        if selected.tag() != expected || selected.is_negative() {
            return Err(EditError::InapplicableRoot { side });
        }
        if selected.is_empty() {
            return Err(EditError::EmptySource { side });
        }
        let removed = self.checked.pop_root(index, side)?;
        self.checked.reclaim(removed)?;
        Ok(())
    }

    /// Converts `AND([]) |- -SAT(A)` into `AND(A) |- OR([])`.
    ///
    /// # Errors
    ///
    /// Returns an error if the selected theorem member does not have that
    /// exact shape or the result cannot be represented.
    pub fn refutation_to_false(&self, index: usize) -> Result<Self, EditError> {
        let table = self.checked.decode_sequents()?;
        let sequent = table
            .get(index)
            .ok_or(EditError::MissingSequent { index })?;
        let Formula::And {
            negative: false,
            children: premise,
        } = &sequent.premise
        else {
            return Err(EditError::InapplicableBinaryRule {
                rule: "refutation-to-false",
            });
        };
        let Formula::Sat {
            negative: true,
            children,
        } = &sequent.conclusion
        else {
            return Err(EditError::InapplicableBinaryRule {
                rule: "refutation-to-false",
            });
        };
        if !premise.is_empty() {
            return Err(EditError::InapplicableBinaryRule {
                rule: "refutation-to-false",
            });
        }
        Ok(Self {
            checked: pack(&[Sequent {
                premise: Formula::And {
                    negative: false,
                    children: children.clone(),
                },
                conclusion: Formula::Or {
                    negative: false,
                    children: Vec::new(),
                },
            }])?,
        })
    }

    /// Canonically combines two theorem tables.
    ///
    /// # Errors
    ///
    /// Returns an error when the combined table exceeds the canonical
    /// packer's fixed-word or host resource bounds.
    pub fn append(&self, other: &Self) -> Result<Self, RuntimeError> {
        let mut sequents = self.checked.decode_sequents()?;
        sequents.extend(other.checked.decode_sequents()?);
        Ok(Self {
            checked: pack(&sequents)?,
        })
    }

    /// Rebuilds this theorem into compact semantic storage.
    ///
    /// Compaction drops allocator fragmentation, free blocks, sharing, and
    /// unreachable garbage. It is separate from ordinary mutations.
    ///
    /// # Errors
    ///
    /// Returns an error when the decoded table no longer fits the canonical
    /// packer's resource bounds.
    pub fn compact(&self) -> Result<Self, RuntimeError> {
        Ok(Self {
            checked: pack(&self.checked.decode_sequents()?)?,
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
        let left_table = self.checked.decode_sequents()?;
        let left = left_table
            .get(left_index)
            .ok_or(EditError::MissingInputSequent {
                input: "left",
                index: left_index,
            })?;
        let right_table = right.checked.decode_sequents()?;
        let right = right_table
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
        let left_table = self.checked.decode_sequents()?;
        let left = left_table
            .get(left_index)
            .ok_or(EditError::MissingInputSequent {
                input: "left",
                index: left_index,
            })?;
        let right_table = right.checked.decode_sequents()?;
        let right = right_table
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
}
use super::{
    Checked, EditError, Formula, ModelWitness, RuntimeError, Sequent, Side, Theorem, concatenate,
    erase_first, pack, positive_roots,
};
