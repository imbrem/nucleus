impl Theorem {
    /// Applies De Morgan's law at a selected formula.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path or a node other than a negated
    /// `AND` or negated `OR`.
    pub fn demorgan(&self, path: &FormulaPath) -> Result<Self, EditError> {
        let mut result = self.clone();
        result.demorgan_mut(path)?;
        Ok(result)
    }

    /// Applies De Morgan's law in place after copy-on-write path isolation.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path or inapplicable node.
    pub fn demorgan_mut(&mut self, path: &FormulaPath) -> Result<(), EditError> {
        self.checked.demorgan_path(path)?;
        Ok(())
    }

    /// Rewrites one contradictory junction in place.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path or absent complementary pair.
    pub fn contradiction_mut(
        &mut self,
        path: &FormulaPath,
        first: usize,
        second: usize,
    ) -> Result<(), EditError> {
        self.checked.contradiction_path(path, first, second)?;
        Ok(())
    }

    /// Flattens one selected nested junction.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path/index or incompatible constructors.
    pub fn flatten(&self, path: &FormulaPath, child: usize) -> Result<Self, EditError> {
        let mut result = self.clone();
        result.flatten_mut(path, child)?;
        Ok(result)
    }

    /// Flattens one nested junction in place.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path/index or incompatible constructors.
    pub fn flatten_mut(&mut self, path: &FormulaPath, child: usize) -> Result<(), EditError> {
        self.checked.flatten_path(path, child)?;
        Ok(())
    }

    /// Reorders one junction using a permutation of its current indices.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path or a non-permutation.
    pub fn permute(&self, path: &FormulaPath, order: &[usize]) -> Result<Self, EditError> {
        let mut result = self.clone();
        result.permute_mut(path, order)?;
        Ok(result)
    }

    /// Reorders one junction in place after checking its index permutation.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid path or non-permutation.
    pub fn permute_mut(&mut self, path: &FormulaPath, order: &[usize]) -> Result<(), EditError> {
        self.checked.permute_path(path, order)?;
        Ok(())
    }

    /// Removes one child after checking it duplicates another child.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid/equal indices or structurally unequal children.
    pub fn dedup_local(
        &self,
        path: &FormulaPath,
        remove: usize,
        retain: usize,
    ) -> Result<Self, EditError> {
        let mut result = self.clone();
        result.dedup_local_mut(path, remove, retain)?;
        Ok(result)
    }

    /// Removes one checked duplicate child in place.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid/equal indices or unequal children.
    pub fn dedup_local_mut(
        &mut self,
        path: &FormulaPath,
        remove: usize,
        retain: usize,
    ) -> Result<(), EditError> {
        self.checked.dedup_local_path(path, remove, retain)?;
        Ok(())
    }

    /// Rewrites a selected formula using proofs of both implication directions.
    ///
    /// # Errors
    ///
    /// Returns an error unless both inputs are singleton opposite-direction
    /// sequents and the selected formula matches the forward premise.
    pub fn rewrite_equivalent(
        &self,
        path: &FormulaPath,
        forward: &Self,
        backward: &Self,
    ) -> Result<Self, EditError> {
        let forward = singleton(forward)?;
        let backward = singleton(backward)?;
        if forward.premise != backward.conclusion || forward.conclusion != backward.premise {
            return Err(EditError::InapplicableRewrite {
                rule: "equivalence",
            });
        }
        // Equivalence replacement is not a hot mutation primitive: it rebuilds
        // the semantic theorem. The allocator-level rewrites above stay packed.
        let mut sequents = self.checked.decode_sequents()?;
        let sequent = sequents
            .get_mut(path.sequent())
            .ok_or(EditError::InvalidPath)?;
        let mut formula = match path.side() {
            Side::Left => &mut sequent.premise,
            Side::Right => &mut sequent.conclusion,
        };
        for &index in path.children() {
            formula = match formula {
                Formula::And { children, .. }
                | Formula::Or { children, .. }
                | Formula::Sat { children, .. } => {
                    children.get_mut(index).ok_or(EditError::InvalidPath)?
                }
                Formula::Literal { .. } => return Err(EditError::InvalidPath),
            };
        }
        if *formula != forward.premise {
            return Err(EditError::InapplicableRewrite {
                rule: "equivalence",
            });
        }
        *formula = forward.conclusion.clone();
        Ok(Self {
            checked: pack(&sequents)?,
        })
    }
}
use super::{EditError, Formula, FormulaPath, Side, Theorem, pack, singleton};
