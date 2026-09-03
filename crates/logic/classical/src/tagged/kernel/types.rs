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
    /// Canonical repacking failed after the abstract edit.
    #[snafu(transparent)]
    Runtime {
        /// Underlying runtime failure.
        source: RuntimeError,
    },
    /// A formula path did not select an existing node.
    #[snafu(display("invalid formula path"))]
    InvalidPath,
    /// An equivalence rewrite did not match its required shape.
    #[snafu(display("inapplicable formula rewrite: {rule}"))]
    InapplicableRewrite {
        /// Name of the rejected rewrite.
        rule: &'static str,
    },
    /// An assignment did not witness the requested propositional conjunction.
    #[snafu(display("assignment does not witness the SAT claim"))]
    InvalidModel,
    /// A model witness contained a nested `SAT` node.
    #[snafu(display("model witness cannot evaluate nested SAT"))]
    NestedSat,
}

/// A conjunction checked true under one explicit Boolean assignment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModelWitness {
    pub(super) children: Vec<Formula>,
}

impl ModelWitness {
    /// Checks a conjunction under the assignment whose listed atoms are true.
    ///
    /// # Errors
    ///
    /// Returns an error if the conjunction is false or contains nested `SAT`.
    pub fn check(
        children: Vec<Formula>,
        true_atoms: impl IntoIterator<Item = u32>,
    ) -> Result<Self, EditError> {
        let assignment = true_atoms
            .into_iter()
            .collect::<std::collections::HashSet<_>>();
        for formula in &children {
            if !evaluate(formula, &assignment)? {
                return Err(EditError::InvalidModel);
            }
        }
        Ok(Self { children })
    }
}

/// An LCF theorem fact backed by checked tagged-runtime syntax.
///
/// The field is private: validation alone creates [`Checked`] syntax, while
/// only the rule implementations in this module may construct theorem facts.
#[derive(Clone, Debug)]
pub struct Theorem {
    pub(super) checked: Checked,
}

use super::{Checked, Formula, RuntimeError, Side, Snafu, evaluate};
