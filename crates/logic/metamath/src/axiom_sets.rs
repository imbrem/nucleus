//! Named logical axiom sets for the supported Metamath databases.
//!
//! These constants identify `$a` statements by label. Labels are database
//! metadata, not semantic evidence; [`AxiomSet::resolve`] checks them against a
//! parsed database and proof-theoretic or semantic claims require separate
//! checked evidence.

use std::collections::BTreeSet;

use covalence_lib_error::snafu::Snafu;

use crate::{Assertion, Database, Statement};

/// A named, layered set of logical `$a` labels from one Metamath database.
#[derive(Clone, Copy, Debug)]
pub struct AxiomSet {
    /// Human-readable theory name.
    pub name: &'static str,
    /// Database in which these labels are defined.
    pub database: &'static str,
    /// Weaker layers included by this theory.
    pub extends: &'static [&'static AxiomSet],
    /// Labels added by this layer.
    pub delta: &'static [&'static str],
}

impl AxiomSet {
    /// All labels in the set, sorted for deterministic reports.
    #[must_use]
    pub fn labels(&self) -> BTreeSet<&'static str> {
        let mut labels = BTreeSet::new();
        self.collect(&mut labels);
        labels
    }

    fn collect(&self, labels: &mut BTreeSet<&'static str>) {
        for base in self.extends {
            base.collect(labels);
        }
        labels.extend(self.delta.iter().copied());
    }

    /// Whether this set contains `label`.
    #[must_use]
    pub fn contains(&self, label: &str) -> bool {
        self.delta.contains(&label) || self.extends.iter().any(|base| base.contains(label))
    }

    /// Resolve every label as a logical `$a` in `db`.
    ///
    /// This detects database drift; it does not prove that `db` is the named
    /// upstream database or that the selected axioms have their intended
    /// semantics.
    ///
    /// # Errors
    ///
    /// Returns an error if a label is absent, names a hypothesis or theorem,
    /// or has a typecode other than `|-`.
    pub fn resolve<'db>(&self, db: &'db Database) -> Result<Vec<&'db Assertion>, AxiomSetError> {
        self.labels()
            .into_iter()
            .map(|label| match db.statement_by_label(label) {
                None => Err(AxiomSetError::MissingLabel {
                    set: self.name,
                    label,
                }),
                Some(Statement::Assert(assertion))
                    if assertion.proof.is_none() && assertion.conclusion.typecode() == "|-" =>
                {
                    Ok(assertion)
                }
                Some(_) => Err(AxiomSetError::NotLogicalAxiom {
                    set: self.name,
                    label,
                }),
            })
            .collect()
    }
}

/// Failure to resolve a named axiom set against a database.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AxiomSetError {
    /// A named label is absent.
    #[snafu(display("axiom set {set} requires absent label {label}"))]
    MissingLabel {
        /// Axiom-set name.
        set: &'static str,
        /// Missing label.
        label: &'static str,
    },
    /// A named label does not identify a logical `$a`.
    #[snafu(display("axiom set {set} label {label} is not a logical $a"))]
    NotLogicalAxiom {
        /// Axiom-set name.
        set: &'static str,
        /// Invalid label.
        label: &'static str,
    },
}

/// Classical propositional logic in `set.mm`.
pub static PROP: AxiomSet = AxiomSet {
    name: "PROP",
    database: "set.mm",
    extends: &[],
    delta: &["ax-mp", "ax-1", "ax-2", "ax-3"],
};

/// Classical first-order predicate logic with equality in `set.mm`.
pub static PRED: AxiomSet = AxiomSet {
    name: "PRED",
    database: "set.mm",
    extends: &[&PROP],
    delta: &[
        "ax-gen", "ax-4", "ax-5", "ax-6", "ax-7", "ax-8", "ax-9", "ax-10", "ax-11", "ax-12",
        "ax-13",
    ],
};

/// Peano arithmetic as postulated by `peano.mm`, excluding its `df-*`
/// definitions.
pub static PA: AxiomSet = AxiomSet {
    name: "PA",
    database: "peano.mm",
    extends: &[],
    delta: &[
        "ax-1",
        "ax-2",
        "ax-3",
        "ax-mp",
        "bi1",
        "bi2",
        "bi3",
        "eq-refl",
        "eq-sym",
        "eq-trans",
        "eq-congr",
        "eq-suc",
        "eq-binop",
        "alpha_1",
        "alpha_2",
        "alpha_3",
        "all_elim",
        "all_elim2",
        "all_elim3",
        "pa_ax1",
        "pa_ax2",
        "pa_ax3",
        "pa_ax4",
        "pa_ax5",
        "pa_ax6",
        "pa_ax7",
    ],
};

/// Higher-order logic as postulated by `hol.mm`, excluding definitions.
pub static HOL: AxiomSet = AxiomSet {
    name: "HOL",
    database: "hol.mm",
    extends: &[],
    delta: &[
        "ax-syl",
        "ax-jca",
        "ax-simpl",
        "ax-simpr",
        "ax-id",
        "ax-trud",
        "ax-cb1",
        "ax-cb2",
        "ax-wctl",
        "ax-wctr",
        "ax-weq",
        "ax-refl",
        "ax-eqmp",
        "ax-ded",
        "ax-wct",
        "ax-wc",
        "ax-ceq",
        "ax-wv",
        "ax-wl",
        "ax-beta",
        "ax-distrc",
        "ax-leq",
        "ax-distrl",
        "ax-wov",
        "ax-eqtypi",
        "ax-eqtypri",
        "ax-hbl1",
        "ax-17",
        "ax-inst",
        "ax-wabs",
        "ax-wrep",
        "ax-tdef",
        "ax-eta",
        "ax-wat",
        "ax-ac",
        "ax-inf",
    ],
};

static IPROP: AxiomSet = AxiomSet {
    name: "iPROP",
    database: "iset.mm",
    extends: &[],
    delta: &[
        "ax-mp", "ax-1", "ax-2", "ax-ia1", "ax-ia2", "ax-ia3", "ax-in1", "ax-in2", "ax-io",
    ],
};

static IPRED: AxiomSet = AxiomSet {
    name: "iPRED",
    database: "iset.mm",
    extends: &[&IPROP],
    delta: &[
        "ax-5", "ax-7", "ax-gen", "ax-ie1", "ax-ie2", "ax-8", "ax-10", "ax-11", "ax-i12",
        "ax-bndl", "ax-4", "ax-17", "ax-i9", "ax-ial", "ax-i5r", "ax-13", "ax-14",
    ],
};

/// Intuitionistic Zermelo–Fraenkel set theory in `iset.mm`.
pub static IZF: AxiomSet = AxiomSet {
    name: "IZF",
    database: "iset.mm",
    extends: &[&IPRED],
    delta: &[
        "ax-ext",
        "ax-coll",
        "ax-sep",
        "ax-nul",
        "ax-pow",
        "ax-pr",
        "ax-un",
        "ax-setind",
        "ax-iinf",
    ],
};

static ZF_KERNEL: AxiomSet = AxiomSet {
    name: "ZF kernel",
    database: "set.mm",
    extends: &[&PRED],
    delta: &["ax-ext", "ax-rep", "ax-pow", "ax-un", "ax-reg", "ax-inf"],
};

/// Zermelo–Fraenkel set theory as postulated by `set.mm`.
pub static ZF: AxiomSet = AxiomSet {
    name: "ZF",
    database: "set.mm",
    extends: &[&ZF_KERNEL],
    delta: &["ax-sep", "ax-nul", "ax-pr", "ax-inf2"],
};

/// ZF with choice as postulated by `set.mm`.
pub static ZFC: AxiomSet = AxiomSet {
    name: "ZFC",
    database: "set.mm",
    extends: &[&ZF],
    delta: &["ax-ac2", "ax-ac"],
};

/// Grothendieck–Tarski set theory in `set.mm`.
pub static GT: AxiomSet = AxiomSet {
    name: "GT",
    database: "set.mm",
    extends: &[&ZFC],
    delta: &["ax-groth"],
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    #[test]
    fn named_layers_have_expected_boundaries() {
        assert!(PROP.contains("ax-mp"));
        assert!(ZF.contains("ax-ext"));
        assert!(!ZF.contains("ax-ac"));
        assert!(ZFC.contains("ax-ac"));
        assert!(GT.contains("ax-groth"));
        assert!(IZF.contains("ax-setind"));
        assert!(PA.contains("pa_ax7"));
        assert!(HOL.contains("ax-beta"));
    }

    #[test]
    fn resolution_rejects_database_drift() {
        let db = parse("$c |- $. ax-mp $a |- $.").expect("parse fixture");
        assert!(matches!(
            PROP.resolve(&db),
            Err(AxiomSetError::MissingLabel { label: "ax-1", .. })
        ));
    }
}
