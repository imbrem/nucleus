//! What a theorem cites, and what it rests on.
//!
//! Two queries, and they are not the same shape. **Dependencies** — the labels
//! a proof transitively cites — is a plain reachability walk. **Axioms** — the
//! `$a` statements underneath a theorem — needs a further judgement that
//! Metamath itself does not make, and that judgement is the reason this module
//! is more than a graph traversal.
//!
//! ## Three kinds of `$a`, and only one of them is structural
//!
//! A `$a` is an *unproved assertion*. The format says nothing more. But real
//! databases use `$a` for three unrelated jobs:
//!
//! * a **syntax constructor** — `wi $a wff ( ph -> ps ) $.`, a production of
//!   the grammar. Structurally recognisable: its conclusion's typecode is not
//!   the provable typecode. That test is clean across `set.mm`, `iset.mm`,
//!   `hol.mm`, `nf.mm` and `ql.mm`, and it matters — **48% of `set.mm`'s `$a`
//!   are syntax constructors**, which is most of what a naive query returns.
//! * a **definition** — `df-an $a |- ( ( ph /\ ps ) <-> ... ) $.`, which
//!   introduces a constant and is meant to be eliminable;
//! * a **logical axiom** — `ax-mp`, `ax-ext`, `ax-groth`, the real
//!   assumptions.
//!
//! The syntax split is structural. **The axiom-versus-definition split is
//! not.** Nothing in the format distinguishes them — no typecode, no keyword,
//! no syntactic property. Every prior tool falls back to the `ax-` / `df-`
//! label prefix, independently: `metamath.exe` (`mmcmds.c` says so in a
//! comment: "It is up to the database creator to follow this standard, which
//! is not enforced"), `metamath-knife`, and mmj2.
//!
//! So this module keeps the two apart. [`AxiomRole::Syntax`] comes from the
//! typecode; [`AxiomRole::Axiom`] and [`AxiomRole::Definition`] come from
//! [`Conventions`], which the caller supplies and can replace.
//!
//! ## `Unclassified` is the point
//!
//! A logical `$a` that matches no convention is
//! [`AxiomRole::Unclassified`] — reported, never dropped. Prior tools drop
//! such statements: `metamath.exe` omits them from its HTML axiom lists, and
//! `metamath-knife`'s usage checker contains
//! `if !axiom.starts_with(b"ax-") { continue; }`. Either way **a mislabelled
//! `|-` `$a` becomes an invisible assumption**, which is precisely the failure
//! a provenance query exists to prevent.
//!
//! This is not hypothetical. Two databases in this crate's own corpus test do
//! not follow the convention at all:
//!
//! | database | `$a` | `\|-` `$a` | `df-` | `ax-` | neither |
//! |---|---:|---:|---:|---:|---:|
//! | `set.mm` | 3,008 | 1,563 | 1,437 | 126 | 0 |
//! | `iset.mm` | 905 | 493 | 404 | 89 | 0 |
//! | `nf.mm` | 363 | 201 | 158 | 43 | 0 |
//! | `hol.mm` | 71 | 47 | 11 | 36 | 0 |
//! | `miu.mm` | 10 | 5 | 0 | 0 | **5** |
//! | `peano.mm` | 48 | 30 | 0 | 6 | **24** |
//!
//! Anything hard-coding `ax-` answers *nothing* for the last two.
//!
//! ## Decode, don't replay — and don't shortcut either
//!
//! Neither query simulates the proof stack. [`proof_steps`] already decodes
//! both encodings to a uniform step sequence, and the label steps are all a
//! citation query needs.
//!
//! A compressed proof's `( ... )` label block is *not* used as the answer,
//! though it is tempting and `metamath-knife` does it. Decoding every letter
//! block in `set.mm` and comparing shows the roster is exact for 47,670 of
//! 47,678 theorems but carries 15 stray unused entries across the other 8. It
//! over-approximates, so it is decoded rather than read off.
//!
//! ## Scope
//!
//! * **`$f` / `$e` labels are dropped.** They are the theorem's own
//!   parameters and already sit in [`Assertion::frame`]; `metamath.exe` drops
//!   them at the source too.
//! * **`$d` conditions do not accumulate.** A cited assertion's obligations
//!   are discharged where it is applied, against the prover's own
//!   `scope_disjoints`; they do not propagate outward.
//! * **An axiom rests on itself.** [`axioms`] of a `$a` is that `$a`.
//!
//! ## Why the whole-database answer is one forward pass
//!
//! [`replay`](crate::replay) rejects a proof citing a label declared no
//! earlier than the theorem being proved, so **the citation graph is a DAG in
//! source order by construction**. [`AxiomIndex`] exploits that: a single
//! forward sweep, each assertion's axiom set the union of its citations' —
//! already computed, because they come earlier. No recursion, no visited set,
//! no cycle detection, and 50,686 answers for the cost of about one.
//!
//! The index does not *assume* the ordering, because a database that has not
//! been verified carries no such guarantee: `decompress_proof` checks that a
//! label-block entry exists, not that it is earlier. A citation that resolves
//! to a not-yet-swept assertion is [`MmError::ForwardReference`] — one
//! comparison per edge, which the "is it in the table yet" lookup already
//! performs.

use fnv::{FnvHashMap, FnvHashSet};

use crate::database::{Assertion, Database, Statement};
use crate::error::MmError;
use crate::expr::Symbol;
use crate::verify::{ProofStep, proof_steps};

/// The typecode `set.mm`, `iset.mm`, `hol.mm`, `nf.mm` and `ql.mm` all use for
/// "this is provable", as opposed to "this is well-formed syntax".
pub const PROVABLE_TYPECODE: &str = "|-";

/// What job a `$a` statement does.
///
/// Only [`Syntax`](Self::Syntax) is decided structurally; see the module docs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AxiomRole {
    /// A grammar production: the conclusion's typecode is not the provable
    /// typecode. Structural, and the one classification a database cannot get
    /// wrong.
    Syntax,
    /// A logical assumption, per the naming convention in force.
    Axiom,
    /// A definition, per the naming convention in force. Eliminable in
    /// principle; that it is *actually* conservative is a separate question
    /// this module does not answer.
    Definition,
    /// A logical `$a` no convention claims. Neither an axiom nor a definition
    /// as far as anything checkable goes — and therefore the interesting case,
    /// because it is an assumption nobody has accounted for.
    Unclassified,
}

impl std::fmt::Display for AxiomRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Syntax => "syntax constructor",
            Self::Axiom => "axiom",
            Self::Definition => "definition",
            Self::Unclassified => "unclassified assertion",
        })
    }
}

/// The naming conventions a database follows, for the part of the
/// classification that has no structural test.
///
/// [`Default`] is the `set.mm` family's (`ax-` and `df-`). It is a *default*
/// and not a rule: `miu.mm` and `peano.mm` follow neither prefix, and under
/// these conventions every one of their logical `$a` is
/// [`AxiomRole::Unclassified`] — which is the honest answer, not a failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Conventions {
    /// The typecode that means "provable". Everything else is syntax.
    pub provable_typecode: Symbol,
    /// Label prefixes marking a logical axiom.
    pub axiom_prefixes: Vec<Symbol>,
    /// Label prefixes marking a definition.
    pub definition_prefixes: Vec<Symbol>,
}

impl Default for Conventions {
    fn default() -> Self {
        Self {
            provable_typecode: Symbol::from(PROVABLE_TYPECODE),
            axiom_prefixes: vec![Symbol::from("ax-")],
            definition_prefixes: vec![Symbol::from("df-")],
        }
    }
}

impl Conventions {
    /// Only the structural split: every logical `$a` is
    /// [`AxiomRole::Unclassified`].
    ///
    /// The right choice for a database whose naming is unknown, and the
    /// baseline any convention is an improvement on.
    #[must_use]
    pub fn structural() -> Self {
        Self {
            provable_typecode: Symbol::from(PROVABLE_TYPECODE),
            axiom_prefixes: Vec::new(),
            definition_prefixes: Vec::new(),
        }
    }

    /// Whether `typecode` is this database's provable typecode.
    #[must_use]
    pub fn is_provable(&self, typecode: &str) -> bool {
        typecode == self.provable_typecode
    }

    /// The role of a `$a` with this conclusion typecode and label.
    ///
    /// A label matching both an axiom and a definition prefix is an
    /// [`AxiomRole::Axiom`]; no shipped convention has overlapping prefixes.
    #[must_use]
    pub fn role_of(&self, typecode: &str, label: &str) -> AxiomRole {
        if !self.is_provable(typecode) {
            return AxiomRole::Syntax;
        }
        let matches = |ps: &[Symbol]| ps.iter().any(|p| label.starts_with(p.as_str()));
        if matches(&self.axiom_prefixes) {
            AxiomRole::Axiom
        } else if matches(&self.definition_prefixes) {
            AxiomRole::Definition
        } else {
            AxiomRole::Unclassified
        }
    }
}

/// The role of the `$a` named `label`, or `None` when `label` does not name a
/// `$a` of `db` — a `$p` theorem, a hypothesis, or nothing at all.
#[must_use]
pub fn classify(db: &Database, label: &str, conventions: &Conventions) -> Option<AxiomRole> {
    match db.statement_by_label(label) {
        Some(Statement::Assert(a)) if a.proof.is_none() => {
            Some(conventions.role_of(a.conclusion.typecode(), &a.label))
        }
        _ => None,
    }
}

/// The assertions `assertion`'s proof cites, in first-citation order and
/// without repeats.
///
/// `$f` and `$e` steps are dropped (see the module docs), as are heap and save
/// steps, which address earlier stack entries rather than statements. An axiom
/// cites nothing.
///
/// # Errors
///
/// Returns an error when a compressed proof does not decode, or when a step
/// names a label the database does not declare
/// ([`MmError::UnknownLabel`]).
pub fn direct_citations<'db>(
    db: &'db Database,
    assertion: &Assertion,
) -> Result<Vec<&'db str>, MmError> {
    let steps = proof_steps(db, assertion)?;
    let mut out: Vec<&str> = Vec::new();
    let mut seen: FnvHashSet<&str> = FnvHashSet::default();
    for step in &steps {
        let ProofStep::Label(label) = step else {
            continue;
        };
        let Some(statement) = db.statement_by_label(label) else {
            return Err(MmError::UnknownLabel {
                theorem: assertion.label.clone(),
                label: label.clone(),
            });
        };
        let Statement::Assert(cited) = statement else {
            continue;
        };
        if seen.insert(cited.label.as_str()) {
            out.push(cited.label.as_str());
        }
    }
    Ok(out)
}

/// Every assertion `assertion`'s proof transitively cites, sorted by label.
///
/// `assertion` itself is not included: it depends on what it cites, not on
/// itself. An axiom depends on nothing.
///
/// # Errors
///
/// As [`direct_citations`], for `assertion` and every assertion reachable from
/// it.
pub fn dependencies<'db>(
    db: &'db Database,
    assertion: &Assertion,
) -> Result<Vec<&'db str>, MmError> {
    let mut reached: FnvHashSet<&str> = FnvHashSet::default();
    let mut stack = direct_citations(db, assertion)?;
    for label in &stack {
        reached.insert(*label);
    }
    while let Some(label) = stack.pop() {
        let Some(Statement::Assert(cited)) = db.statement_by_label(label) else {
            continue;
        };
        for next in direct_citations(db, cited)? {
            if reached.insert(next) {
                stack.push(next);
            }
        }
    }
    let mut out: Vec<&str> = reached.into_iter().collect();
    out.sort_unstable();
    Ok(out)
}

/// Every `$a` `assertion` rests on, sorted by label — syntax constructors and
/// definitions included.
///
/// Nothing is filtered: use [`classify`] to split the answer by
/// [`AxiomRole`], or [`AxiomIndex`] when the question is about a whole
/// database rather than one theorem. An axiom rests on itself.
///
/// # Errors
///
/// As [`dependencies`].
pub fn axioms<'db>(db: &'db Database, assertion: &Assertion) -> Result<Vec<&'db str>, MmError> {
    if assertion.proof.is_none() {
        // Borrow the database's copy of the label, not the caller's assertion:
        // the return type outlives `assertion`.
        return Ok(match db.statement_by_label(&assertion.label) {
            Some(Statement::Assert(own)) => vec![own.label.as_str()],
            _ => Vec::new(),
        });
    }
    let mut out = dependencies(db, assertion)?;
    out.retain(|label| {
        matches!(db.statement_by_label(label), Some(Statement::Assert(a)) if a.proof.is_none())
    });
    Ok(out)
}

/// Every assertion's axiom set, computed in one forward pass over the
/// database.
///
/// The per-theorem [`axioms`] walk is linear in the reachable sub-database and
/// shares nothing between calls; asking it for all 47,678 `set.mm` theorems
/// re-walks the same interior repeatedly. This computes every answer at once
/// (see the module docs for why source order makes that a single sweep) and
/// stores each as a dense bitset over the database's `$a`, which is what keeps
/// it affordable: `set.mm` has 3,008 `$a` and 50,686 assertions, so the whole
/// index is 50,686 × 376 bytes ≈ 19 MB. The transitive *dependency* sets are
/// an order of magnitude larger and are deliberately not stored — that query
/// stays a per-call walk.
///
/// The index borrows the database and holds no interior mutability, so it is a
/// caller-owned cache rather than a field of [`Database`]: `verify_all` takes
/// `&Database` and wants to stay `Sync`.
#[derive(Debug, Clone)]
pub struct AxiomIndex<'db> {
    /// Every `$a` label in source order. Position in this vector is the bit
    /// position in `bits`.
    axiom_labels: Vec<&'db str>,
    /// Assertion label → its row index in `bits`.
    rows: FnvHashMap<&'db str, usize>,
    /// `rows.len() * words` bitset words, row-major.
    bits: Vec<u64>,
    /// Bitset words per row.
    words: usize,
}

impl<'db> AxiomIndex<'db> {
    /// Build the index.
    ///
    /// # Errors
    ///
    /// As [`direct_citations`] for any assertion, plus
    /// [`MmError::ForwardReference`] when a proof cites an assertion that does
    /// not come earlier in the database — the property that makes the single
    /// forward pass valid, checked rather than assumed.
    pub fn build(db: &'db Database) -> Result<Self, MmError> {
        let axiom_labels: Vec<&str> = db
            .assertions()
            .filter(|a| a.proof.is_none())
            .map(|a| a.label.as_str())
            .collect();
        let axiom_bit: FnvHashMap<&str, usize> = axiom_labels
            .iter()
            .enumerate()
            .map(|(bit, label)| (*label, bit))
            .collect();

        let words = axiom_labels.len().div_ceil(u64::BITS as usize);
        let assertion_count = db.assertions().count();
        let mut bits = vec![0_u64; assertion_count * words];
        let mut rows: FnvHashMap<&str, usize> =
            FnvHashMap::with_capacity_and_hasher(assertion_count, <_>::default());

        for (row, assertion) in db.assertions().enumerate() {
            let start = row * words;
            if assertion.proof.is_none() {
                if let Some(&bit) = axiom_bit.get(assertion.label.as_str()) {
                    bits[start + bit / 64] |= 1 << (bit % 64);
                }
            } else {
                for cited in direct_citations(db, assertion)? {
                    let &source = rows.get(cited).ok_or_else(|| MmError::ForwardReference {
                        theorem: assertion.label.clone(),
                        label: cited.to_owned(),
                    })?;
                    // `source < row` always, so the source row is fully
                    // computed and the split is well defined.
                    let (earlier, current) = bits.split_at_mut(start);
                    let from = &earlier[source * words..source * words + words];
                    for (into, word) in current[..words].iter_mut().zip(from) {
                        *into |= *word;
                    }
                }
            }
            rows.insert(assertion.label.as_str(), row);
        }

        Ok(Self {
            axiom_labels,
            rows,
            bits,
            words,
        })
    }

    /// Every `$a` label in the database, in source order — the universe the
    /// answers range over.
    #[must_use]
    pub fn axiom_labels(&self) -> &[&'db str] {
        &self.axiom_labels
    }

    /// The `$a` labels `label` rests on, in source order, or `None` when
    /// `label` does not name an assertion of the database.
    ///
    /// Agrees with [`axioms`] as a set; the order differs (source, not
    /// alphabetical).
    #[must_use]
    pub fn axioms(&self, label: &str) -> Option<impl Iterator<Item = &'db str> + '_> {
        let &row = self.rows.get(label)?;
        let start = row * self.words;
        let row_bits = &self.bits[start..start + self.words];
        Some(
            self.axiom_labels
                .iter()
                .enumerate()
                .filter_map(move |(bit, name)| {
                    (row_bits[bit / 64] & (1 << (bit % 64)) != 0).then_some(*name)
                }),
        )
    }

    /// The `$a` labels `label` rests on whose role passes `keep`.
    ///
    /// The usual call is `logical_axioms`-style filtering: pass a closure
    /// rejecting [`AxiomRole::Syntax`], which is roughly half of `set.mm`'s
    /// `$a` and none of its content.
    #[must_use]
    pub fn axioms_where<'index>(
        &'index self,
        db: &'db Database,
        label: &str,
        conventions: &'index Conventions,
        keep: impl Fn(AxiomRole) -> bool + 'index,
    ) -> Option<impl Iterator<Item = (&'db str, AxiomRole)> + 'index> {
        Some(self.axioms(label)?.filter_map(move |name| {
            let role = classify(db, name, conventions)?;
            keep(role).then_some((name, role))
        }))
    }

    /// Whether `label` rests on `axiom`. `false` when either is unknown.
    #[must_use]
    pub fn rests_on(&self, label: &str, axiom: &str) -> bool {
        let Some(&row) = self.rows.get(label) else {
            return false;
        };
        let Some(bit) = self.axiom_labels.iter().position(|name| *name == axiom) else {
            return false;
        };
        self.bits[row * self.words + bit / 64] & (1 << (bit % 64)) != 0
    }

    /// The number of assertions indexed.
    #[must_use]
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Whether the database has no assertions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::{AxiomIndex, AxiomRole, Conventions, axioms, classify, dependencies};
    use crate::database::Statement;
    use crate::parse::parse;
    use crate::verify::verify_all;

    /// Propositional calculus in the `set.mm` naming style: three syntax
    /// constructors (one of them unused), two axioms, one definition, and two
    /// theorems, the second citing the first. Every proof verifies, so the
    /// citation edges are the ones a checker would accept.
    const PROP: &str = r"
        $c wff |- ( ) -> -. T. $.
        $v ph ps $.
        wph $f wff ph $.
        wps $f wff ps $.
        wi $a wff ( ph -> ps ) $.
        wn $a wff -. ph $.
        wtru $a wff T. $.
        ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
        ${
            min $e |- ph $.
            maj $e |- ( ph -> ps ) $.
            ax-mp $a |- ps $.
        $}
        df-tru $a |- T. $.
        truimp $p |- ( ph -> T. ) $=
            wtru wph wtru wi df-tru wtru wph ax-1 ax-mp $.
        truimp2 $p |- ( ps -> ( ph -> T. ) ) $=
            wph wtru wi wps wph wtru wi wi wph truimp
            wph wtru wi wps ax-1 ax-mp $.
    ";

    fn assertion<'a>(db: &'a crate::Database, label: &str) -> &'a crate::Assertion {
        match db.statement_by_label(label) {
            Some(Statement::Assert(a)) => a,
            _ => panic!("{label} is not an assertion"),
        }
    }

    #[test]
    fn the_fixture_verifies() {
        let db = parse(PROP).unwrap();
        assert_eq!(verify_all(&db).unwrap(), 2);
    }

    #[test]
    fn classification_splits_syntax_structurally_and_the_rest_nominally() {
        let db = parse(PROP).unwrap();
        let c = Conventions::default();
        assert_eq!(classify(&db, "wi", &c), Some(AxiomRole::Syntax));
        assert_eq!(classify(&db, "ax-1", &c), Some(AxiomRole::Axiom));
        assert_eq!(classify(&db, "df-tru", &c), Some(AxiomRole::Definition));
        // `$p` theorems and hypotheses are not `$a` at all.
        assert_eq!(classify(&db, "truimp", &c), None);
        assert_eq!(classify(&db, "wph", &c), None);
        assert_eq!(classify(&db, "min", &c), None);
        assert_eq!(classify(&db, "nonesuch", &c), None);
    }

    #[test]
    fn a_logical_axiom_matching_no_convention_is_reported_not_dropped() {
        // `miu.mm` and `peano.mm` shape: a logical `$a` with neither prefix.
        let db = parse(
            r"
            $c wff |- I $.
            wI $a wff I $.
            theIaxiom $a |- I $.
        ",
        )
        .unwrap();
        let c = Conventions::default();
        assert_eq!(classify(&db, "wI", &c), Some(AxiomRole::Syntax));
        assert_eq!(
            classify(&db, "theIaxiom", &c),
            Some(AxiomRole::Unclassified),
            "a logical $a matching no prefix must surface, not vanish"
        );
    }

    #[test]
    fn structural_conventions_claim_nothing_beyond_the_typecode() {
        let db = parse(PROP).unwrap();
        let c = Conventions::structural();
        assert_eq!(classify(&db, "wi", &c), Some(AxiomRole::Syntax));
        assert_eq!(classify(&db, "ax-1", &c), Some(AxiomRole::Unclassified));
        assert_eq!(classify(&db, "df-tru", &c), Some(AxiomRole::Unclassified));
    }

    #[test]
    fn dependencies_drop_hypotheses_and_exclude_the_theorem_itself() {
        let db = parse(PROP).unwrap();
        assert_eq!(
            dependencies(&db, assertion(&db, "truimp")).unwrap(),
            ["ax-1", "ax-mp", "df-tru", "wi", "wtru"],
            "the `min`/`maj` $e steps and the `wph` $f steps are the theorem\'s \
             own parameters, not dependencies"
        );
        assert!(
            dependencies(&db, assertion(&db, "ax-1"))
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn an_axiom_rests_on_itself_and_nothing_else() {
        let db = parse(PROP).unwrap();
        assert_eq!(axioms(&db, assertion(&db, "ax-1")).unwrap(), ["ax-1"]);
        assert_eq!(axioms(&db, assertion(&db, "wi")).unwrap(), ["wi"]);
    }

    #[test]
    fn axioms_keep_syntax_constructors_for_the_caller_to_filter() {
        let db = parse(PROP).unwrap();
        let c = Conventions::default();
        let used = axioms(&db, assertion(&db, "truimp")).unwrap();
        assert_eq!(used, ["ax-1", "ax-mp", "df-tru", "wi", "wtru"]);
        let logical: Vec<_> = used
            .iter()
            .filter(|l| classify(&db, l, &c) != Some(AxiomRole::Syntax))
            .copied()
            .collect();
        assert_eq!(logical, ["ax-1", "ax-mp", "df-tru"]);
    }

    #[test]
    fn transitivity_reaches_through_an_intermediate_theorem() {
        let db = parse(PROP).unwrap();
        // `truimp2` cites `truimp`, which is where `df-tru` enters.
        assert_eq!(
            dependencies(&db, assertion(&db, "truimp2")).unwrap(),
            ["ax-1", "ax-mp", "df-tru", "truimp", "wi", "wtru"]
        );
        assert_eq!(
            axioms(&db, assertion(&db, "truimp2")).unwrap(),
            ["ax-1", "ax-mp", "df-tru", "wi", "wtru"],
            "the intermediate $p drops out; only the $a it rests on remain"
        );
    }

    #[test]
    fn the_index_agrees_with_the_per_theorem_walk_on_every_assertion() {
        let db = parse(PROP).unwrap();
        verify_all(&db).unwrap();
        let index = AxiomIndex::build(&db).unwrap();
        assert_eq!(index.len(), 8);
        assert_eq!(
            index.axiom_labels(),
            ["wi", "wn", "wtru", "ax-1", "ax-mp", "df-tru"]
        );

        for a in db.assertions() {
            let mut walked = axioms(&db, a).unwrap();
            let mut indexed: Vec<&str> = index.axioms(&a.label).unwrap().collect();
            walked.sort_unstable();
            indexed.sort_unstable();
            assert_eq!(walked, indexed, "disagreement on {}", a.label);
        }
        assert!(index.rests_on("truimp2", "df-tru"));
        assert!(
            !index.rests_on("truimp2", "wn"),
            "the unused syntax constructor is under nothing"
        );
        assert!(!index.rests_on("nonesuch", "wi"));
        assert!(!index.rests_on("truimp2", "nonesuch"));
    }

    #[test]
    fn the_index_filters_by_role() {
        let db = parse(PROP).unwrap();
        let index = AxiomIndex::build(&db).unwrap();
        let c = Conventions::default();
        let logical: Vec<_> = index
            .axioms_where(&db, "truimp2", &c, |role| role != AxiomRole::Syntax)
            .unwrap()
            .collect();
        assert_eq!(
            logical,
            [
                ("ax-1", AxiomRole::Axiom),
                ("ax-mp", AxiomRole::Axiom),
                ("df-tru", AxiomRole::Definition),
            ],
            "source order, not alphabetical"
        );
    }

    #[test]
    fn a_forward_citation_is_refused_rather_than_swept_past() {
        // `verify_all` rejects this too; the index must not depend on having
        // been run after it.
        let db = parse(
            r"
            $c wff |- I $.
            wI $a wff I $.
            loop $p |- I $= loop $.
        ",
        )
        .unwrap();
        assert!(verify_all(&db).is_err());
        assert!(matches!(
            AxiomIndex::build(&db),
            Err(crate::MmError::ForwardReference { .. })
        ));
    }
}
