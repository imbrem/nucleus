//! Seeds the propositional init database for the HOL kernel.
//!
//! The init database is an ordinary kernel-state image whose `init`
//! namespace exports the standard propositional connectives as interned
//! closed terms. Nothing here is trusted: every object is built through
//! the kernel view and type-checked before export, and regenerating the
//! image reconstructs the same logical content from this source.
//!
//! # Mapping onto the kernel's primitives
//!
//! This kernel differs from textbook HOL Light in what is primitive, so
//! the classic definitions adapt as follows (see `hol/semantics.txt`):
//!
//! - `true` and `false` are the primitive Boolean literals `TM_BOOL 1`
//!   and `TM_BOOL 0`; they are exported as terms rather than defined via
//!   `(λp. p) = (λp. p)` or `∀p. p`. The primitive `false` literal *is*
//!   the canonical falsehood: the kernel's own `not` abbreviation is
//!   `not t := (t = false)`.
//! - Equality is a term former (`TM_EQ`), not a constant, and universal
//!   quantification is the standard equational abbreviation
//!   `∀x:A. P x := (P = λx:A. true)` over it.
//! - `not`, `and`, `imp`, `or`, and (Boolean) `forall` are genuinely
//!   derived and exported here as closed lambda terms:
//!   - `not := λp. p = false`
//!   - `and := λp q. (λf. f p q) = (λf. f true true)` with
//!     `f : bool → bool → bool`
//!   - `imp := λp q. (and p q) = p`
//!   - `or := λp q. ∀r. (imp (imp p r) (imp (imp q r) r))`, spelled with
//!     the `forall` abbreviation and applications of the exported
//!     constants
//!   - `forall := λP:bool → bool. P = (λx:bool. true)`
//!
//! Regeneration is checked at the level of logical content (structural
//! identity of the exported trees), not image bytes: the verification
//! primitive for distributing an init image is content-hash equality of
//! the artifact itself, and a byte-level mismatch means a different
//! artifact, not an invalid one.

use covalence_lib_error::snafu::Snafu;
use covalence_neutron::Bytes;
use covalence_nucleus::Connection;
use covalence_nucleus::hol::{
    AllowAll, ExportTarget, Hol, HolError, HolImageError, HolView, Policy, TermId, Tm, Ty,
};

/// The namespace under which the connectives are exported.
pub const NAMESPACE: &str = "init";

/// Export names inside [`NAMESPACE`], in stable positional order.
pub mod name {
    /// The primitive `true` literal.
    pub const TRUE: &str = "true";
    /// The primitive `false` literal.
    pub const FALSE: &str = "false";
    /// `not := λp. p = false`.
    pub const NOT: &str = "not";
    /// `and := λp q. (λf. f p q) = (λf. f true true)`.
    pub const AND: &str = "and";
    /// `imp := λp q. (and p q) = p`.
    pub const IMP: &str = "imp";
    /// `or := λp q. ∀r. (p → r) → (q → r) → r`.
    pub const OR: &str = "or";
    /// `forall := λP. P = (λx:bool. true)`, the Boolean instance.
    pub const FORALL: &str = "forall";
}

/// All export names in stable positional order.
pub const NAMES: [&str; 7] = [
    name::TRUE,
    name::FALSE,
    name::NOT,
    name::AND,
    name::IMP,
    name::OR,
    name::FORALL,
];

/// The interned propositional constants of one seeded database.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InitTerms<'v> {
    /// The primitive `true` literal.
    pub truth: TermId<'v>,
    /// The primitive `false` literal.
    pub falsity: TermId<'v>,
    /// The `not` connective.
    pub not: TermId<'v>,
    /// The `and` connective.
    pub and: TermId<'v>,
    /// The `imp` connective.
    pub imp: TermId<'v>,
    /// The `or` connective.
    pub or: TermId<'v>,
    /// The Boolean `forall` combinator.
    pub forall: TermId<'v>,
}

impl<'v> InitTerms<'v> {
    /// Lists the constants in stable export order, parallel to [`NAMES`].
    #[must_use]
    pub const fn in_export_order(&self) -> [TermId<'v>; 7] {
        [
            self.truth,
            self.falsity,
            self.not,
            self.and,
            self.imp,
            self.or,
            self.forall,
        ]
    }
}

/// Interns the propositional connectives and exports them under
/// [`NAMESPACE`].
///
/// Seeding is idempotent: repeating it on an already seeded database
/// resolves to the identical objects and positions. Every constant is
/// type-checked in the empty context before it is exported.
///
/// # Errors
///
/// Fails if the policy refuses interning or exporting, a constant fails
/// to type-check, an export name already names a different object, or
/// storage fails.
pub fn seed<'v, P: Policy>(hol: &HolView<'v, P>) -> Result<InitTerms<'v>, HolError> {
    let terms = intern_connectives(hol)?;
    for term in terms.in_export_order() {
        hol.type_of(hol.empty_kinds(), hol.empty_vars(), term)?;
    }
    let namespace = hol.namespace(NAMESPACE)?;
    for (export_name, term) in NAMES.iter().zip(terms.in_export_order()) {
        hol.export(namespace, export_name, ExportTarget::Term(term))?;
    }
    Ok(terms)
}

/// Resolves a previously seeded database's connectives by name.
///
/// # Errors
///
/// Fails if the policy refuses reads, the `init` namespace or one of its
/// exports is missing, or an export is not a term.
pub fn resolve<'v, P: Policy>(hol: &HolView<'v, P>) -> Result<InitTerms<'v>, HolError> {
    let namespace = hol
        .find_namespace(NAMESPACE)?
        .ok_or(HolError::UnknownExport {
            name: NAMESPACE.to_owned(),
        })?;
    let mut resolved = [None; 7];
    for (slot, export_name) in resolved.iter_mut().zip(NAMES) {
        *slot = Some(
            hol.resolve_export(namespace, export_name)?
                .as_term()
                .ok_or(HolError::UnknownExport {
                    name: export_name.to_owned(),
                })?,
        );
    }
    let [truth, falsity, not, and, imp, or, forall] = resolved.map(Option::unwrap);
    Ok(InitTerms {
        truth,
        falsity,
        not,
        and,
        imp,
        or,
        forall,
    })
}

/// Builds the connectives as interned closed terms.
fn intern_connectives<'v, P: Policy>(hol: &HolView<'v, P>) -> Result<InitTerms<'v>, HolError> {
    let bool_ty = hol.ty(Ty::Bool)?;
    let bool_bool = hol.ty(Ty::Arr(bool_ty, bool_ty))?;
    let selector_ty = hol.ty(Ty::Arr(bool_ty, bool_bool))?;
    let truth = hol.tm(Tm::Bool(true))?;
    let falsity = hol.tm(Tm::Bool(false))?;
    let bv0 = hol.tm(Tm::Bv(0))?;
    let bv1 = hol.tm(Tm::Bv(1))?;
    let bv2 = hol.tm(Tm::Bv(2))?;

    // not := λp. p = false
    let not = hol.tm(Tm::Lam(bool_ty, hol.tm(Tm::Eq(bv0, falsity))?))?;

    // and := λp q. (λf. f p q) = (λf. f true true); under the selector
    // binder p and q sit at indices 2 and 1.
    let picked = hol.tm(Tm::App(hol.tm(Tm::App(bv0, bv2))?, bv1))?;
    let picked_true = hol.tm(Tm::App(hol.tm(Tm::App(bv0, truth))?, truth))?;
    let and_body = hol.tm(Tm::Eq(
        hol.tm(Tm::Lam(selector_ty, picked))?,
        hol.tm(Tm::Lam(selector_ty, picked_true))?,
    ))?;
    let and = hol.tm(Tm::Lam(bool_ty, hol.tm(Tm::Lam(bool_ty, and_body))?))?;

    // imp := λp q. (and p q) = p
    let and_pq = hol.tm(Tm::App(hol.tm(Tm::App(and, bv1))?, bv0))?;
    let imp_body = hol.tm(Tm::Eq(and_pq, bv1))?;
    let imp = hol.tm(Tm::Lam(bool_ty, hol.tm(Tm::Lam(bool_ty, imp_body))?))?;

    // or := λp q. ∀r. (p → r) → (q → r) → r, with the quantifier spelled
    // as the equational abbreviation and the arrows as applications of
    // `imp`; under the r binder p and q sit at indices 2 and 1.
    let imp_app = |antecedent: TermId<'v>, consequent: TermId<'v>| {
        hol.tm(Tm::App(hol.tm(Tm::App(imp, antecedent))?, consequent))
    };
    let p_implies_r = imp_app(bv2, bv0)?;
    let q_implies_r = imp_app(bv1, bv0)?;
    let chain = imp_app(p_implies_r, imp_app(q_implies_r, bv0)?)?;
    let or_body = hol.tm(Tm::Eq(
        hol.tm(Tm::Lam(bool_ty, chain))?,
        hol.tm(Tm::Lam(bool_ty, truth))?,
    ))?;
    let or = hol.tm(Tm::Lam(bool_ty, hol.tm(Tm::Lam(bool_ty, or_body))?))?;

    // forall := λP. P = (λx:bool. true)
    let forall_body = hol.tm(Tm::Eq(bv0, hol.tm(Tm::Lam(bool_ty, truth))?))?;
    let forall = hol.tm(Tm::Lam(bool_bool, forall_body))?;

    Ok(InitTerms {
        truth,
        falsity,
        not,
        and,
        imp,
        or,
        forall,
    })
}

/// Generates the init image: a fresh kernel-state database, seeded and
/// serialized whole.
///
/// # Errors
///
/// Fails if the kernel-state database cannot be opened, seeded, or
/// serialized.
pub fn init_image() -> Result<Bytes, InitError> {
    let connection = Connection::<Hol<AllowAll>>::open_hol_in_memory(AllowAll)?;
    seed(&connection.view())?;
    Ok(connection.serialize_image()?)
}

/// Failure to generate the init image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum InitError {
    /// The kernel-state database could not be opened.
    #[snafu(display("cannot open the kernel-state database"), context(false))]
    Open {
        /// Underlying open failure.
        source: covalence_nucleus::hol::HolOpenError,
    },
    /// A connective could not be interned or exported.
    #[snafu(display("cannot seed the propositional connectives"), context(false))]
    Seed {
        /// Underlying kernel-view failure.
        source: HolError,
    },
    /// The seeded database could not be serialized.
    #[snafu(display("cannot serialize the init image"), context(false))]
    Image {
        /// Underlying image failure.
        source: HolImageError,
    },
}

#[cfg(test)]
mod tests {
    use covalence_nucleus::hol::{Kind, Ty};

    use super::*;

    fn open() -> Connection<Hol<AllowAll>> {
        Connection::open_hol_in_memory(AllowAll).expect("open kernel-state database")
    }

    #[test]
    fn seeding_type_checks_every_connective() {
        let connection = open();
        let hol = connection.view();
        let terms = seed(&hol).expect("seed");
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let bool_bool = hol.ty(Ty::Arr(bool_ty, bool_ty)).expect("bool -> bool");
        let binary = hol.ty(Ty::Arr(bool_ty, bool_bool)).expect("binary");
        let quantifier = hol.ty(Ty::Arr(bool_bool, bool_ty)).expect("quantifier");
        let type_of = |term| {
            hol.type_of(hol.empty_kinds(), hol.empty_vars(), term)
                .expect("type")
        };
        assert_eq!(type_of(terms.truth), bool_ty);
        assert_eq!(type_of(terms.falsity), bool_ty);
        assert_eq!(type_of(terms.not), bool_bool);
        assert_eq!(type_of(terms.and), binary);
        assert_eq!(type_of(terms.imp), binary);
        assert_eq!(type_of(terms.or), binary);
        assert_eq!(type_of(terms.forall), quantifier);
    }

    #[test]
    fn seeding_is_idempotent_and_exports_resolve() {
        let connection = open();
        let hol = connection.view();
        let first = seed(&hol).expect("seed");
        let second = seed(&hol).expect("seed again");
        assert_eq!(first, second);
        assert_eq!(resolve(&hol).expect("resolve"), first);

        let namespace = hol
            .find_namespace(NAMESPACE)
            .expect("query")
            .expect("namespace");
        for (position, term) in first.in_export_order().iter().enumerate() {
            let export = hol
                .export_at(namespace, u32::try_from(position).expect("position"))
                .expect("positional export");
            assert_eq!(export.as_term(), Some(*term));
        }
    }

    #[test]
    fn regeneration_reconstructs_identical_logical_content() {
        // Two independently seeded databases agree object by object:
        // interning the first database's trees into the second lands on
        // exactly the ids the second database exported. This checks the
        // logical artifact, not image bytes; distributing an image pins
        // bytes by content hash instead.
        let first = open();
        let second = open();
        let first_terms = seed(&first.view()).expect("seed first");
        let second_terms = seed(&second.view()).expect("seed second");
        let first_hol = first.view();
        let second_hol = second.view();
        for (from, into) in first_terms
            .in_export_order()
            .iter()
            .zip(second_terms.in_export_order())
        {
            let tree = first_hol.load_tm(*from).expect("load");
            assert_eq!(second_hol.intern_tm(&tree).expect("intern"), into);
        }
    }

    #[test]
    fn init_image_round_trips_through_the_kernel() {
        let bytes = init_image().expect("generate");
        let connection =
            Connection::<Hol<AllowAll>>::open_hol_image(&bytes, AllowAll).expect("open image");
        let hol = connection.view();
        let terms = resolve(&hol).expect("resolve");
        // The image stays a live kernel state: proof steps work on top.
        hol.proof_step(covalence_nucleus::hol::rules::Truth {
            kinds: hol.empty_kinds(),
            vars: hol.empty_vars(),
        })
        .expect("prove truth");
        assert_eq!(
            hol.tm_node(terms.truth).expect("node"),
            Tm::Bool(true),
            "true resolves to the primitive literal"
        );
        let _ = hol.kind(Kind::Star).expect("kernel stays writable");
    }
}
