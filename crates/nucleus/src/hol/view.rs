//! The borrowing kernel view: interning, node readers, and spines.
//!
//! A [`HolView`] shares its connection (`&self` throughout) and produces
//! branded ids that cannot outlive it. Ids constructed by this view are
//! guaranteed present and sort-correct for its whole lifetime, because
//! exclusive maintenance (future garbage collection) requires `&mut`
//! access to the connection and is therefore impossible while a view is
//! alive. Raw integers re-enter only through the checked `*_from_raw`
//! operations. Prepared statements are cached in the underlying
//! connection's statement cache, so preparation is lazy and shared.

use covalence_lib_error::snafu::{OptionExt, ResultExt, Snafu};
use covalence_lib_sqlite::{self as sqlite, OptionalExtension};

use super::syntax::{
    HypsId, Ids, Kind, KindId, KindsId, Sort, SourceId, TermId, Tm, Ty, TypeId, VarsId,
    sort_of_tag, tag,
};
use super::{Hol, Operation, Policy};
use crate::Connection;

/// Failure of a kernel-view operation.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu), visibility(pub(crate)))]
pub enum HolError {
    /// The connection policy refused the operation.
    #[snafu(display("policy refused {operation:?}"))]
    PolicyDenied {
        /// The refused operation.
        operation: Operation,
    },
    /// A raw id does not name a row in this store.
    #[snafu(display("id {raw} is not present in this store"))]
    UnknownId {
        /// The offending raw id.
        raw: i64,
    },
    /// A raw id names a row of the wrong sort.
    #[snafu(display("id {raw} has sort {found:?}, expected {expected:?}"))]
    SortMismatch {
        /// The offending raw id.
        raw: i64,
        /// The sort required by the operation.
        expected: Sort,
        /// The sort actually stored.
        found: Sort,
    },
    /// A stored row carries a tag outside the semantic vocabulary.
    #[snafu(display("row {raw} carries unknown tag {tag}"))]
    UnknownTag {
        /// The offending raw id.
        raw: i64,
        /// The unknown tag value.
        tag: i64,
    },
    /// A source reference does not name a registered `hol_source` row.
    #[snafu(display("source {raw} is not registered in this store"))]
    UnknownSource {
        /// The offending raw source id.
        raw: i64,
    },
    /// A stored payload is outside its documented range.
    #[snafu(display("row {raw} carries a malformed payload"))]
    MalformedPayload {
        /// The offending raw id.
        raw: i64,
    },
    /// A de Bruijn index escapes its context.
    #[snafu(display("variable {index} is unbound in this context"))]
    UnboundVariable {
        /// The offending index.
        index: u32,
    },
    /// Two types that must coincide differ.
    #[snafu(display("type mismatch"))]
    TypeMismatch,
    /// Two kinds that must coincide differ.
    #[snafu(display("kind mismatch"))]
    KindMismatch,
    /// A conclusion or hypothesis is not Boolean.
    #[snafu(display("term is not Boolean"))]
    NotBoolean,
    /// A premise conclusion is not an equality node.
    #[snafu(display("conclusion is not an equality"))]
    NotAnEquality,
    /// A premise conclusion is not an application node.
    #[snafu(display("conclusion is not an application"))]
    NotAnApplication,
    /// Premises disagree on a context that must be shared.
    #[snafu(display("premise contexts disagree"))]
    ContextMismatch,
    /// A hypothesis mentions the variable being discharged.
    #[snafu(display("hypothesis mentions the bound variable"))]
    HypothesisNotStrengthenable,
    /// An instantiation vector has the wrong length.
    #[snafu(display("expected {expected} values, found {found}"))]
    ArityMismatch {
        /// Required number of values.
        expected: usize,
        /// Supplied number of values.
        found: usize,
    },
    /// Syntax exceeds the expansion depth bound.
    #[snafu(display("syntax exceeds the maximum expansion depth"))]
    DepthExceeded,
    /// The underlying storage failed.
    #[snafu(display("kernel storage failure"))]
    Storage {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },
}

/// A borrowing view over a HOL kernel-state connection.
pub struct HolView<'v, P: Policy> {
    connection: &'v Connection<Hol<P>>,
}

impl<P: Policy> Connection<Hol<P>> {
    /// Opens a borrowing kernel view.
    #[must_use]
    pub fn view(&self) -> HolView<'_, P> {
        HolView { connection: self }
    }
}

impl<'v, P: Policy> HolView<'v, P> {
    fn sqlite(&self) -> &sqlite::Connection {
        self.connection.parts().0.sqlite()
    }

    pub(crate) fn authorize(&self, operation: Operation) -> Result<(), HolError> {
        if self.connection.parts().1.policy.allows(operation) {
            Ok(())
        } else {
            PolicyDeniedSnafu { operation }.fail()
        }
    }

    /// Interns one object row, returning the canonical id.
    pub(crate) fn insert_object(
        &self,
        tag: i64,
        lhs: i64,
        rhs: i64,
        ty: i64,
    ) -> Result<i64, HolError> {
        self.sqlite()
            .prepare_cached(
                "INSERT INTO hol_object(tag, lhs, rhs, ty) VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(tag, lhs, rhs, ty) DO UPDATE SET tag = tag
                 RETURNING id",
            )
            .and_then(|mut statement| {
                statement.query_row((tag, lhs, rhs, ty), |row| row.get::<_, i64>(0))
            })
            .context(StorageSnafu)
    }

    /// Reads one object row.
    pub(crate) fn read_object(&self, raw: i64) -> Result<(i64, i64, i64, i64), HolError> {
        self.sqlite()
            .prepare_cached("SELECT tag, lhs, rhs, ty FROM hol_object WHERE id = ?1")
            .and_then(|mut statement| {
                statement
                    .query_row((raw,), |row| {
                        Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
                    })
                    .optional()
            })
            .context(StorageSnafu)?
            .context(UnknownIdSnafu { raw })
    }

    fn expect_sort(&self, raw: i64, expected: Sort) -> Result<(), HolError> {
        // Spine ids may be 0 (the empty spine); object ids are positive.
        if raw == 0 && matches!(expected, Sort::Kinds | Sort::Vars | Sort::Hyps) {
            return Ok(());
        }
        let (tag, ..) = self.read_object(raw)?;
        let found = sort_of_tag(tag).context(UnknownTagSnafu { raw, tag })?;
        if found == expected {
            Ok(())
        } else {
            SortMismatchSnafu {
                raw,
                expected,
                found,
            }
            .fail()
        }
    }

    // ------------------------------------------------------------------
    // Formation (interning).
    // ------------------------------------------------------------------

    /// Interns a kind node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn kind(&self, node: Kind<Ids<'v>>) -> Result<KindId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let raw = match node {
            Kind::Star => self.insert_object(tag::K_STAR, 0, 0, 0)?,
            Kind::Arr(domain, codomain) => {
                self.insert_object(tag::K_ARR, domain.raw(), codomain.raw(), 0)?
            }
        };
        Ok(KindId::new(raw))
    }

    /// Interns a type node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning, a source is unregistered, or
    /// storage fails.
    pub fn ty(&self, node: Ty<Ids<'v>>) -> Result<TypeId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let raw = match node {
            Ty::Bv(index) => self.insert_object(tag::TY_BV, i64::from(index), 0, 0)?,
            Ty::Lam(kind, body) => self.insert_object(tag::TY_LAM, body.raw(), 0, kind.raw())?,
            Ty::App(function, argument) => {
                self.insert_object(tag::TY_APP, function.raw(), argument.raw(), 0)?
            }
            Ty::All(kind, body) => self.insert_object(tag::TY_ALL, body.raw(), 0, kind.raw())?,
            Ty::Bool => self.insert_object(tag::TY_BOOL, 0, 0, 0)?,
            Ty::Arr(domain, codomain) => {
                self.insert_object(tag::TY_ARR, domain.raw(), codomain.raw(), 0)?
            }
            Ty::Sub(carrier, predicate) => {
                self.insert_object(tag::TY_SUB, predicate.raw(), 0, carrier.raw())?
            }
            Ty::Ind => self.insert_object(tag::TY_IND, 0, 0, 0)?,
            Ty::Ext(source, position) => {
                self.insert_object(tag::TY_EXT, source.raw(), i64::from(position), 0)?
            }
        };
        Ok(TypeId::new(raw))
    }

    /// Interns a term node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning, a source is unregistered, or
    /// storage fails.
    pub fn tm(&self, node: Tm<Ids<'v>>) -> Result<TermId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let raw = match node {
            Tm::Bv(index) => self.insert_object(tag::TM_BV, i64::from(index), 0, 0)?,
            Tm::App(function, argument) => {
                self.insert_object(tag::TM_APP, function.raw(), argument.raw(), 0)?
            }
            Tm::Lam(domain, body) => {
                self.insert_object(tag::TM_LAM, body.raw(), 0, domain.raw())?
            }
            Tm::TyApp(function, argument) => {
                self.insert_object(tag::TM_TYAPP, function.raw(), argument.raw(), 0)?
            }
            Tm::TyLam(kind, body) => {
                self.insert_object(tag::TM_TYLAM, body.raw(), 0, kind.raw())?
            }
            Tm::Bool(value) => self.insert_object(tag::TM_BOOL, i64::from(value), 0, 0)?,
            Tm::Eq(left, right) => self.insert_object(tag::TM_EQ, left.raw(), right.raw(), 0)?,
            Tm::Eps(predicate) => self.insert_object(tag::TM_EPS, predicate.raw(), 0, 0)?,
            Tm::Abs(predicate, value) => {
                self.insert_object(tag::TM_ABS, predicate.raw(), value.raw(), 0)?
            }
            Tm::Rep(predicate, value) => {
                self.insert_object(tag::TM_REP, predicate.raw(), value.raw(), 0)?
            }
            Tm::Ext(source, position, claim) => {
                self.insert_object(tag::TM_EXT, source.raw(), i64::from(position), claim.raw())?
            }
        };
        Ok(TermId::new(raw))
    }

    // ------------------------------------------------------------------
    // Destructors.
    // ------------------------------------------------------------------

    /// Reads a kind node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the row is malformed.
    pub fn kind_node(&self, id: KindId<'v>) -> Result<Kind<Ids<'v>>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let raw = id.raw();
        let (tag_value, lhs, rhs, _) = self.read_object(raw)?;
        match tag_value {
            tag::K_STAR => Ok(Kind::Star),
            tag::K_ARR => Ok(Kind::Arr(KindId::new(lhs), KindId::new(rhs))),
            other => UnknownTagSnafu { raw, tag: other }.fail(),
        }
    }

    /// Reads a type node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the row is malformed.
    pub fn ty_node(&self, id: TypeId<'v>) -> Result<Ty<Ids<'v>>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let raw = id.raw();
        let (tag_value, lhs, rhs, ty) = self.read_object(raw)?;
        let index =
            |value: i64| u32::try_from(value).map_err(|_| MalformedPayloadSnafu { raw }.build());
        match tag_value {
            tag::TY_BV => Ok(Ty::Bv(index(lhs)?)),
            tag::TY_LAM => Ok(Ty::Lam(KindId::new(ty), TypeId::new(lhs))),
            tag::TY_APP => Ok(Ty::App(TypeId::new(lhs), TypeId::new(rhs))),
            tag::TY_ALL => Ok(Ty::All(KindId::new(ty), TypeId::new(lhs))),
            tag::TY_BOOL => Ok(Ty::Bool),
            tag::TY_ARR => Ok(Ty::Arr(TypeId::new(lhs), TypeId::new(rhs))),
            tag::TY_SUB => Ok(Ty::Sub(TypeId::new(ty), TermId::new(lhs))),
            tag::TY_IND => Ok(Ty::Ind),
            tag::TY_EXT => Ok(Ty::Ext(SourceId::new(lhs), index(rhs)?)),
            other => UnknownTagSnafu { raw, tag: other }.fail(),
        }
    }

    /// Reads a term node.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the row is malformed.
    pub fn tm_node(&self, id: TermId<'v>) -> Result<Tm<Ids<'v>>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let raw = id.raw();
        let (tag_value, lhs, rhs, ty) = self.read_object(raw)?;
        let index =
            |value: i64| u32::try_from(value).map_err(|_| MalformedPayloadSnafu { raw }.build());
        match tag_value {
            tag::TM_BV => Ok(Tm::Bv(index(lhs)?)),
            tag::TM_APP => Ok(Tm::App(TermId::new(lhs), TermId::new(rhs))),
            tag::TM_LAM => Ok(Tm::Lam(TypeId::new(ty), TermId::new(lhs))),
            tag::TM_TYAPP => Ok(Tm::TyApp(TermId::new(lhs), TypeId::new(rhs))),
            tag::TM_TYLAM => Ok(Tm::TyLam(KindId::new(ty), TermId::new(lhs))),
            tag::TM_BOOL => match lhs {
                0 => Ok(Tm::Bool(false)),
                1 => Ok(Tm::Bool(true)),
                _ => MalformedPayloadSnafu { raw }.fail(),
            },
            tag::TM_EQ => Ok(Tm::Eq(TermId::new(lhs), TermId::new(rhs))),
            tag::TM_EPS => Ok(Tm::Eps(TermId::new(lhs))),
            tag::TM_ABS => Ok(Tm::Abs(TermId::new(lhs), TermId::new(rhs))),
            tag::TM_REP => Ok(Tm::Rep(TermId::new(lhs), TermId::new(rhs))),
            tag::TM_EXT => Ok(Tm::Ext(SourceId::new(lhs), index(rhs)?, TypeId::new(ty))),
            other => UnknownTagSnafu { raw, tag: other }.fail(),
        }
    }

    // ------------------------------------------------------------------
    // Context spines.
    // ------------------------------------------------------------------

    /// The empty kind context.
    #[must_use]
    pub const fn empty_kinds(&self) -> KindsId<'v> {
        KindsId::new(0)
    }

    /// The empty variable context.
    #[must_use]
    pub const fn empty_vars(&self) -> VarsId<'v> {
        VarsId::new(0)
    }

    /// The empty hypothesis set.
    #[must_use]
    pub const fn empty_hyps(&self) -> HypsId<'v> {
        HypsId::new(0)
    }

    /// Builds a kind-context spine; `entries[0]` is the innermost entry.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn kinds(&self, entries: &[KindId<'v>]) -> Result<KindsId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let mut spine = 0_i64;
        for entry in entries.iter().rev() {
            spine = self.insert_object(tag::KS, spine, entry.raw(), 0)?;
        }
        Ok(KindsId::new(spine))
    }

    /// Builds a variable-context spine; `entries[0]` is the innermost entry.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn vars(&self, entries: &[TypeId<'v>]) -> Result<VarsId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let mut spine = 0_i64;
        for entry in entries.iter().rev() {
            spine = self.insert_object(tag::VS, spine, entry.raw(), 0)?;
        }
        Ok(VarsId::new(spine))
    }

    /// Builds the canonical hypothesis spine for a set of propositions.
    ///
    /// Entries are deduplicated and ordered; the result is independent of
    /// input order.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses interning or storage fails.
    pub fn hyps(&self, props: &[TermId<'v>]) -> Result<HypsId<'v>, HolError> {
        self.authorize(Operation::InternSyntax)?;
        let mut raws: Vec<i64> = props.iter().map(|id| id.raw()).collect();
        raws.sort_unstable();
        raws.dedup();
        let mut spine = 0_i64;
        for raw in raws {
            spine = self.insert_object(tag::HS, spine, raw, 0)?;
        }
        Ok(HypsId::new(spine))
    }

    /// Lists a kind-context spine, innermost first.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the spine is malformed.
    pub fn kinds_entries(&self, spine: KindsId<'v>) -> Result<Vec<KindId<'v>>, HolError> {
        Ok(self
            .spine_entries(spine.raw(), tag::KS, Sort::Kinds)?
            .into_iter()
            .map(KindId::new)
            .collect())
    }

    /// Lists a variable-context spine, innermost first.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the spine is malformed.
    pub fn vars_entries(&self, spine: VarsId<'v>) -> Result<Vec<TypeId<'v>>, HolError> {
        Ok(self
            .spine_entries(spine.raw(), tag::VS, Sort::Vars)?
            .into_iter()
            .map(TypeId::new)
            .collect())
    }

    /// Lists a hypothesis spine in canonical (ascending) order.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or the spine is malformed.
    pub fn hyps_entries(&self, spine: HypsId<'v>) -> Result<Vec<TermId<'v>>, HolError> {
        let mut entries: Vec<TermId<'v>> = self
            .spine_entries(spine.raw(), tag::HS, Sort::Hyps)?
            .into_iter()
            .map(TermId::new)
            .collect();
        entries.reverse();
        Ok(entries)
    }

    fn spine_entries(&self, head: i64, spine_tag: i64, sort: Sort) -> Result<Vec<i64>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let mut entries = Vec::new();
        let mut cursor = head;
        while cursor != 0 {
            let (tag_value, parent, entry, _) = self.read_object(cursor)?;
            if tag_value != spine_tag {
                let found = sort_of_tag(tag_value).context(UnknownTagSnafu {
                    raw: cursor,
                    tag: tag_value,
                })?;
                return SortMismatchSnafu {
                    raw: cursor,
                    expected: sort,
                    found,
                }
                .fail();
            }
            entries.push(entry);
            cursor = parent;
        }
        Ok(entries)
    }

    // ------------------------------------------------------------------
    // Checked re-entry from raw integers.
    // ------------------------------------------------------------------

    /// Revalidates a raw kind id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn kind_from_raw(&self, raw: i64) -> Result<KindId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Kind)?;
        Ok(KindId::new(raw))
    }

    /// Revalidates a raw type id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn ty_from_raw(&self, raw: i64) -> Result<TypeId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Type)?;
        Ok(TypeId::new(raw))
    }

    /// Revalidates a raw term id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn tm_from_raw(&self, raw: i64) -> Result<TermId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Term)?;
        Ok(TermId::new(raw))
    }

    /// Revalidates a raw kind-context spine id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn kinds_from_raw(&self, raw: i64) -> Result<KindsId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Kinds)?;
        Ok(KindsId::new(raw))
    }

    /// Revalidates a raw variable-context spine id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn vars_from_raw(&self, raw: i64) -> Result<VarsId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Vars)?;
        Ok(VarsId::new(raw))
    }

    /// Revalidates a raw hypothesis spine id.
    ///
    /// # Errors
    ///
    /// Fails if the id is absent or names a row of another sort.
    pub fn hyps_from_raw(&self, raw: i64) -> Result<HypsId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.expect_sort(raw, Sort::Hyps)?;
        Ok(HypsId::new(raw))
    }

    /// Revalidates a raw source id against `hol_source`.
    ///
    /// # Errors
    ///
    /// Fails if no source row carries this id.
    pub fn source_from_raw(&self, raw: i64) -> Result<SourceId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let present: Option<i64> = self
            .sqlite()
            .prepare_cached("SELECT source_id FROM hol_source WHERE source_id = ?1")
            .and_then(|mut statement| statement.query_row((raw,), |row| row.get(0)).optional())
            .context(StorageSnafu)?;
        present.context(UnknownSourceSnafu { raw })?;
        Ok(SourceId::new(raw))
    }
}

#[cfg(test)]
mod tests {
    use super::super::AllowAll;
    use super::*;

    fn open() -> Connection<Hol<AllowAll>> {
        Connection::open_hol_in_memory(AllowAll).expect("open kernel-state database")
    }

    #[test]
    fn interning_is_idempotent_and_reads_back() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let identity = hol
            .tm(Tm::Bv(0))
            .and_then(|body| hol.tm(Tm::Lam(bool_ty, body)));
        let identity = identity.expect("identity");
        let again = hol
            .tm(Tm::Bv(0))
            .and_then(|body| hol.tm(Tm::Lam(bool_ty, body)))
            .expect("identity again");
        assert_eq!(identity, again);
        let node = hol.tm_node(identity).expect("read back");
        assert!(matches!(node, Tm::Lam(domain, _) if domain == bool_ty));
    }

    #[test]
    fn raw_reentry_checks_presence_and_sort() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        assert!(matches!(
            hol.tm_from_raw(bool_ty.raw()),
            Err(HolError::SortMismatch { .. })
        ));
        assert!(matches!(
            hol.ty_from_raw(9999),
            Err(HolError::UnknownId { .. })
        ));
        assert_eq!(hol.ty_from_raw(bool_ty.raw()).expect("revalidate"), bool_ty);
    }

    #[test]
    fn hypothesis_spines_are_canonical_sets() {
        let connection = open();
        let hol = connection.view();
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let falsity = hol.tm(Tm::Bool(false)).expect("false");
        let ordered = hol.hyps(&[truth, falsity]).expect("ordered");
        let reversed = hol.hyps(&[falsity, truth, falsity]).expect("reversed");
        assert_eq!(ordered, reversed);
        let entries = hol.hyps_entries(ordered).expect("entries");
        assert_eq!(entries.len(), 2);
        assert!(entries[0].raw() < entries[1].raw());
    }

    #[test]
    fn context_spines_round_trip_in_index_order() {
        let connection = open();
        let hol = connection.view();
        let star = hol.kind(Kind::Star).expect("star");
        let arrow = hol.kind(Kind::Arr(star, star)).expect("arrow");
        let spine = hol.kinds(&[arrow, star]).expect("spine");
        let entries = hol.kinds_entries(spine).expect("entries");
        assert_eq!(entries, vec![arrow, star]);
        assert_eq!(hol.kinds(&[]).expect("empty"), hol.empty_kinds());
    }

    #[test]
    fn unregistered_sources_are_rejected() {
        let connection = open();
        let hol = connection.view();
        assert!(matches!(
            hol.source_from_raw(1),
            Err(HolError::UnknownSource { .. })
        ));
    }

    #[test]
    fn policy_refusal_blocks_interning() {
        struct DenyIntern;
        impl Policy for DenyIntern {
            fn allows(&self, operation: Operation) -> bool {
                operation != Operation::InternSyntax
            }
        }
        let connection =
            Connection::open_hol_in_memory(DenyIntern).expect("open kernel-state database");
        let hol = connection.view();
        assert!(matches!(
            hol.ty(Ty::Bool),
            Err(HolError::PolicyDenied { .. })
        ));
    }
}
