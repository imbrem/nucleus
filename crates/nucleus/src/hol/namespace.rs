//! The namespace/export layer: stable names over kernel objects.
//!
//! Namespaces and exports are directory data, never authority: an export
//! row names an existing object so that other databases and untrusted
//! drivers can find it, but resolving a name yields nothing beyond what
//! the object table already held. Positions are dense and stable once
//! assigned, so `(namespace, position)` is the anchor a designated-source
//! import (`TY_EXT`/`TM_EXT`) can later refer to.
//!
//! The export sort codes stored in `hol_export.sort` are a physical
//! convention of this module, not part of `semantics.txt`: 1 kind, 2 type,
//! 3 term, 4 kind-spine, 5 var-spine, 6 hypothesis-spine.

use covalence_lib_error::snafu::{OptionExt, ResultExt};
use covalence_lib_sqlite::OptionalExtension;

use super::syntax::{HypsId, KindId, KindsId, NamespaceId, Sort, TermId, TypeId, VarsId};
use super::view::{
    ExportConflictSnafu, HolError, HolView, InvalidNameSnafu, StorageSnafu, UnknownExportSnafu,
    UnknownIdSnafu,
};
use super::{Operation, Policy};

/// A resolved export: one branded id of the recorded sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[expect(missing_docs, reason = "variants mirror the object sort classes")]
pub enum ExportTarget<'v> {
    Kind(KindId<'v>),
    Type(TypeId<'v>),
    Term(TermId<'v>),
    Kinds(KindsId<'v>),
    Vars(VarsId<'v>),
    Hyps(HypsId<'v>),
}

impl<'v> ExportTarget<'v> {
    /// Returns the sort class of the exported object.
    #[must_use]
    pub const fn sort(self) -> Sort {
        match self {
            Self::Kind(_) => Sort::Kind,
            Self::Type(_) => Sort::Type,
            Self::Term(_) => Sort::Term,
            Self::Kinds(_) => Sort::Kinds,
            Self::Vars(_) => Sort::Vars,
            Self::Hyps(_) => Sort::Hyps,
        }
    }

    /// Returns the raw row id of the exported object.
    #[must_use]
    pub const fn raw(self) -> i64 {
        match self {
            Self::Kind(id) => id.raw(),
            Self::Type(id) => id.raw(),
            Self::Term(id) => id.raw(),
            Self::Kinds(id) => id.raw(),
            Self::Vars(id) => id.raw(),
            Self::Hyps(id) => id.raw(),
        }
    }

    /// Returns the exported term, if the export is a term.
    #[must_use]
    pub const fn as_term(self) -> Option<TermId<'v>> {
        match self {
            Self::Term(id) => Some(id),
            _ => None,
        }
    }
}

const fn sort_code(sort: Sort) -> i64 {
    match sort {
        Sort::Kind => 1,
        Sort::Type => 2,
        Sort::Term => 3,
        Sort::Kinds => 4,
        Sort::Vars => 5,
        Sort::Hyps => 6,
    }
}

const fn sort_of_code(code: i64) -> Option<Sort> {
    match code {
        1 => Some(Sort::Kind),
        2 => Some(Sort::Type),
        3 => Some(Sort::Term),
        4 => Some(Sort::Kinds),
        5 => Some(Sort::Vars),
        6 => Some(Sort::Hyps),
        _ => None,
    }
}

impl<'v, P: Policy> HolView<'v, P> {
    /// Interns a namespace, returning the existing row when present.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses exporting, the name is empty, or
    /// storage fails.
    pub fn namespace(&self, name: &str) -> Result<NamespaceId<'v>, HolError> {
        self.authorize(Operation::Export)?;
        if name.is_empty() {
            return InvalidNameSnafu.fail();
        }
        self.raw_sqlite()
            .prepare_cached(
                "INSERT INTO hol_namespace(name) VALUES (?1)
                 ON CONFLICT(name) DO UPDATE SET name = name
                 RETURNING ns_id",
            )
            .and_then(|mut statement| statement.query_row((name,), |row| row.get::<_, i64>(0)))
            .context(StorageSnafu)
            .map(NamespaceId::new)
    }

    /// Looks up a namespace without creating it.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads or storage fails.
    pub fn find_namespace(&self, name: &str) -> Result<Option<NamespaceId<'v>>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.raw_sqlite()
            .prepare_cached("SELECT ns_id FROM hol_namespace WHERE name = ?1")
            .and_then(|mut statement| {
                statement
                    .query_row((name,), |row| row.get::<_, i64>(0))
                    .optional()
            })
            .context(StorageSnafu)
            .map(|found| found.map(NamespaceId::new))
    }

    /// Exports `target` under `name`, appending at the next free position.
    ///
    /// Re-exporting an identical `(name, target)` pair returns the
    /// existing position, so seeding is idempotent; exporting a different
    /// target under an existing name is a conflict.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses exporting, the name is empty, the name
    /// already names a different object, or storage fails.
    pub fn export(
        &self,
        namespace: NamespaceId<'v>,
        name: &str,
        target: ExportTarget<'v>,
    ) -> Result<u32, HolError> {
        self.authorize(Operation::Export)?;
        if name.is_empty() {
            return InvalidNameSnafu.fail();
        }
        if let Some((position, existing)) = self.named_export(namespace, name)? {
            if existing == target {
                return Ok(position);
            }
            return ExportConflictSnafu {
                name: name.to_owned(),
            }
            .fail();
        }
        self.raw_sqlite()
            .prepare_cached(
                "INSERT INTO hol_export(ns_id, pos, sort, target, name)
                 SELECT ?1, coalesce(max(pos) + 1, 0), ?2, ?3, ?4
                 FROM hol_export WHERE ns_id = ?1
                 RETURNING pos",
            )
            .and_then(|mut statement| {
                statement.query_row(
                    (
                        namespace.raw(),
                        sort_code(target.sort()),
                        target.raw(),
                        name,
                    ),
                    |row| row.get::<_, i64>(0),
                )
            })
            .context(StorageSnafu)
            .map(|position| u32::try_from(position).unwrap_or_default())
    }

    /// Resolves an export by name.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads, no export carries this name, or
    /// the stored row is malformed.
    pub fn resolve_export(
        &self,
        namespace: NamespaceId<'v>,
        name: &str,
    ) -> Result<ExportTarget<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let (_, target) = self
            .named_export(namespace, name)?
            .context(UnknownExportSnafu {
                name: name.to_owned(),
            })?;
        Ok(target)
    }

    /// Resolves an export by position.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses reads, the position is unassigned, or
    /// the stored row is malformed.
    pub fn export_at(
        &self,
        namespace: NamespaceId<'v>,
        position: u32,
    ) -> Result<ExportTarget<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        let row = self
            .raw_sqlite()
            .prepare_cached("SELECT sort, target FROM hol_export WHERE ns_id = ?1 AND pos = ?2")
            .and_then(|mut statement| {
                statement
                    .query_row((namespace.raw(), i64::from(position)), |row| {
                        Ok((row.get::<_, i64>(0)?, row.get::<_, i64>(1)?))
                    })
                    .optional()
            })
            .context(StorageSnafu)?
            .context(UnknownExportSnafu {
                name: format!("#{position}"),
            })?;
        self.decode_export(row)
    }

    fn named_export(
        &self,
        namespace: NamespaceId<'v>,
        name: &str,
    ) -> Result<Option<(u32, ExportTarget<'v>)>, HolError> {
        let row = self
            .raw_sqlite()
            .prepare_cached(
                "SELECT pos, sort, target FROM hol_export WHERE ns_id = ?1 AND name = ?2",
            )
            .and_then(|mut statement| {
                statement
                    .query_row((namespace.raw(), name), |row| {
                        Ok((
                            row.get::<_, i64>(0)?,
                            row.get::<_, i64>(1)?,
                            row.get::<_, i64>(2)?,
                        ))
                    })
                    .optional()
            })
            .context(StorageSnafu)?;
        let Some((position, sort, target)) = row else {
            return Ok(None);
        };
        let target = self.decode_export((sort, target))?;
        Ok(Some((u32::try_from(position).unwrap_or_default(), target)))
    }

    /// Revalidates a stored `(sort, target)` pair against the object
    /// table, so a resolved export carries the same guarantee as any
    /// other branded id.
    fn decode_export(&self, row: (i64, i64)) -> Result<ExportTarget<'v>, HolError> {
        let (code, raw) = row;
        let sort = sort_of_code(code).context(UnknownIdSnafu { raw })?;
        Ok(match sort {
            Sort::Kind => ExportTarget::Kind(self.kind_from_raw(raw)?),
            Sort::Type => ExportTarget::Type(self.ty_from_raw(raw)?),
            Sort::Term => ExportTarget::Term(self.tm_from_raw(raw)?),
            Sort::Kinds => ExportTarget::Kinds(self.kinds_from_raw(raw)?),
            Sort::Vars => ExportTarget::Vars(self.vars_from_raw(raw)?),
            Sort::Hyps => ExportTarget::Hyps(self.hyps_from_raw(raw)?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::syntax::{Tm, Ty};
    use super::super::{AllowAll, Hol, Operation, Policy};
    use super::*;
    use crate::Connection;

    fn open() -> Connection<Hol<AllowAll>> {
        Connection::open_hol_in_memory(AllowAll).expect("open kernel-state database")
    }

    #[test]
    fn namespaces_intern_and_resolve_exports() {
        let connection = open();
        let hol = connection.view();
        let namespace = hol.namespace("init").expect("namespace");
        assert_eq!(hol.namespace("init").expect("again"), namespace);
        assert_eq!(hol.find_namespace("init").expect("find"), Some(namespace));
        assert_eq!(hol.find_namespace("absent").expect("absent"), None);

        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let position = hol
            .export(namespace, "true", ExportTarget::Term(truth))
            .expect("export");
        assert_eq!(position, 0);
        assert_eq!(
            hol.resolve_export(namespace, "true").expect("resolve"),
            ExportTarget::Term(truth)
        );
        assert_eq!(
            hol.export_at(namespace, 0).expect("positional"),
            ExportTarget::Term(truth)
        );
    }

    #[test]
    fn exports_are_idempotent_and_conflicts_are_rejected() {
        let connection = open();
        let hol = connection.view();
        let namespace = hol.namespace("init").expect("namespace");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let falsity = hol.tm(Tm::Bool(false)).expect("false");
        let first = hol
            .export(namespace, "true", ExportTarget::Term(truth))
            .expect("export");
        let again = hol
            .export(namespace, "true", ExportTarget::Term(truth))
            .expect("re-export");
        assert_eq!(first, again);
        assert!(matches!(
            hol.export(namespace, "true", ExportTarget::Term(falsity)),
            Err(HolError::ExportConflict { name }) if name == "true"
        ));
        let second = hol
            .export(namespace, "false", ExportTarget::Term(falsity))
            .expect("second export");
        assert_eq!(second, 1);
    }

    #[test]
    fn empty_names_and_unknown_exports_are_rejected() {
        let connection = open();
        let hol = connection.view();
        let namespace = hol.namespace("init").expect("namespace");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        assert!(matches!(hol.namespace(""), Err(HolError::InvalidName)));
        assert!(matches!(
            hol.export(namespace, "", ExportTarget::Term(truth)),
            Err(HolError::InvalidName)
        ));
        assert!(matches!(
            hol.resolve_export(namespace, "missing"),
            Err(HolError::UnknownExport { name }) if name == "missing"
        ));
        assert!(matches!(
            hol.export_at(namespace, 7),
            Err(HolError::UnknownExport { .. })
        ));
    }

    #[test]
    fn export_targets_carry_every_sort() {
        let connection = open();
        let hol = connection.view();
        let namespace = hol.namespace("sorts").expect("namespace");
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let vars = hol.vars(&[bool_ty]).expect("vars");
        hol.export(namespace, "type", ExportTarget::Type(bool_ty))
            .expect("type export");
        hol.export(namespace, "vars", ExportTarget::Vars(vars))
            .expect("vars export");
        hol.export(namespace, "term", ExportTarget::Term(truth))
            .expect("term export");
        assert_eq!(
            hol.resolve_export(namespace, "type").expect("type"),
            ExportTarget::Type(bool_ty)
        );
        assert_eq!(
            hol.resolve_export(namespace, "vars").expect("vars"),
            ExportTarget::Vars(vars)
        );
        assert_eq!(
            hol.resolve_export(namespace, "term")
                .expect("term")
                .as_term(),
            Some(truth)
        );
    }

    #[test]
    fn export_policy_gates_writes_but_not_reads() {
        struct ReadOnly;
        impl Policy for ReadOnly {
            fn allows(&self, operation: Operation) -> bool {
                operation == Operation::ReadSyntax
            }
        }
        let connection =
            Connection::open_hol_in_memory(ReadOnly).expect("open kernel-state database");
        let hol = connection.view();
        assert!(matches!(
            hol.namespace("init"),
            Err(HolError::PolicyDenied { .. })
        ));
        assert_eq!(hol.find_namespace("init").expect("find"), None);
    }
}
