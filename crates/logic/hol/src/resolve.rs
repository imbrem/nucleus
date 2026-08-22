//! Direct navigation across Ethane arena imports.

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;

use crate::{Arena, Import, ImportId, Link, Ref, Sort, Table, Tag, wire};

/// Supplies an immutable table for a content-addressed link.
///
/// A resolver is untrusted. It may perform I/O, cache tables, or return a
/// table for the wrong address. Consumers use [`ResolverExt::resolve_checked`]
/// before relying on its answer.
pub trait Resolver {
    /// Implementation-specific lookup or I/O failure.
    type Error: std::error::Error + 'static;

    /// Gets a table claimed to answer `link`.
    ///
    /// # Errors
    ///
    /// Returns an implementation-specific resolution failure. A currently
    /// unavailable link is one such failure and belongs in this error type.
    fn resolve(&mut self, link: &Link) -> Result<Table, Self::Error>;
}

/// A recoverable failure while following an import or proxy row.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ResolveError<E>
where
    E: std::error::Error + 'static,
{
    /// A local or foreign reference does not name a row.
    #[snafu(display("reference {reference:?} does not name an arena row"))]
    MissingReference {
        /// Missing one-based definition reference.
        reference: Ref,
    },
    /// An import identifier does not name an import entry.
    #[snafu(display("import {source_id:?} does not name an import entry"))]
    MissingImport {
        /// Missing one-based import identifier.
        source_id: ImportId,
    },
    /// A null import was traversed.
    #[snafu(display("import {source_id:?} is null"))]
    NullImport {
        /// Null one-based import identifier.
        source_id: ImportId,
    },
    /// A literal import could not be promoted to a table.
    #[snafu(display("could not encode literal arena import: {source}"))]
    LiteralEncoding {
        /// Arena encoding failure.
        source: wire::EncodeError,
    },
    /// The untrusted resolver failed.
    #[snafu(display("could not resolve {link:?}: {source}"))]
    Resolver {
        /// Link being resolved.
        link: Link,
        /// Resolver-specific failure.
        source: E,
    },
    /// The untrusted resolver returned a table for another address.
    #[snafu(display("resolver returned address {returned} for request {requested}"))]
    WrongAddress {
        /// Address requested by the link.
        requested: O256,
        /// Address carried by the returned table.
        returned: O256,
    },
    /// A non-proxy row was passed to proxy resolution.
    #[snafu(display("reference {reference:?} is not a proxy row"))]
    NotProxy {
        /// Reference to the non-proxy row.
        reference: Ref,
    },
    /// A proxy points to a row in another syntactic category.
    #[snafu(display("proxy expects {expected:?}, but target declares {actual:?}"))]
    CategoryMismatch {
        /// Category declared by the proxy tag.
        expected: Sort,
        /// Category declared by the foreign row tag.
        actual: Sort,
    },
}

mod sealed {
    pub trait ResolverExt {}

    impl<R: super::Resolver + ?Sized> ResolverExt for R {}
}

/// Address-checked operations available on every [`Resolver`].
///
/// This trait is sealed and blanket-implemented, so resolver implementations
/// cannot replace the address check. A successful result is a table for the
/// exact requested link.
pub trait ResolverExt: Resolver + sealed::ResolverExt {
    /// Gets a table for exactly `link`.
    ///
    /// # Errors
    ///
    /// Propagates [`Resolver::resolve`] failures and returns
    /// [`ResolveError::WrongAddress`] if the resolver answers with a table for
    /// another address.
    fn resolve_checked(&mut self, link: &Link) -> Result<Table, ResolveError<Self::Error>> {
        let table = self
            .resolve(link)
            .map_err(|source| ResolveError::Resolver {
                link: *link,
                source,
            })?;
        let returned = table.address();
        if returned == link.blake3 {
            Ok(table)
        } else {
            Err(ResolveError::WrongAddress {
                requested: link.blake3,
                returned,
            })
        }
    }
}

impl<R: Resolver + ?Sized> ResolverExt for R {}

/// A reference paired with the immutable table that owns it.
///
/// This is a flat cursor, not a reconstructed syntax tree. Its accessors read
/// one row in place and do not follow ordinary child references.
#[derive(Clone, Debug)]
pub struct Expr {
    table: Table,
    reference: Ref,
}

impl Expr {
    /// Returns the local reference within [`Self::table`].
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }

    /// Returns the table that owns this reference.
    #[must_use]
    pub const fn table(&self) -> &Table {
        &self.table
    }

    /// Returns the arena that owns this reference.
    #[must_use]
    pub fn arena(&self) -> &Arena {
        &self.table
    }

    /// Returns the row's tag.
    ///
    /// # Panics
    ///
    /// Panics only if the private `Expr` invariant is broken.
    #[must_use]
    pub fn tag(&self) -> Tag {
        self.arena()
            .tag(self.reference)
            .expect("resolved references name an existing row")
    }

    /// Returns the row's optional equality claim.
    #[must_use]
    pub fn eq(&self) -> Option<Ref> {
        self.arena().eq(self.reference)
    }

    /// Returns the row's optional sort claim.
    #[must_use]
    pub fn sort(&self) -> Option<Ref> {
        self.arena().sort(self.reference)
    }

    /// Iterates over the row's ordinary children.
    ///
    /// # Panics
    ///
    /// Panics only if the private `Expr` invariant is broken.
    #[must_use]
    pub fn children(&self) -> impl ExactSizeIterator<Item = Ref> + '_ {
        self.arena()
            .children(self.reference)
            .expect("resolved references name an existing row")
    }

    /// Returns the name carried by a variable or binder row.
    #[must_use]
    pub fn name(&self) -> Option<u64> {
        self.arena().name(self.reference)
    }

    /// Returns the value carried by a Boolean literal row.
    #[must_use]
    pub fn bool_value(&self) -> Option<bool> {
        self.arena().bool_value(self.reference)
    }

    /// Returns the source and index carried by a proxy row.
    #[must_use]
    pub fn foreign(&self) -> Option<(ImportId, Ref)> {
        self.arena().foreign(self.reference)
    }
}

impl Table {
    /// Returns a flat cursor for a row in this table.
    #[must_use]
    pub fn expr(&self, reference: Ref) -> Option<Expr> {
        self.tag(reference)?;
        Some(Expr {
            table: self.clone(),
            reference,
        })
    }
}

impl Arena {
    /// Resolves one import-table entry without traversing its definitions.
    ///
    /// Literal imports are encoded and hashed to produce the same [`Table`]
    /// representation returned for links.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent or null import, literal encoding
    /// failure, resolver failure, or mismatched returned address.
    pub fn resolve_import<R: Resolver + ?Sized>(
        &self,
        resolver: &mut R,
        source: ImportId,
    ) -> Result<Table, ResolveError<R::Error>> {
        let entry = self
            .import(source)
            .ok_or(ResolveError::MissingImport { source_id: source })?;
        match entry {
            Import::Null => Err(ResolveError::NullImport { source_id: source }),
            Import::Literal(arena) => Table::from_arena((**arena).clone())
                .map_err(|source| ResolveError::LiteralEncoding { source }),
            Import::Link(link) => resolver.resolve_checked(link),
        }
    }

    /// Resolves one foreign reference without elaborating or copying its row.
    ///
    /// # Errors
    ///
    /// In addition to import failures, returns
    /// [`ResolveError::MissingReference`] when the foreign table has no such
    /// row.
    pub fn resolve_foreign<R: Resolver + ?Sized>(
        &self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<Expr, ResolveError<R::Error>> {
        let table = self.resolve_import(resolver, source)?;
        table
            .expr(foreign)
            .ok_or(ResolveError::MissingReference { reference: foreign })
    }

    /// Follows one `tm.ref`, `ty.ref`, or `kind.ref` row.
    ///
    /// The target's declared category must match the proxy tag. No child is
    /// traversed and no recursive syntax value is allocated.
    ///
    /// # Errors
    ///
    /// Returns [`ResolveError::NotProxy`] for an ordinary row and
    /// [`ResolveError::CategoryMismatch`] for a proxy whose target declares
    /// another category.
    pub fn resolve_proxy<R: Resolver + ?Sized>(
        &self,
        resolver: &mut R,
        reference: Ref,
    ) -> Result<Expr, ResolveError<R::Error>> {
        let expected = self
            .tag(reference)
            .ok_or(ResolveError::MissingReference { reference })?
            .sort();
        let (source, foreign) = self
            .foreign(reference)
            .ok_or(ResolveError::NotProxy { reference })?;
        let target = self.resolve_foreign(resolver, source, foreign)?;
        let actual = target.tag().sort();
        if actual == expected {
            Ok(target)
        } else {
            Err(ResolveError::CategoryMismatch { expected, actual })
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{Import, LinkFormat};
    use covalence_logic_cas::CasFact;

    struct OneTable(Table);

    impl Resolver for OneTable {
        type Error = Infallible;

        fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
            Ok(self.0.clone())
        }
    }

    #[test]
    fn literal_and_link_proxies_use_the_same_table_cursor() {
        let mut imported = Arena::empty();
        let target = imported.push_bool_ty().unwrap();
        let mut encoded = Vec::new();
        wire::serialize(&imported, &mut encoded).unwrap();
        let table = Table::try_from(CasFact::from_bytes(encoded)).unwrap();

        let mut owner = Arena::empty();
        let literal = owner
            .push_import(Import::Literal(Box::new(imported)))
            .unwrap();
        let linked = owner
            .push_import(Import::Link(Link {
                format: LinkFormat::Cbor,
                blake3: table.address(),
            }))
            .unwrap();
        let literal_proxy = owner.push_ty_ref(literal, target).unwrap();
        let linked_proxy = owner.push_ty_ref(linked, target).unwrap();
        let mut resolver = OneTable(table);

        let literal = owner.resolve_proxy(&mut resolver, literal_proxy).unwrap();
        let linked = owner.resolve_proxy(&mut resolver, linked_proxy).unwrap();
        assert_eq!(literal.table().address(), linked.table().address());
        assert_eq!(literal.reference(), linked.reference());
        assert_eq!(literal.tag(), linked.tag());
        assert_eq!(literal.children().collect::<Vec<_>>(), Vec::<Ref>::new());
    }

    #[test]
    fn proxy_resolution_checks_only_the_declared_category() {
        let mut imported = Arena::empty();
        let target = imported.push_bool_ty().unwrap();
        let mut owner = Arena::empty();
        let source = owner
            .push_import(Import::Literal(Box::new(imported)))
            .unwrap();
        let proxy = owner.push_tm_ref(source, target).unwrap();
        let mut resolver = OneTable(Table::from_arena(Arena::empty()).unwrap());

        assert!(matches!(
            owner.resolve_proxy(&mut resolver, proxy),
            Err(ResolveError::CategoryMismatch {
                expected: Sort::Tm,
                actual: Sort::Ty,
            })
        ));
    }

    #[test]
    fn checked_resolution_rejects_an_unrelated_table() {
        let table = Table::from_arena(Arena::empty()).unwrap();
        let returned = table.address();
        let requested = O256::from_array([9; 32]);
        assert_ne!(requested, returned);
        let link = Link {
            format: LinkFormat::Cbor,
            blake3: requested,
        };
        let mut resolver = OneTable(table);

        assert!(matches!(
            resolver.resolve_checked(&link),
            Err(ResolveError::WrongAddress {
                requested: expected,
                returned: actual,
            }) if expected == requested && actual == returned
        ));
    }
}
