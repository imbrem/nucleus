//! Direct navigation across raw Ethane arena imports.

use std::sync::Arc;

use crate::{Arena, Import, ImportId, Link, Ref, Sort, Tag};

/// Supplies an arena for a content-addressed link.
///
/// A resolver is untrusted: this raw layer uses the returned arena only as
/// data. The checked layer accepts opaque arena facts instead. Mutable access
/// permits callers to implement caching without putting synchronization or
/// storage policy in the arena crate.
pub trait Resolver {
    type Error;

    /// Returns the linked arena when it is currently available.
    ///
    /// # Errors
    ///
    /// Returns a resolver-specific lookup failure. Temporary absence is
    /// represented by `Ok(None)`.
    fn resolve(&mut self, link: &Link) -> Result<Option<Arc<Arena>>, Self::Error>;
}

/// A borrowed literal import or a shared linked arena.
///
/// Literal imports remain allocation-free. Link ownership is supplied by the
/// resolver and is not part of the serialized arena.
#[derive(Clone, Debug)]
pub enum ResolvedArena<'a> {
    Literal(&'a Arena),
    Linked(Arc<Arena>),
}

impl AsRef<Arena> for ResolvedArena<'_> {
    fn as_ref(&self) -> &Arena {
        match self {
            Self::Literal(arena) => arena,
            Self::Linked(arena) => arena,
        }
    }
}

/// One reference paired with the arena that owns it.
///
/// This is a flat cursor, not a reconstructed syntax tree. Its accessors read
/// the row in place and do not follow ordinary child references.
#[derive(Clone, Debug)]
pub struct ResolvedRef<'a> {
    arena: ResolvedArena<'a>,
    reference: Ref,
}

impl ResolvedRef<'_> {
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }

    #[must_use]
    pub fn arena(&self) -> &Arena {
        self.arena.as_ref()
    }

    #[must_use]
    pub fn tag(&self) -> Tag {
        // Construction checks that the reference exists.
        self.arena()
            .tag(self.reference)
            .expect("resolved references name an existing row")
    }

    #[must_use]
    pub fn eq(&self) -> Option<Ref> {
        self.arena().eq(self.reference)
    }

    #[must_use]
    pub fn sort(&self) -> Option<Ref> {
        self.arena().sort(self.reference)
    }

    #[must_use]
    pub fn children(&self) -> impl ExactSizeIterator<Item = Ref> + '_ {
        self.arena()
            .children(self.reference)
            .expect("resolved references name an existing row")
    }

    #[must_use]
    pub fn name(&self) -> Option<u64> {
        self.arena().name(self.reference)
    }

    #[must_use]
    pub fn bool_value(&self) -> Option<bool> {
        self.arena().bool_value(self.reference)
    }

    #[must_use]
    pub fn foreign(&self) -> Option<(ImportId, Ref)> {
        self.arena().foreign(self.reference)
    }
}

/// A recoverable failure while following an explicit import or proxy row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolveError<E> {
    MissingReference(Ref),
    MissingImport(ImportId),
    NullImport(ImportId),
    Unavailable(Link),
    Resolver(E),
    NotProxy(Ref),
    CategoryMismatch { expected: Sort, actual: Sort },
}

impl Arena {
    /// Returns a flat cursor for a local row.
    #[must_use]
    pub fn resolved(&self, reference: Ref) -> Option<ResolvedRef<'_>> {
        self.tag(reference)?;
        Some(ResolvedRef {
            arena: ResolvedArena::Literal(self),
            reference,
        })
    }

    /// Resolves one import-table entry without traversing its definitions.
    ///
    /// # Errors
    ///
    /// Distinguishes an absent or null import, temporary link absence, and a
    /// resolver failure.
    pub fn resolve_import<'a, R: Resolver>(
        &'a self,
        resolver: &mut R,
        source: ImportId,
    ) -> Result<ResolvedArena<'a>, ResolveError<R::Error>> {
        let entry = self
            .import(source)
            .ok_or(ResolveError::MissingImport(source))?;
        match entry {
            Import::Null => Err(ResolveError::NullImport(source)),
            Import::Literal(arena) => Ok(ResolvedArena::Literal(arena)),
            Import::Link(link) => resolver
                .resolve(link)
                .map_err(ResolveError::Resolver)?
                .map(ResolvedArena::Linked)
                .ok_or(ResolveError::Unavailable(*link)),
        }
    }

    /// Resolves one foreign reference without elaborating or copying its row.
    ///
    /// # Errors
    ///
    /// In addition to import failures, returns `MissingReference` when the
    /// foreign arena has no such row.
    pub fn resolve_foreign<'a, R: Resolver>(
        &'a self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<ResolvedRef<'a>, ResolveError<R::Error>> {
        let arena = self.resolve_import(resolver, source)?;
        if arena.as_ref().tag(foreign).is_none() {
            return Err(ResolveError::MissingReference(foreign));
        }
        Ok(ResolvedRef {
            arena,
            reference: foreign,
        })
    }

    /// Follows one `tm.ref`, `ty.ref`, or `kind.ref` row.
    ///
    /// The target's declared tag category must match the proxy tag. No child
    /// is traversed and no recursive syntax value is allocated.
    ///
    /// # Errors
    ///
    /// Returns `NotProxy` for an ordinary row and `CategoryMismatch` for a
    /// proxy whose foreign row declares another category.
    pub fn resolve_proxy<'a, R: Resolver>(
        &'a self,
        resolver: &mut R,
        reference: Ref,
    ) -> Result<ResolvedRef<'a>, ResolveError<R::Error>> {
        let expected = self
            .tag(reference)
            .ok_or(ResolveError::MissingReference(reference))?
            .sort();
        let (source, foreign) = self
            .foreign(reference)
            .ok_or(ResolveError::NotProxy(reference))?;
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
    use covalence_lib_hash::O256;

    struct OneLink {
        address: O256,
        arena: Arc<Arena>,
    }

    impl Resolver for OneLink {
        type Error = Infallible;

        fn resolve(&mut self, link: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
            Ok((link.blake3 == self.address).then(|| Arc::clone(&self.arena)))
        }
    }

    fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    #[test]
    fn literal_and_link_proxies_read_the_same_flat_row() {
        let mut imported = Arena::empty();
        let target = imported.push_bool_ty().unwrap();
        let imported = Arc::new(imported);
        let address = O256::from_array([1; 32]);

        let mut owner = Arena::empty();
        let literal = owner
            .push_import(Import::Literal(Box::new((*imported).clone())))
            .unwrap();
        let linked = owner
            .push_import(Import::Link(Link {
                format: LinkFormat::Cbor,
                blake3: address,
            }))
            .unwrap();
        let literal_proxy = owner.push_ty_ref(literal, target).unwrap();
        let linked_proxy = owner.push_ty_ref(linked, target).unwrap();
        let mut resolver = OneLink {
            address,
            arena: imported,
        };

        let literal = owner.resolve_proxy(&mut resolver, literal_proxy).unwrap();
        let linked = owner.resolve_proxy(&mut resolver, linked_proxy).unwrap();
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
        let mut resolver = OneLink {
            address: O256::from_array([2; 32]),
            arena: Arc::new(Arena::empty()),
        };

        assert!(matches!(
            owner.resolve_proxy(&mut resolver, proxy),
            Err(ResolveError::CategoryMismatch {
                expected: Sort::Tm,
                actual: Sort::Ty,
            })
        ));
        assert_eq!(owner.resolved(reference(100)).map(|node| node.tag()), None);
    }
}
