//! Checked Ethane kernel wrapper.

use std::sync::Arc;

use crate::{
    Arena, Import, ImportId, Meta, Ref, ResolveError, Resolver,
    resolve::{Value, resolve_at},
};

/// A recoverable failure while validating an untrusted arena as a kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelError<E> {
    TooManyDefinitions,
    ForwardReference { owner: Ref, child: Ref },
    UnsupportedAxiom(String),
    InvalidSortingClaim(Ref),
    InvalidEqualityClaim(Ref),
    InvalidContext(Ref),
    InvalidConclusion(Meta),
    Resolve(ResolveError<E>),
}

impl<E> From<ResolveError<E>> for KernelError<E> {
    fn from(error: ResolveError<E>) -> Self {
        Self::Resolve(error)
    }
}

impl<E: std::fmt::Debug + std::fmt::Display> std::fmt::Display for KernelError<E> {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyDefinitions => {
                output.write_str("arena has more than u64::MAX definitions")
            }
            Self::ForwardReference { owner, child } => write!(
                output,
                "definition {} has forward local child {}",
                owner.get(),
                child.get()
            ),
            Self::UnsupportedAxiom(name) => write!(output, "unsupported axiom capability {name}"),
            Self::InvalidSortingClaim(reference) => {
                write!(
                    output,
                    "invalid sorting claim at definition {}",
                    reference.get()
                )
            }
            Self::InvalidEqualityClaim(reference) => {
                write!(
                    output,
                    "invalid equality claim at definition {}",
                    reference.get()
                )
            }
            Self::InvalidContext(reference) => {
                write!(
                    output,
                    "context entry {} is not a checked Boolean",
                    reference.get()
                )
            }
            Self::InvalidConclusion(record) => {
                write!(output, "invalid metadata conclusion {record:?}")
            }
            Self::Resolve(error) => write!(output, "could not resolve kernel data: {error:?}"),
        }
    }
}

impl<E: std::fmt::Debug + std::fmt::Display> std::error::Error for KernelError<E> {}

/// An arena whose exposed claims satisfy `OneBased.Arena.KernelValid`.
///
/// Raw CBOR decoding returns [`Arena`], never `Kernel`. Construction runs the
/// checked validation pass. The resolver is a ghost parameter in Lean; Rust
/// callers must retain the successful-resolution persistence promised by
/// their CAS implementation.
#[derive(Clone, Debug)]
pub struct Kernel {
    arena: Arena,
}

impl Kernel {
    /// Validate an untrusted arena.
    ///
    /// The MVP accepts reflexive inline equality claims. Beta and congruence
    /// extend the equality checker without weakening this constructor.
    ///
    /// # Errors
    ///
    /// Returns the first failed representation, resolution, sorting, typing,
    /// equality, context, metadata, or axiom check.
    pub fn try_from_arena<R: Resolver>(
        arena: Arena,
        resolver: &R,
        fuel: usize,
    ) -> Result<Self, KernelError<R::Error>> {
        validate_structure(&arena)?;

        for name in arena.axioms() {
            if name != "ax.inf" {
                return Err(KernelError::UnsupportedAxiom(name.to_owned()));
            }
        }

        for position in 1..=arena.len() {
            let reference = reference(position)?;
            validate_sort(&arena, resolver, reference, fuel)?;
            validate_reflexive_equality(&arena, resolver, reference, fuel)?;
        }

        for reference in arena.context() {
            let value = resolve_at(&arena, resolver, reference, fuel)?;
            if !is_checked_bool(&value) {
                return Err(KernelError::InvalidContext(reference));
            }
        }

        for record in arena.assertions() {
            if !validate_meta(&arena, resolver, *record, fuel)? {
                return Err(KernelError::InvalidConclusion(*record));
            }
        }

        Ok(Self { arena })
    }

    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }
}

fn reference<E>(position: usize) -> Result<Ref, KernelError<E>> {
    let value = u64::try_from(position).map_err(|_| KernelError::TooManyDefinitions)?;
    Ref::new(value).ok_or(KernelError::TooManyDefinitions)
}

fn validate_structure<E>(arena: &Arena) -> Result<(), KernelError<E>> {
    for position in 1..=arena.len() {
        let owner = reference(position)?;
        let row = arena.row(owner).ok_or(KernelError::TooManyDefinitions)?;
        for child in row.expr().children() {
            if child >= owner {
                return Err(KernelError::ForwardReference { owner, child });
            }
        }
    }
    Ok(())
}

fn validate_sort<R: Resolver>(
    arena: &Arena,
    resolver: &R,
    reference: Ref,
    fuel: usize,
) -> Result<(), KernelError<R::Error>> {
    let Some(classifier) = arena.sort(reference) else {
        return Ok(());
    };
    let value = resolve_at(arena, resolver, reference, fuel)?;
    let classifier = resolve_at(arena, resolver, classifier, fuel)?;
    if value.has_sort(&classifier) {
        Ok(())
    } else {
        Err(KernelError::InvalidSortingClaim(reference))
    }
}

fn validate_reflexive_equality<R: Resolver>(
    arena: &Arena,
    resolver: &R,
    reference: Ref,
    fuel: usize,
) -> Result<(), KernelError<R::Error>> {
    let Some(right) = arena.eq(reference) else {
        return Ok(());
    };
    let left = resolve_at(arena, resolver, reference, fuel)?;
    let right = resolve_at(arena, resolver, right, fuel)?;
    if left == right && left.is_well_formed() {
        Ok(())
    } else {
        Err(KernelError::InvalidEqualityClaim(reference))
    }
}

fn is_checked_bool(value: &Value) -> bool {
    matches!(
        value,
        Value::Tm {
            ty: crate::resolve::Syntax::BoolTy,
            ..
        }
    ) && value.is_well_formed()
}

fn imported<R: Resolver>(
    owner: &Arena,
    resolver: &R,
    source: ImportId,
) -> Result<Arc<Arena>, ResolveError<R::Error>> {
    let entry = owner
        .import(source)
        .ok_or(ResolveError::MissingImport(source))?;
    match entry {
        Import::Null => Err(ResolveError::NullImport(source)),
        Import::Literal(arena) => Ok(Arc::new((**arena).clone())),
        Import::Link(link) => resolver
            .resolve(link)
            .map_err(ResolveError::Resolver)?
            .ok_or(ResolveError::Unavailable(*link)),
    }
}

fn validate_meta<R: Resolver>(
    owner: &Arena,
    resolver: &R,
    record: Meta,
    fuel: usize,
) -> Result<bool, KernelError<R::Error>> {
    Ok(match record {
        Meta::Valid { src } => {
            let arena = imported(owner, resolver, src)?;
            let mut all_resolve = true;
            for position in 1..=arena.len() {
                let reference = reference(position)?;
                if resolve_at(&arena, resolver, reference, fuel).is_err() {
                    all_resolve = false;
                    break;
                }
            }
            all_resolve
        }
        Meta::Wf { src, ix, sort } => {
            let arena = imported(owner, resolver, src)?;
            let value = resolve_at(&arena, resolver, ix, fuel)?;
            let classifier = resolve_at(owner, resolver, sort, fuel)?;
            value.has_sort(&classifier)
        }
    })
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        Link,
        row::{Expr, Row},
    };

    const fn reference(value: u64) -> Ref {
        Ref::new(value).unwrap()
    }

    struct NoLinks;

    impl Resolver for NoLinks {
        type Error = Infallible;

        fn resolve(&self, _: &Link) -> Result<Option<Arc<Arena>>, Self::Error> {
            Ok(None)
        }
    }

    #[test]
    fn checked_boolean_context_and_reflexive_equality_are_accepted() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                Row::new(Expr::BoolTy),
                Row::new(Expr::Bool(true)).with_sort(reference(1)),
                Row::new(Expr::Bool(true)).with_eq(reference(2)),
            ],
            [reference(2)],
            vec![],
            vec![],
        );
        assert!(Kernel::try_from_arena(arena, &NoLinks, 4).is_ok());
    }

    #[test]
    fn assumptions_are_not_promoted_and_bad_assertions_are_rejected() {
        let assumed = Meta::Wf {
            src: ImportId::new(1).unwrap(),
            ix: reference(1),
            sort: reference(1),
        };
        let arena = Arena::from_parts(vec![], [], vec![], [], vec![assumed], vec![]);
        assert!(Kernel::try_from_arena(arena, &NoLinks, 1).is_ok());

        let asserted = Arena::from_parts(vec![], [], vec![], [], vec![], vec![assumed]);
        assert!(matches!(
            Kernel::try_from_arena(asserted, &NoLinks, 1),
            Err(KernelError::Resolve(ResolveError::MissingImport(_)))
        ));
    }

    #[test]
    fn forward_edges_and_unchecked_contexts_are_rejected() {
        let forward = Arena::from_parts(
            vec![],
            [],
            vec![Row::new(Expr::App(reference(2), reference(2)))],
            [],
            vec![],
            vec![],
        );
        assert!(matches!(
            Kernel::try_from_arena(forward, &NoLinks, 2),
            Err(KernelError::ForwardReference { .. })
        ));

        let unchecked = Arena::from_parts(
            vec![],
            [],
            vec![Row::new(Expr::KindStar)],
            [reference(1)],
            vec![],
            vec![],
        );
        assert!(matches!(
            Kernel::try_from_arena(unchecked, &NoLinks, 2),
            Err(KernelError::InvalidContext(_))
        ));
    }
}
