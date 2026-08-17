//! Backend-neutral surface syntax and an LCF-style kernel boundary.
//!
//! Surface values are portable data. Checked terms and theorems are backend
//! values and deliberately have no public constructors. Direct (eager) links
//! are resolved to surface syntax before this API is called. Lazy imports are
//! syntax, but initially their classifications must be fully closed.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter};

/// Stable identity of a kernel implementation/configuration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct BackendId(String);

impl BackendId {
    #[must_use]
    pub fn new(value: impl Into<String>) -> Self {
        Self(value.into())
    }

    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A content-addressed reference. Its byte-level encoding belongs to the
/// codec/CAS layer rather than the kernel.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Link(Box<[u8]>);

impl Link {
    #[must_use]
    pub fn new(bytes: impl Into<Box<[u8]>>) -> Self {
        Self(bytes.into())
    }

    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SurfaceType {
    Bool,
    Nat,
    Arrow(Box<Self>, Box<Self>),
    /// An opaque, lazy type import. The kind is implicit in this first slice.
    LazyImport(Link),
}

impl SurfaceType {
    #[must_use]
    pub fn arrow(domain: Self, codomain: Self) -> Self {
        Self::Arrow(Box::new(domain), Box::new(codomain))
    }
}

/// Typed free variables are surface names, not kernel handles.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SurfaceVar {
    pub name: String,
    pub ty: SurfaceType,
}

impl SurfaceVar {
    #[must_use]
    pub fn new(name: impl Into<String>, ty: SurfaceType) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceTerm {
    Free(SurfaceVar),
    Bound(u32),
    App(Box<Self>, Box<Self>),
    Abs(SurfaceType, Box<Self>),
    Bool(bool),
    Nat(u64),
    Eq(SurfaceType, Box<Self>, Box<Self>),
    /// An opaque lazy term carrying its complete declared classification.
    LazyImport {
        link: Link,
        ty: SurfaceType,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SurfaceContext(BTreeMap<String, SurfaceType>);

impl SurfaceContext {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: impl Into<String>, ty: SurfaceType) -> Option<SurfaceType> {
        self.0.insert(name.into(), ty)
    }

    #[must_use]
    pub fn get(&self, name: &str) -> Option<&SurfaceType> {
        self.0.get(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &SurfaceType)> {
        self.0.iter().map(|(name, ty)| (name.as_str(), ty))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceError {
    DanglingBoundVariable(u32),
    FreeVariable,
}

impl Display for SurfaceError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::DanglingBoundVariable(index) => {
                write!(formatter, "dangling bound variable {index}")
            }
            Self::FreeVariable => formatter.write_str("term contains a free variable"),
        }
    }
}

impl Error for SurfaceError {}

impl SurfaceTerm {
    #[must_use]
    pub fn app(function: Self, argument: Self) -> Self {
        Self::App(Box::new(function), Box::new(argument))
    }

    #[must_use]
    pub fn abs(domain: SurfaceType, body: Self) -> Self {
        Self::Abs(domain, Box::new(body))
    }

    #[must_use]
    pub fn eq(ty: SurfaceType, left: Self, right: Self) -> Self {
        Self::Eq(ty, Box::new(left), Box::new(right))
    }

    /// Open a surface variable for convenient named construction.
    #[must_use]
    pub fn open(variable: SurfaceVar) -> Self {
        Self::Free(variable)
    }

    /// Close all occurrences of `variable` with a locally nameless binder.
    /// Existing bound indices remain attached to their current binders; the
    /// new variable's index reflects the abstractions traversed.
    ///
    /// # Errors
    ///
    /// Returns an error if nesting exceeds the supported bound-index range.
    pub fn close(self, variable: &SurfaceVar) -> Result<Self, SurfaceError> {
        self.close_at(variable, 0)
    }

    fn close_at(self, variable: &SurfaceVar, depth: u32) -> Result<Self, SurfaceError> {
        Ok(match self {
            Self::Free(found) if found == *variable => Self::Bound(depth),
            Self::Free(found) => Self::Free(found),
            Self::Bound(index) => Self::Bound(index),
            Self::App(function, argument) => Self::app(
                function.close_at(variable, depth)?,
                argument.close_at(variable, depth)?,
            ),
            Self::Abs(domain, body) => Self::abs(
                domain,
                body.close_at(
                    variable,
                    depth
                        .checked_add(1)
                        .ok_or(SurfaceError::DanglingBoundVariable(depth))?,
                )?,
            ),
            Self::Bool(value) => Self::Bool(value),
            Self::Nat(value) => Self::Nat(value),
            Self::Eq(ty, left, right) => Self::eq(
                ty,
                left.close_at(variable, depth)?,
                right.close_at(variable, depth)?,
            ),
            Self::LazyImport { link, ty } => Self::LazyImport { link, ty },
        })
    }

    /// Check the initial lazy-import invariant: no free variables and no
    /// bound variables escaping their enclosing abstractions.
    ///
    /// # Errors
    ///
    /// Returns an error for a free or dangling bound variable.
    pub fn require_closed(&self) -> Result<(), SurfaceError> {
        self.require_closed_at(0)
    }

    fn require_closed_at(&self, depth: u32) -> Result<(), SurfaceError> {
        match self {
            Self::Free(_) => Err(SurfaceError::FreeVariable),
            Self::Bound(index) if *index >= depth => {
                Err(SurfaceError::DanglingBoundVariable(*index))
            }
            // An import declares that its referenced term is fully closed.
            // Resolution validates that contract before exposing content.
            Self::Bound(_) | Self::Bool(_) | Self::Nat(_) | Self::LazyImport { .. } => Ok(()),
            Self::App(function, argument) => {
                function.require_closed_at(depth)?;
                argument.require_closed_at(depth)
            }
            Self::Abs(_, body) => body.require_closed_at(
                depth
                    .checked_add(1)
                    .ok_or(SurfaceError::DanglingBoundVariable(depth))?,
            ),
            Self::Eq(_, left, right) => {
                left.require_closed_at(depth)?;
                right.require_closed_at(depth)
            }
        }
    }
}

/// LCF kernel interface. Implementations keep all associated result types
/// opaque; clients cannot forge checked terms or theorems.
pub trait KernelBackend: Send + Sync + 'static {
    type CheckedType;
    type CheckedTerm;
    type Theorem;
    type Error: Error + Send + Sync + 'static;

    fn backend_id(&self) -> BackendId;

    /// Check and lower a surface type.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic when the type is malformed or ill-kinded.
    fn check_type(&self, surface: &SurfaceType) -> Result<Self::CheckedType, Self::Error>;

    /// Check and lower a surface term in a surface context.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic when sorting, closure, or typing fails.
    fn check_term(
        &self,
        context: &SurfaceContext,
        surface: &SurfaceTerm,
    ) -> Result<Self::CheckedTerm, Self::Error>;

    // Backend-neutral term construction. These remain raw surface values
    // until passed through `check_term`.
    fn open(&self, variable: SurfaceVar) -> SurfaceTerm {
        SurfaceTerm::open(variable)
    }

    /// Close a named variable into locally nameless form.
    ///
    /// # Errors
    ///
    /// Returns an error if binder nesting exceeds the bound-index range.
    fn close(&self, variable: &SurfaceVar, body: SurfaceTerm) -> Result<SurfaceTerm, SurfaceError> {
        body.close(variable)
    }

    fn app(&self, function: SurfaceTerm, argument: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::app(function, argument)
    }

    fn abs(&self, domain: SurfaceType, body: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::abs(domain, body)
    }

    fn bool_lit(&self, value: bool) -> SurfaceTerm {
        SurfaceTerm::Bool(value)
    }

    fn nat_lit(&self, value: u64) -> SurfaceTerm {
        SurfaceTerm::Nat(value)
    }

    fn eq(&self, ty: SurfaceType, left: SurfaceTerm, right: SurfaceTerm) -> SurfaceTerm {
        SurfaceTerm::eq(ty, left, right)
    }

    // Primitive LCF inferences. No serializable proof trace crosses this API.
    /// Introduce a proposition as the theorem's sole assumption.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic if the term is not a proposition or its
    /// checked handle belongs to another backend.
    fn assume(&self, proposition: &Self::CheckedTerm) -> Result<Self::Theorem, Self::Error>;

    /// Prove reflexive equality of a checked term.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic if the handle is incompatible.
    fn reflexivity(&self, term: &Self::CheckedTerm) -> Result<Self::Theorem, Self::Error>;

    /// Combine equality theorems by application congruence.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic when theorem types or identities mismatch.
    fn application_congruence(
        &self,
        function: &Self::Theorem,
        argument: &Self::Theorem,
    ) -> Result<Self::Theorem, Self::Error>;

    /// Prove beta conversion for an abstraction and argument.
    ///
    /// # Errors
    ///
    /// Returns a backend diagnostic when the checked terms are incompatible.
    fn beta(
        &self,
        abstraction: &Self::CheckedTerm,
        argument: &Self::CheckedTerm,
    ) -> Result<Self::Theorem, Self::Error>;

    fn conclusion(&self, theorem: &Self::Theorem) -> SurfaceTerm;
}

#[cfg(test)]
mod tests {
    use super::{Link, SurfaceError, SurfaceTerm, SurfaceType, SurfaceVar};

    #[test]
    fn open_close_builds_capture_free_locally_nameless_body() {
        let x = SurfaceVar::new("x", SurfaceType::Nat);
        let body = SurfaceTerm::abs(
            SurfaceType::Bool,
            SurfaceTerm::app(SurfaceTerm::Bound(0), SurfaceTerm::open(x.clone())),
        );

        assert_eq!(
            body.close(&x).unwrap(),
            SurfaceTerm::abs(
                SurfaceType::Bool,
                SurfaceTerm::app(SurfaceTerm::Bound(0), SurfaceTerm::Bound(1)),
            )
        );
    }

    #[test]
    fn lazy_import_classifications_start_fully_closed() {
        let imported = SurfaceTerm::LazyImport {
            link: Link::new([1_u8, 2, 3]),
            ty: SurfaceType::Nat,
        };
        assert_eq!(imported.require_closed(), Ok(()));

        let x = SurfaceVar::new("x", SurfaceType::Nat);
        assert_eq!(
            SurfaceTerm::open(x).require_closed(),
            Err(SurfaceError::FreeVariable)
        );
    }

    #[test]
    fn dangling_bound_variables_are_rejected() {
        assert_eq!(
            SurfaceTerm::Bound(0).require_closed(),
            Err(SurfaceError::DanglingBoundVariable(0))
        );
        assert_eq!(
            SurfaceTerm::abs(SurfaceType::Nat, SurfaceTerm::Bound(0)).require_closed(),
            Ok(())
        );
    }
}
