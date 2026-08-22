//! Checked Ethane kernel wrapper.
//!
//! The executable boundary has a direct specification in
//! `Nucleus.Hol.Ethane.Arena.OneBased.Executable`:
//!
//! | Rust operation | Lean specification |
//! | --- | --- |
//! | `try_from_arena` | `Arena.RustValidAt`, `Arena.rustValid_sound` |
//! | `kind_at`, `ty_at`, `tm_at` | `RustKernel.IndexResult` |
//! | `star`, `bool_ty` | `RustKernel.StarResult`, `BoolTyResult` |
//! | `tm_fv`, `lam`, `app`, `eq`, `bool` | the corresponding `RustKernel.*Result` |
//! | import and reference methods | `ImportResult`, `KindRefResult`, `TyRefResult`, `TmRefResult` |
//! | `assume_valid`, `assume_wf` | `AssumeResult` |
//! | `assert_valid`, `assert_wf` | `AssertResult` |
//! | `add_context`, `add_axiom` | `ContextResult`, `AxiomResult` |
//! | `assert_eq` | `AssertEqResult`, `Kernel.Equality.ofMember` |
//! | equality symmetry, transitivity, application | `Kernel.Equality.symm`, `.trans`, `.app` |

use std::sync::Arc;

use crate::{
    Arena, Import, ImportId, Link, Meta, Ref, ResolveError, Resolver, Sort,
    resolve::{Syntax, Value, resolve_at},
    row::{Expr, Row},
};

/// A recoverable failure while validating an untrusted arena as a kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum KernelError<E> {
    TooManyDefinitions,
    TooManyImports,
    ForwardReference { owner: Ref, child: Ref },
    UnsupportedAxiom(String),
    InvalidSortingClaim(Ref),
    InvalidEqualityClaim(Ref),
    InvalidContext(Ref),
    InvalidConclusion(Meta),
    InvalidConstructor { expected: Sort, actual: Sort },
    MissingDefinition(Ref),
    ForeignEquality,
    EqualityEndpointMismatch,
    EqualityCongruenceMismatch,
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
            Self::TooManyImports => output.write_str("arena has more than u64::MAX imports"),
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
            Self::InvalidConstructor { expected, actual } => {
                write!(
                    output,
                    "constructor produced {actual:?}, expected {expected:?}"
                )
            }
            Self::MissingDefinition(reference) => {
                write!(output, "definition {} does not exist", reference.get())
            }
            Self::ForeignEquality => output.write_str("equality belongs to another kernel"),
            Self::EqualityEndpointMismatch => {
                output.write_str("equality proof endpoints do not compose")
            }
            Self::EqualityCongruenceMismatch => {
                output.write_str("application children do not match equality endpoints")
            }
            Self::Resolve(error) => write!(output, "could not resolve kernel data: {error:?}"),
        }
    }
}

impl<E: std::fmt::Debug + std::fmt::Display> std::error::Error for KernelError<E> {}

/// An arena whose exposed claims satisfy `OneBased.Arena.KernelValid`.
///
/// Raw CBOR decoding returns [`Arena`], never `Kernel`. Construction runs the
/// checked validation pass. The resolver is retained by the kernel, matching
/// the fixed resolver parameter of `OneBased.Kernel` in Lean. Consequently a
/// checked state cannot later be interpreted or extended with a different
/// resolver.
#[derive(Clone, Debug)]
pub struct Kernel<R> {
    arena: Arena,
    resolver: Arc<R>,
    identity: Arc<()>,
}

macro_rules! checked_index {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(Ref);

        impl $name {
            #[must_use]
            pub const fn reference(self) -> Ref {
                self.0
            }
        }
    };
}

checked_index!(KindIx);
checked_index!(TyIx);
checked_index!(TmIx);

/// An opaque equality capability owned by one checked kernel lineage.
#[derive(Clone, Debug)]
pub struct EqualityIx {
    identity: Arc<()>,
    left: Ref,
    right: Ref,
}

impl EqualityIx {
    #[must_use]
    pub const fn left(&self) -> Ref {
        self.left
    }

    #[must_use]
    pub const fn right(&self) -> Ref {
        self.right
    }
}

impl<R: Resolver> Kernel<R> {
    /// Validate an untrusted arena.
    ///
    /// The MVP accepts reflexive inline equality claims. Beta and congruence
    /// extend the equality checker without weakening this constructor.
    ///
    /// # Errors
    ///
    /// Returns the first failed representation, resolution, sorting, typing,
    /// equality, context, metadata, or axiom check.
    pub fn try_from_arena(
        arena: Arena,
        resolver: Arc<R>,
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
            validate_sort(&arena, resolver.as_ref(), reference, fuel)?;
            validate_reflexive_equality(&arena, resolver.as_ref(), reference, fuel)?;
        }

        for reference in arena.context() {
            let value = resolve_at(&arena, resolver.as_ref(), reference, fuel)?;
            if !is_checked_bool(&value) {
                return Err(KernelError::InvalidContext(reference));
            }
        }

        for record in arena.assertions() {
            if !validate_meta(&arena, &resolver, *record, fuel)? {
                return Err(KernelError::InvalidConclusion(*record));
            }
        }

        Ok(Self {
            arena,
            resolver,
            identity: Arc::new(()),
        })
    }

    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }

    #[must_use]
    pub fn resolver(&self) -> &R {
        self.resolver.as_ref()
    }

    /// Recover a checked kind handle for an existing definition.
    ///
    /// # Errors
    ///
    /// Returns an error when the reference is absent, unresolved, or not a
    /// well-formed kind.
    pub fn kind_at(&self, fuel: usize, reference: Ref) -> Result<KindIx, KernelError<R::Error>> {
        self.index_at(fuel, reference, Sort::Kind).map(KindIx)
    }

    /// Recover a checked type handle for an existing definition.
    ///
    /// # Errors
    ///
    /// Returns an error when the reference is absent, unresolved, or not a
    /// well-kinded type.
    pub fn ty_at(&self, fuel: usize, reference: Ref) -> Result<TyIx, KernelError<R::Error>> {
        self.index_at(fuel, reference, Sort::Ty).map(TyIx)
    }

    /// Recover a checked term handle for an existing definition.
    ///
    /// # Errors
    ///
    /// Returns an error when the reference is absent, unresolved, or not a
    /// well-typed term.
    pub fn tm_at(&self, fuel: usize, reference: Ref) -> Result<TmIx, KernelError<R::Error>> {
        self.index_at(fuel, reference, Sort::Tm).map(TmIx)
    }

    /// Append `kind.star` and recheck the resulting state.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation or kernel revalidation fails.
    pub fn star(&mut self, fuel: usize) -> Result<KindIx, KernelError<R::Error>> {
        self.push_checked(fuel, Row::new(Expr::KindStar), Sort::Kind)
            .map(KindIx)
    }

    /// Append the Boolean type and recheck the resulting state.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation or kernel revalidation fails.
    pub fn bool_ty(&mut self, fuel: usize) -> Result<TyIx, KernelError<R::Error>> {
        self.push_checked(fuel, Row::new(Expr::BoolTy), Sort::Ty)
            .map(TyIx)
    }

    /// Append a typed free term variable.
    ///
    /// # Errors
    ///
    /// Returns an error if the type handle is invalid or revalidation fails.
    pub fn tm_fv(
        &mut self,
        fuel: usize,
        name: u64,
        ty: TyIx,
    ) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::TmFv {
                name,
                ty: ty.reference(),
            }),
            Sort::Tm,
        )
        .map(TmIx)
    }

    /// Append a binary-binder term lambda.
    ///
    /// # Errors
    ///
    /// Returns an error if the operands do not form a typed lambda.
    pub fn lam(
        &mut self,
        fuel: usize,
        binder: TmIx,
        body: TmIx,
    ) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::Lam(binder.reference(), body.reference())),
            Sort::Tm,
        )
        .map(TmIx)
    }

    /// Append term application.
    ///
    /// # Errors
    ///
    /// Returns an error if the argument does not have the function's domain.
    pub fn app(
        &mut self,
        fuel: usize,
        function: TmIx,
        argument: TmIx,
    ) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::App(function.reference(), argument.reference())),
            Sort::Tm,
        )
        .map(TmIx)
    }

    /// Append object-language equality. The operand type is inferred.
    ///
    /// # Errors
    ///
    /// Returns an error if the operands do not have one strict common type.
    pub fn eq(
        &mut self,
        fuel: usize,
        left: TmIx,
        right: TmIx,
    ) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::Eq(left.reference(), right.reference())),
            Sort::Tm,
        )
        .map(TmIx)
    }

    /// Append either Boolean term.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation or kernel revalidation fails.
    pub fn bool(&mut self, fuel: usize, value: bool) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(fuel, Row::new(Expr::Bool(value)), Sort::Tm)
            .map(TmIx)
    }

    /// Add a checked Boolean term to the normalized assumption context.
    ///
    /// # Errors
    ///
    /// Returns an error unless the handle denotes a well-typed Boolean term
    /// in the current arena or complete revalidation fails.
    pub fn add_context(
        &mut self,
        fuel: usize,
        proposition: TmIx,
    ) -> Result<(), KernelError<R::Error>> {
        let value = resolve_at(&self.arena, self.resolver(), proposition.reference(), fuel)?;
        if !is_checked_bool(&value) {
            return Err(KernelError::InvalidContext(proposition.reference()));
        }
        let mut candidate = self.arena.clone();
        candidate.insert_context(proposition.reference());
        self.replace_arena_checked(candidate, fuel)
    }

    /// Enable one named axiom capability and revalidate the kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsupported capability name or if complete
    /// revalidation fails.
    pub fn add_axiom(&mut self, fuel: usize, name: &str) -> Result<(), KernelError<R::Error>> {
        if name != "ax.inf" {
            return Err(KernelError::UnsupportedAxiom(name.to_owned()));
        }
        let mut candidate = self.arena.clone();
        candidate.insert_axiom(name);
        self.replace_arena_checked(candidate, fuel)
    }

    /// Append a literal raw arena import. The import conveys no trust by
    /// itself.
    ///
    /// # Errors
    ///
    /// Returns an error if the import table overflows or the resulting state
    /// no longer validates.
    pub fn import_literal(
        &mut self,
        fuel: usize,
        arena: Arena,
    ) -> Result<ImportId, KernelError<R::Error>> {
        self.push_import_checked(fuel, Import::Literal(Box::new(arena)))
    }

    /// Append a lazy content-addressed import.
    ///
    /// # Errors
    ///
    /// Returns an error if the import table overflows or the resulting state
    /// no longer validates.
    pub fn import_link(
        &mut self,
        fuel: usize,
        link: Link,
    ) -> Result<ImportId, KernelError<R::Error>> {
        self.push_import_checked(fuel, Import::Link(link))
    }

    /// Append a checked term proxy into an import.
    ///
    /// # Errors
    ///
    /// Returns an error unless the foreign reference resolves to a
    /// well-typed term.
    pub fn tm_ref(
        &mut self,
        fuel: usize,
        source: ImportId,
        foreign: Ref,
    ) -> Result<TmIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::TmRef {
                src: source,
                ix: foreign,
            }),
            Sort::Tm,
        )
        .map(TmIx)
    }

    /// Append a checked type proxy into an import.
    ///
    /// # Errors
    ///
    /// Returns an error unless the foreign reference resolves to a
    /// well-kinded type.
    pub fn ty_ref(
        &mut self,
        fuel: usize,
        source: ImportId,
        foreign: Ref,
    ) -> Result<TyIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::TyRef {
                src: source,
                ix: foreign,
            }),
            Sort::Ty,
        )
        .map(TyIx)
    }

    /// Append a checked kind proxy into an import.
    ///
    /// # Errors
    ///
    /// Returns an error unless the foreign reference resolves to a kind.
    pub fn kind_ref(
        &mut self,
        fuel: usize,
        source: ImportId,
        foreign: Ref,
    ) -> Result<KindIx, KernelError<R::Error>> {
        self.push_checked(
            fuel,
            Row::new(Expr::KindRef {
                src: source,
                ix: foreign,
            }),
            Sort::Kind,
        )
        .map(KindIx)
    }

    /// Record imported-kernel validity as a premise. This does not promote it
    /// to a checked conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error if the existing conclusions cease to validate.
    pub fn assume_valid(
        &mut self,
        fuel: usize,
        source: ImportId,
    ) -> Result<(), KernelError<R::Error>> {
        self.push_meta_checked(fuel, Meta::Valid { src: source }, false)
    }

    /// Establish imported-kernel validity as a recursively checked
    /// conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error unless the import resolves to a valid kernel.
    pub fn assert_valid(
        &mut self,
        fuel: usize,
        source: ImportId,
    ) -> Result<(), KernelError<R::Error>> {
        self.push_meta_checked(fuel, Meta::Valid { src: source }, true)
    }

    /// Record foreign sorting as an explicit premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the existing conclusions cease to validate.
    pub fn assume_wf(
        &mut self,
        fuel: usize,
        source: ImportId,
        foreign: Ref,
        sort: Ref,
    ) -> Result<(), KernelError<R::Error>> {
        self.push_meta_checked(
            fuel,
            Meta::Wf {
                src: source,
                ix: foreign,
                sort,
            },
            false,
        )
    }

    /// Establish foreign sorting as a checked conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error unless the foreign expression has the supplied local
    /// classifier.
    pub fn assert_wf(
        &mut self,
        fuel: usize,
        source: ImportId,
        foreign: Ref,
        sort: Ref,
    ) -> Result<(), KernelError<R::Error>> {
        self.push_meta_checked(
            fuel,
            Meta::Wf {
                src: source,
                ix: foreign,
                sort,
            },
            true,
        )
    }

    /// Attach an equality assertion and recheck the complete state. The MVP
    /// accepts reflexivity and the checked identity-beta shape.
    ///
    /// # Errors
    ///
    /// Returns an error if either handle is invalid or the claim is unproved.
    pub fn assert_eq(
        &mut self,
        fuel: usize,
        left: TmIx,
        right: TmIx,
    ) -> Result<EqualityIx, KernelError<R::Error>> {
        let mut candidate = self.arena.clone();
        if !candidate.set_eq(left.reference(), right.reference()) {
            return Err(KernelError::MissingDefinition(left.reference()));
        }
        self.replace_arena_checked(candidate, fuel)?;
        Ok(self.equality(left.reference(), right.reference()))
    }

    /// Recover the checked equality attached to an inline member.
    ///
    /// # Errors
    ///
    /// Returns an error if the left reference has no such checked member.
    pub fn equality_at(&self, left: Ref, right: Ref) -> Result<EqualityIx, KernelError<R::Error>> {
        if self.arena.eq(left) != Some(right) {
            return Err(KernelError::InvalidEqualityClaim(left));
        }
        Ok(self.equality(left, right))
    }

    /// Apply symmetry to an opaque equality capability.
    ///
    /// # Errors
    ///
    /// Returns an error when the capability belongs to another kernel.
    pub fn equality_symm(
        &self,
        equality: &EqualityIx,
    ) -> Result<EqualityIx, KernelError<R::Error>> {
        self.check_equality_owner(equality)?;
        Ok(self.equality(equality.right, equality.left))
    }

    /// Compose two opaque equality capabilities.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign capabilities or mismatched middle
    /// endpoints.
    pub fn equality_trans(
        &self,
        left: &EqualityIx,
        right: &EqualityIx,
    ) -> Result<EqualityIx, KernelError<R::Error>> {
        self.check_equality_owner(left)?;
        self.check_equality_owner(right)?;
        if left.right != right.left {
            return Err(KernelError::EqualityEndpointMismatch);
        }
        Ok(self.equality(left.left, right.right))
    }

    /// Apply application congruence to two checked equality capabilities.
    ///
    /// The application rows must use the function and argument endpoints in
    /// the same order as the supplied capabilities. All six terms are checked
    /// again in the current arena before the result capability is returned.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign capabilities, mismatched application
    /// children, unresolved terms, or incompatible function and argument
    /// types.
    pub fn equality_app(
        &self,
        fuel: usize,
        left_app: TmIx,
        right_app: TmIx,
        function: &EqualityIx,
        argument: &EqualityIx,
    ) -> Result<EqualityIx, KernelError<R::Error>> {
        self.check_equality_owner(function)?;
        self.check_equality_owner(argument)?;

        let expected_left = Expr::App(function.left, argument.left);
        let expected_right = Expr::App(function.right, argument.right);
        if self.arena.row(left_app.reference()).map(Row::expr) != Some(&expected_left)
            || self.arena.row(right_app.reference()).map(Row::expr) != Some(&expected_right)
        {
            return Err(KernelError::EqualityCongruenceMismatch);
        }

        for reference in [
            left_app.reference(),
            right_app.reference(),
            function.left,
            function.right,
            argument.left,
            argument.right,
        ] {
            self.tm_at(fuel, reference)?;
        }

        let left_function = resolve_at(&self.arena, self.resolver(), function.left, fuel)?;
        let right_function = resolve_at(&self.arena, self.resolver(), function.right, fuel)?;
        let left_argument = resolve_at(&self.arena, self.resolver(), argument.left, fuel)?;
        let right_argument = resolve_at(&self.arena, self.resolver(), argument.right, fuel)?;
        let left_application =
            resolve_at(&self.arena, self.resolver(), left_app.reference(), fuel)?;
        let right_application =
            resolve_at(&self.arena, self.resolver(), right_app.reference(), fuel)?;

        let Value::Tm {
            ty: Syntax::Arr(domain, codomain),
            ..
        } = &left_function
        else {
            return Err(KernelError::EqualityCongruenceMismatch);
        };
        let compatible = matches!(&right_function,
            Value::Tm { ty, .. } if ty == &Syntax::Arr(domain.clone(), codomain.clone()))
            && matches!(&left_argument, Value::Tm { ty, .. } if ty == domain.as_ref())
            && matches!(&right_argument, Value::Tm { ty, .. } if ty == domain.as_ref())
            && matches!(&left_application, Value::Tm { ty, .. } if ty == codomain.as_ref())
            && matches!(&right_application, Value::Tm { ty, .. } if ty == codomain.as_ref());
        if !compatible {
            return Err(KernelError::EqualityCongruenceMismatch);
        }

        Ok(self.equality(left_app.reference(), right_app.reference()))
    }

    fn push_checked(
        &mut self,
        fuel: usize,
        row: Row,
        expected: Sort,
    ) -> Result<Ref, KernelError<R::Error>> {
        let mut candidate = self.arena.clone();
        let reference = candidate
            .push_row(row)
            .ok_or(KernelError::TooManyDefinitions)?;
        let actual = candidate.check_wf(self.resolver.as_ref(), reference, fuel)?;
        if actual != expected {
            return Err(KernelError::InvalidConstructor { expected, actual });
        }
        self.replace_arena_checked(candidate, fuel)?;
        Ok(reference)
    }

    fn push_import_checked(
        &mut self,
        fuel: usize,
        import: Import,
    ) -> Result<ImportId, KernelError<R::Error>> {
        let mut candidate = self.arena.clone();
        let source = candidate
            .push_import(import)
            .ok_or(KernelError::TooManyImports)?;
        self.replace_arena_checked(candidate, fuel)?;
        Ok(source)
    }

    fn push_meta_checked(
        &mut self,
        fuel: usize,
        record: Meta,
        conclusion: bool,
    ) -> Result<(), KernelError<R::Error>> {
        let mut candidate = self.arena.clone();
        if conclusion {
            candidate.push_assertion(record);
        } else {
            candidate.push_assumption(record);
        }
        self.replace_arena_checked(candidate, fuel)?;
        Ok(())
    }

    fn replace_arena_checked(
        &mut self,
        arena: Arena,
        fuel: usize,
    ) -> Result<(), KernelError<R::Error>> {
        let mut checked = Self::try_from_arena(arena, Arc::clone(&self.resolver), fuel)?;
        checked.identity = Arc::clone(&self.identity);
        *self = checked;
        Ok(())
    }

    fn equality(&self, left: Ref, right: Ref) -> EqualityIx {
        EqualityIx {
            identity: Arc::clone(&self.identity),
            left,
            right,
        }
    }

    fn check_equality_owner(&self, equality: &EqualityIx) -> Result<(), KernelError<R::Error>> {
        if Arc::ptr_eq(&self.identity, &equality.identity) {
            Ok(())
        } else {
            Err(KernelError::ForeignEquality)
        }
    }

    fn index_at(
        &self,
        fuel: usize,
        reference: Ref,
        expected: Sort,
    ) -> Result<Ref, KernelError<R::Error>> {
        if self.arena.tag(reference).is_none() {
            return Err(KernelError::MissingDefinition(reference));
        }
        let actual = self
            .arena
            .check_wf(self.resolver.as_ref(), reference, fuel)?;
        if actual != expected {
            return Err(KernelError::InvalidConstructor { expected, actual });
        }
        Ok(reference)
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
    if (left == right && left.is_well_formed()) || left.is_identity_beta_to(&right) {
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
    resolver: &Arc<R>,
    record: Meta,
    fuel: usize,
) -> Result<bool, KernelError<R::Error>> {
    Ok(match record {
        Meta::Valid { src } => {
            let arena = imported(owner, resolver.as_ref(), src)?;
            let remaining = fuel.checked_sub(1).ok_or(ResolveError::FuelExhausted)?;
            Kernel::try_from_arena((*arena).clone(), Arc::clone(resolver), remaining)?;
            true
        }
        Meta::Wf { src, ix, sort } => {
            let arena = imported(owner, resolver.as_ref(), src)?;
            let value = resolve_at(&arena, resolver.as_ref(), ix, fuel)?;
            let classifier = resolve_at(owner, resolver.as_ref(), sort, fuel)?;
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
        assert!(Kernel::try_from_arena(arena, Arc::new(NoLinks), 4).is_ok());
    }

    #[test]
    fn checked_identity_beta_is_accepted() {
        let arena = Arena::from_parts(
            vec![],
            [],
            vec![
                Row::new(Expr::BoolTy),
                Row::new(Expr::TmFv {
                    name: 7,
                    ty: reference(1),
                }),
                Row::new(Expr::Lam(reference(2), reference(2))),
                Row::new(Expr::Bool(true)),
                Row::new(Expr::App(reference(3), reference(4))).with_eq(reference(4)),
            ],
            [],
            vec![],
            vec![],
        );
        assert!(Kernel::try_from_arena(arena, Arc::new(NoLinks), 6).is_ok());
    }

    #[test]
    fn checked_mutations_build_the_beta_demo_without_forging() {
        let mut kernel = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 1).unwrap();
        let bool_ty = kernel.bool_ty(2).unwrap();
        let variable = kernel.tm_fv(3, 7, bool_ty).unwrap();
        let identity = kernel.lam(4, variable, variable).unwrap();
        let truth = kernel.bool(5, true).unwrap();
        let application = kernel.app(6, identity, truth).unwrap();
        let beta = kernel.assert_eq(6, application, truth).unwrap();
        let symmetric = kernel.equality_symm(&beta).unwrap();
        let transitive = kernel.equality_trans(&beta, &symmetric).unwrap();
        let identity_equality = kernel.assert_eq(7, identity, identity).unwrap();
        let truth_equality = kernel.assert_eq(7, truth, truth).unwrap();
        let second_application = kernel.app(8, identity, truth).unwrap();
        let congruent = kernel
            .equality_app(
                8,
                application,
                second_application,
                &identity_equality,
                &truth_equality,
            )
            .unwrap();
        kernel.add_context(8, truth).unwrap();
        kernel.add_context(8, truth).unwrap();
        kernel.add_axiom(8, "ax.inf").unwrap();
        kernel.add_axiom(8, "ax.inf").unwrap();
        let proposition = kernel.eq(7, application, truth).unwrap();

        assert_eq!(symmetric.left(), truth.reference());
        assert_eq!(symmetric.right(), application.reference());
        assert_eq!(transitive.left(), application.reference());
        assert_eq!(transitive.right(), application.reference());
        assert_eq!(congruent.left(), application.reference());
        assert_eq!(congruent.right(), second_application.reference());
        assert_eq!(
            kernel.arena().context().collect::<Vec<_>>(),
            vec![truth.reference()]
        );
        assert_eq!(kernel.arena().axioms().collect::<Vec<_>>(), vec!["ax.inf"]);

        assert_eq!(
            kernel.arena().tag(bool_ty.reference()),
            Some(crate::Tag::Ty(crate::TyTag::Bool))
        );
        assert_eq!(
            kernel.arena().tag(proposition.reference()),
            Some(crate::Tag::Tm(crate::TmTag::Eq))
        );
    }

    #[test]
    fn assumptions_are_not_promoted_and_bad_assertions_are_rejected() {
        let assumed = Meta::Wf {
            src: ImportId::new(1).unwrap(),
            ix: reference(1),
            sort: reference(1),
        };
        let arena = Arena::from_parts(vec![], [], vec![], [], vec![assumed], vec![]);
        assert!(Kernel::try_from_arena(arena, Arc::new(NoLinks), 1).is_ok());

        let asserted = Arena::from_parts(vec![], [], vec![], [], vec![], vec![assumed]);
        assert!(matches!(
            Kernel::try_from_arena(asserted, Arc::new(NoLinks), 1),
            Err(KernelError::Resolve(ResolveError::MissingImport(_)))
        ));
    }

    #[test]
    fn valid_metadata_checks_the_imported_kernel_recursively() {
        let valid = Arena::from_parts(
            vec![Import::Literal(Box::new(Arena::empty()))],
            [],
            vec![],
            [],
            vec![],
            vec![Meta::Valid {
                src: ImportId::new(1).unwrap(),
            }],
        );
        assert!(Kernel::try_from_arena(valid, Arc::new(NoLinks), 2).is_ok());

        let invalid_import = Arena::from_parts(
            vec![],
            ["ax.unknown".to_owned()],
            vec![],
            [],
            vec![],
            vec![],
        );
        let invalid = Arena::from_parts(
            vec![Import::Literal(Box::new(invalid_import))],
            [],
            vec![],
            [],
            vec![],
            vec![Meta::Valid {
                src: ImportId::new(1).unwrap(),
            }],
        );
        assert!(matches!(
            Kernel::try_from_arena(invalid, Arc::new(NoLinks), 2),
            Err(KernelError::UnsupportedAxiom(_))
        ));
    }

    #[test]
    fn checked_imports_keep_premises_and_conclusions_distinct() {
        let imported = Arena::from_parts(
            vec![],
            [],
            vec![Row::new(Expr::BoolTy), Row::new(Expr::Bool(true))],
            [],
            vec![],
            vec![],
        );
        let mut kernel = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 4).unwrap();
        let local_bool = kernel.bool_ty(4).unwrap();
        let source = kernel.import_literal(4, imported).unwrap();
        let imported_bool = kernel.ty_ref(4, source, reference(1)).unwrap();
        let imported_true = kernel.tm_ref(4, source, reference(2)).unwrap();

        kernel.assume_valid(4, source).unwrap();
        kernel.assert_valid(4, source).unwrap();
        kernel
            .assert_wf(4, source, reference(2), local_bool.reference())
            .unwrap();

        assert_eq!(
            kernel.arena().tag(imported_bool.reference()),
            Some(crate::Tag::Ty(crate::TyTag::Ref))
        );
        assert_eq!(
            kernel.arena().tag(imported_true.reference()),
            Some(crate::Tag::Tm(crate::TmTag::Ref))
        );
        assert_eq!(kernel.arena().assumptions(), &[Meta::Valid { src: source }]);
        assert_eq!(
            kernel.arena().assertions(),
            &[
                Meta::Valid { src: source },
                Meta::Wf {
                    src: source,
                    ix: reference(2),
                    sort: local_bool.reference(),
                },
            ]
        );
    }

    #[test]
    fn kind_references_are_checked_but_have_no_meta_wf_classifier() {
        let imported = Arena::from_parts(
            vec![],
            [],
            vec![Row::new(Expr::KindStar)],
            [],
            vec![],
            vec![],
        );
        let mut kernel = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 3).unwrap();
        let source = kernel.import_literal(3, imported).unwrap();
        assert!(kernel.kind_ref(3, source, reference(1)).is_ok());

        let bogus_sort = kernel.star(3).unwrap();
        assert!(matches!(
            kernel.assert_wf(3, source, reference(1), bogus_sort.reference()),
            Err(KernelError::InvalidConclusion(Meta::Wf { .. }))
        ));
    }

    #[test]
    fn equality_capabilities_cannot_cross_kernel_lineages() {
        let mut first = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 3).unwrap();
        let first_true = first.bool(3, true).unwrap();
        let equality = first.assert_eq(3, first_true, first_true).unwrap();

        let second = Kernel::try_from_arena(Arena::empty(), Arc::new(NoLinks), 1).unwrap();
        assert!(matches!(
            second.equality_symm(&equality),
            Err(KernelError::ForeignEquality)
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
            Kernel::try_from_arena(forward, Arc::new(NoLinks), 2),
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
            Kernel::try_from_arena(unchecked, Arc::new(NoLinks), 2),
            Err(KernelError::InvalidContext(_))
        ));
    }
}
