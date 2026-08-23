//! Minimal checked operations over Ethane arena rows.
//!
//! The arena is the only syntax representation. The kernel accepts and
//! returns plain local references, validates their tags and classifiers on
//! every call, and records equality classes directly in each row's `eq`
//! member. Concrete resolvers, caches, ergonomic typed objects, and indexes
//! over the union-find belong in userspace.

use std::convert::Infallible;

use covalence_lib_error::snafu::Snafu;
use smallvec::SmallVec;

use crate::{
    Arena, Import, ImportId, Link, Meta, Ref, ResolveError, Resolver, Sort, Tag,
    row::{Expr as Node, Row},
};

/// A recoverable failure at the checked kernel boundary.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum KernelError<E = Infallible>
where
    E: std::error::Error + 'static,
{
    /// The dense definition index no longer fits in `Ref`.
    #[snafu(display("kernel has too many definitions"))]
    TooManyDefinitions,
    /// The import index no longer fits in `ImportId`.
    #[snafu(display("kernel has too many imports"))]
    TooManyImports,
    /// A reference does not name a local row.
    #[snafu(display("reference {reference:?} does not name a kernel row"))]
    MissingDefinition {
        /// Missing local reference.
        reference: Ref,
    },
    /// A row belongs to another syntactic category.
    #[snafu(display("reference {reference:?} declares {actual:?}, but {expected:?} was required"))]
    WrongCategory {
        /// Reference being inspected.
        reference: Ref,
        /// Required category.
        expected: Sort,
        /// Category declared by the row tag.
        actual: Sort,
    },
    /// A type or term row has no classifier.
    #[snafu(display("reference {reference:?} has no sort member"))]
    MissingSort {
        /// Unclassified reference.
        reference: Ref,
    },
    /// A constructor requires a particular row form.
    #[snafu(display("reference {reference:?} has tag {actual:?}, but {expected} was required"))]
    WrongForm {
        /// Reference being inspected.
        reference: Ref,
        /// Required constructor form.
        expected: &'static str,
        /// Actual row tag.
        actual: Tag,
    },
    /// Two classifiers are not members of the same equality class.
    #[snafu(display("classifier {actual:?} is not equal to expected {expected:?}"))]
    ClassifierMismatch {
        /// Required classifier.
        expected: Ref,
        /// Supplied classifier.
        actual: Ref,
    },
    /// The requested axiom capability is unavailable in Ethane.
    #[snafu(display("unsupported axiom capability {name}"))]
    UnsupportedAxiom {
        /// Requested capability name.
        name: String,
    },
    /// Import resolution failed.
    #[snafu(transparent)]
    Resolve {
        /// Checked resolver failure.
        source: ResolveError<E>,
    },
}

/// An Ethane arena assembled only through checked row operations.
///
/// `Kernel` is non-generic and stores no resolver. Imported rows accept an
/// untrusted mutable resolver only for the call which introduces their local
/// proxy.
#[derive(Debug, Default)]
pub struct Kernel {
    arena: Arena,
}

#[derive(Clone, Copy)]
struct TypeBinding {
    left_name: u64,
    left_kind: Option<Ref>,
    right_name: u64,
    right_kind: Option<Ref>,
}

#[derive(Clone, Copy)]
struct TermBinding {
    left_name: u64,
    left_ty: Ref,
    right_name: u64,
    right_ty: Ref,
}

#[derive(Clone, Copy)]
struct TypedName {
    name: u64,
    classifier: Ref,
}

impl Kernel {
    /// Creates the empty checked kernel.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            arena: Arena::empty(),
        }
    }

    /// Borrows the underlying raw arena.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Forgets checked construction and returns the raw arena.
    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }

    /// Returns the syntactic category declared by a checked row.
    ///
    /// # Errors
    ///
    /// Returns an error if `reference` is absent.
    pub fn category(&self, reference: Ref) -> Result<Sort, KernelError> {
        self.category_as::<Infallible>(reference)
    }

    /// Returns the classifier recorded by a checked type or term row.
    ///
    /// # Errors
    ///
    /// Returns an error if `reference` is absent or has no classifier.
    pub fn classifier(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.classifier_as::<Infallible>(reference)
    }

    /// Finds the canonical member of a row's equality class.
    ///
    /// An acyclic class is represented by its root. If raw input contains a
    /// cycle, the smallest member of that cycle is canonical. A cycle is not a
    /// logical error: every edge still asserts equality between its endpoints.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn find(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.find_as::<Infallible>(reference)
    }

    /// Finds a canonical class member and compresses the traversed path.
    ///
    /// Cycles are normalized to a tree rooted at their smallest member.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn find_mut(&mut self, reference: Ref) -> Result<Ref, KernelError> {
        self.find_mut_as::<Infallible>(reference)
    }

    /// Compatibility name for immutable equality lookup.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing row or cross-category parent.
    pub fn representative(&self, reference: Ref) -> Result<Ref, KernelError> {
        self.find(reference)
    }

    /// Tests membership in one row equality class.
    ///
    /// # Errors
    ///
    /// Returns an error if either reference or its parent chain is malformed.
    pub fn equivalent(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.equivalent_as::<Infallible>(left, right)
    }

    /// Tests equality and compresses both traversed paths.
    ///
    /// # Errors
    ///
    /// Returns an error if either reference or parent chain is malformed.
    pub fn equivalent_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.equivalent_mut_as::<Infallible>(left, right)
    }

    /// Tests type equality using only the type-row union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked type rows.
    pub fn ty_eq(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Ty)?;
        self.require_category::<Infallible>(right, Sort::Ty)?;
        self.equivalent(left, right)
    }

    /// Tests type equality and compresses both type-row paths.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked type rows.
    pub fn ty_eq_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Ty)?;
        self.require_category::<Infallible>(right, Sort::Ty)?;
        self.equivalent_mut(left, right)
    }

    /// Tests term equality using only the term-row union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked term rows.
    pub fn tm_eq(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        self.equivalent(left, right)
    }

    /// Tests term equality and compresses both term-row paths.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are checked term rows.
    pub fn tm_eq_mut(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        self.equivalent_mut(left, right)
    }

    /// Appends `kind.star`.
    ///
    /// # Errors
    ///
    /// Returns an error if the dense reference space is exhausted.
    pub fn star(&mut self) -> Result<Ref, KernelError> {
        self.push::<Infallible>(Row::new(Node::KindStar))
    }

    /// Appends a kind arrow.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands are local kind rows.
    pub fn kind_arr(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(domain, Sort::Kind)?;
        self.require_category::<Infallible>(codomain, Sort::Kind)?;
        self.push::<Infallible>(Row::new(Node::KindArr(domain, codomain)))
    }

    /// Appends the Boolean type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `star` names `kind.star`.
    pub fn bool_ty(&mut self, star: Ref) -> Result<Ref, KernelError> {
        self.require_star::<Infallible>(star)?;
        self.push::<Infallible>(Row::new(Node::BoolTy).with_sort(star))
    }

    /// Appends a simple function type.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands are types of kind `star`.
    pub fn ty_arr(&mut self, domain: Ref, codomain: Ref) -> Result<Ref, KernelError> {
        let star = self.require_star_type::<Infallible>(domain)?;
        self.require_star_type::<Infallible>(codomain)?;
        self.push::<Infallible>(Row::new(Node::TyArr(domain, codomain)).with_sort(star))
    }

    /// Appends an intrinsically kinded free type variable.
    ///
    /// # Errors
    ///
    /// Returns an error unless `kind` is a local kind row.
    pub fn ty_fv(&mut self, name: u64, kind: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(kind, Sort::Kind)?;
        self.push::<Infallible>(Row::new(Node::TyFv { name, kind }).with_sort(kind))
    }

    /// Appends type-family application.
    ///
    /// Kinds are syntactic in Ethane, so the argument kind must be the exact
    /// domain reference of the function kind.
    ///
    /// # Errors
    ///
    /// Returns an error for non-type operands, a non-arrow function kind, or
    /// a kind mismatch.
    pub fn ty_app(&mut self, function: Ref, argument: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(function, Sort::Ty)?;
        self.require_category::<Infallible>(argument, Sort::Ty)?;
        let function_kind = self.classifier(function)?;
        let argument_kind = self.classifier(argument)?;
        let (domain, codomain) = self.kind_arrow::<Infallible>(function_kind)?;
        if argument_kind != domain {
            return Err(KernelError::ClassifierMismatch {
                expected: domain,
                actual: argument_kind,
            });
        }
        self.push::<Infallible>(Row::new(Node::TyApp(function, argument)).with_sort(codomain))
    }

    /// Appends a type-family abstraction and its arrow kind.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a free type-variable row.
    pub fn ty_lam(&mut self, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_form::<Infallible>(binder, "ty.fv", |node| matches!(node, Node::TyFv { .. }))?;
        self.require_category::<Infallible>(body, Sort::Ty)?;
        let domain = self.classifier(binder)?;
        let codomain = self.classifier(body)?;
        let kind = self.push::<Infallible>(Row::new(Node::KindArr(domain, codomain)))?;
        self.push::<Infallible>(Row::new(Node::TyLam(binder, body)).with_sort(kind))
    }

    /// Appends a guarded model type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` is a Boolean term.
    pub fn model(&mut self, name: u64, predicate: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
        let star = self.classifier(bool_ty)?;
        self.require_star::<Infallible>(star)?;
        self.push::<Infallible>(Row::new(Node::Model { name, predicate }).with_sort(star))
    }

    /// Appends type-level existential quantification.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` is a Boolean term.
    pub fn ty_exists(&mut self, name: u64, predicate: Ref) -> Result<Ref, KernelError> {
        let bool_ty = self.require_bool_term::<Infallible>(predicate)?;
        self.push::<Infallible>(Row::new(Node::TyExists { name, predicate }).with_sort(bool_ty))
    }

    /// Appends an intrinsically typed free term variable.
    ///
    /// # Errors
    ///
    /// Returns an error unless `ty` is a type of kind `star`.
    pub fn tm_fv(&mut self, name: u64, ty: Ref) -> Result<Ref, KernelError> {
        self.require_star_type::<Infallible>(ty)?;
        self.push::<Infallible>(Row::new(Node::TmFv { name, ty }).with_sort(ty))
    }

    /// Appends term application.
    ///
    /// The function type may be any member of an equality class containing a
    /// function type. Domain checking consults the same type union-find.
    ///
    /// # Errors
    ///
    /// Returns an error unless the function class contains an arrow and its
    /// domain is equal to the argument type.
    pub fn app(&mut self, function: Ref, argument: Ref) -> Result<Ref, KernelError> {
        self.require_category::<Infallible>(function, Sort::Tm)?;
        self.require_category::<Infallible>(argument, Sort::Tm)?;
        let function_ty = self.classifier(function)?;
        let argument_ty = self.classifier(argument)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(function_ty)?;
        if !self.equivalent(domain, argument_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: domain,
                actual: argument_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::App(function, argument)).with_sort(codomain))
    }

    /// Appends a term abstraction and its function type.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a free term-variable row and both
    /// endpoint types have kind `star`.
    pub fn lam(&mut self, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_form::<Infallible>(binder, "tm.fv", |node| matches!(node, Node::TmFv { .. }))?;
        self.require_category::<Infallible>(body, Sort::Tm)?;
        let domain = self.classifier(binder)?;
        let codomain = self.classifier(body)?;
        let function_ty = self.ty_arr(domain, codomain)?;
        self.push::<Infallible>(Row::new(Node::Lam(binder, body)).with_sort(function_ty))
    }

    /// Appends a Boolean literal.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` names a Boolean type row.
    pub fn bool(&mut self, bool_ty: Ref, value: bool) -> Result<Ref, KernelError> {
        self.require_bool_type::<Infallible>(bool_ty)?;
        self.push::<Infallible>(Row::new(Node::Bool(value)).with_sort(bool_ty))
    }

    /// Appends object-language equality.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operand types occupy one union-find class
    /// and `bool_ty` is Boolean.
    pub fn eq(&mut self, bool_ty: Ref, left: Ref, right: Ref) -> Result<Ref, KernelError> {
        self.require_bool_type::<Infallible>(bool_ty)?;
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        let left_ty = self.classifier(left)?;
        let right_ty = self.classifier(right)?;
        if !self.equivalent(left_ty, right_ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: left_ty,
                actual: right_ty,
            });
        }
        self.push::<Infallible>(Row::new(Node::Eq(left, right)).with_sort(bool_ty))
    }

    /// Appends Hilbert choice.
    ///
    /// # Errors
    ///
    /// Returns an error unless the predicate type class contains `ty → bool`.
    pub fn eps(&mut self, ty: Ref, predicate: Ref) -> Result<Ref, KernelError> {
        self.require_star_type::<Infallible>(ty)?;
        self.require_category::<Infallible>(predicate, Sort::Tm)?;
        let predicate_ty = self.classifier(predicate)?;
        let (domain, codomain) = self.type_arrow_member::<Infallible>(predicate_ty)?;
        if !self.equivalent(domain, ty)? {
            return Err(KernelError::ClassifierMismatch {
                expected: ty,
                actual: domain,
            });
        }
        self.require_bool_type::<Infallible>(codomain)?;
        self.push::<Infallible>(Row::new(Node::Eps { ty, predicate }).with_sort(ty))
    }

    /// Appends a literal arena import without asserting anything about it.
    ///
    /// # Errors
    ///
    /// Returns an error if the import reference space is exhausted.
    pub fn import_literal(&mut self, arena: Arena) -> Result<ImportId, KernelError> {
        self.push_import::<Infallible>(Import::Literal(Box::new(arena)))
    }

    /// Appends a lazy content-addressed import without resolving it.
    ///
    /// # Errors
    ///
    /// Returns an error if the import reference space is exhausted.
    pub fn import_link(&mut self, link: Link) -> Result<ImportId, KernelError> {
        self.push_import::<Infallible>(Import::Link(link))
    }

    /// Appends a kind proxy under an explicit imported-validity premise.
    ///
    /// # Errors
    ///
    /// Returns an error if resolution fails or the resolved row is not a kind.
    pub fn kind_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Kind {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Kind,
                actual: target,
            });
        }
        self.arena.push_assumption(Meta::Valid { src: source });
        self.push::<R::Error>(Row::new(Node::KindRef {
            src: source,
            ix: foreign,
        }))
    }

    /// Appends a type proxy under an explicit foreign-kinding premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the local kind is invalid, resolution fails, or the
    /// resolved row is not a type.
    pub fn ty_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
        kind: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        self.require_category::<R::Error>(kind, Sort::Kind)?;
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Ty {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Ty,
                actual: target,
            });
        }
        self.arena.push_assumption(Meta::Wf {
            src: source,
            ix: foreign,
            sort: kind,
        });
        self.push::<R::Error>(
            Row::new(Node::TyRef {
                src: source,
                ix: foreign,
            })
            .with_sort(kind),
        )
    }

    /// Appends a term proxy under an explicit foreign-typing premise.
    ///
    /// # Errors
    ///
    /// Returns an error if the local type is invalid, resolution fails, or the
    /// resolved row is not a term.
    pub fn tm_ref<R: Resolver + ?Sized>(
        &mut self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
        ty: Ref,
    ) -> Result<Ref, KernelError<R::Error>> {
        self.require_star_type::<R::Error>(ty)?;
        let target = self.resolve_foreign(resolver, source, foreign)?;
        if target != Sort::Tm {
            return Err(KernelError::WrongCategory {
                reference: foreign,
                expected: Sort::Tm,
                actual: target,
            });
        }
        self.arena.push_assumption(Meta::Wf {
            src: source,
            ix: foreign,
            sort: ty,
        });
        self.push::<R::Error>(
            Row::new(Node::TmRef {
                src: source,
                ix: foreign,
            })
            .with_sort(ty),
        )
    }

    /// Adds a checked Boolean term to the logical context.
    ///
    /// # Errors
    ///
    /// Returns an error unless `proposition` is a Boolean term.
    pub fn add_context(&mut self, proposition: Ref) -> Result<(), KernelError> {
        self.require_bool_term::<Infallible>(proposition)?;
        self.arena.insert_context(proposition);
        Ok(())
    }

    /// Enables the Ethane infinity axiom capability.
    ///
    /// # Errors
    ///
    /// Returns an error for every currently unsupported name.
    pub fn add_axiom(&mut self, name: &str) -> Result<(), KernelError> {
        if name != "ax.inf" {
            return Err(KernelError::UnsupportedAxiom {
                name: name.to_owned(),
            });
        }
        self.arena.insert_axiom(name);
        Ok(())
    }

    /// Unions two type rows after an alpha-equivalence check.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are types and the direct named
    /// syntax checker establishes alpha-equivalence.
    pub fn ty_alpha(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Ty)?;
        self.require_category::<Infallible>(right, Sort::Ty)?;
        if !self.alpha_equivalent(left, right)? {
            return Ok(false);
        }
        self.union::<Infallible>(left, right)?;
        Ok(true)
    }

    /// Unions two term rows after an alpha-equivalence check.
    ///
    /// # Errors
    ///
    /// Returns an error unless both references are terms with equal types and
    /// the direct named syntax checker establishes alpha-equivalence.
    pub fn tm_alpha(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        self.require_category::<Infallible>(left, Sort::Tm)?;
        self.require_category::<Infallible>(right, Sort::Tm)?;
        let left_ty = self.classifier(left)?;
        let right_ty = self.classifier(right)?;
        if !self.equivalent(left_ty, right_ty)? {
            if !self.alpha_equivalent(left_ty, right_ty)? {
                return Ok(false);
            }
            self.union::<Infallible>(left_ty, right_ty)?;
        }
        if !self.alpha_equivalent(left, right)? {
            return Ok(false);
        }
        self.union::<Infallible>(left, right)?;
        Ok(true)
    }

    fn alpha_equivalent(&self, left: Ref, right: Ref) -> Result<bool, KernelError> {
        let fuel = self.arena.len().saturating_add(1);
        self.alpha_at::<Infallible>(left, right, &[], &[], fuel)
    }

    fn alpha_at<E>(
        &self,
        left: Ref,
        right: Ref,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if left == right {
            return Ok(true);
        }
        if fuel == 0 {
            return Ok(false);
        }
        let left_row = self.row::<E>(left)?;
        let right_row = self.row::<E>(right)?;
        match (left_row.tag().sort(), right_row.tag().sort()) {
            (Sort::Kind, Sort::Kind) => self.alpha_kind(
                *left_row.expr(),
                *right_row.expr(),
                type_scope,
                term_scope,
                fuel - 1,
            ),
            (Sort::Ty, Sort::Ty) => self.alpha_type(
                *left_row.expr(),
                *right_row.expr(),
                type_scope,
                term_scope,
                fuel - 1,
            ),
            (Sort::Tm, Sort::Tm) => self.alpha_term(
                *left_row.expr(),
                *right_row.expr(),
                type_scope,
                term_scope,
                fuel - 1,
            ),
            _ => Ok(false),
        }
    }

    fn alpha_kind<E>(
        &self,
        left: Node,
        right: Node,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match (left, right) {
            (Node::KindStar, Node::KindStar) => Ok(true),
            (Node::KindArr(a, b), Node::KindArr(c, d)) => Ok(self
                .alpha_at(a, c, type_scope, term_scope, fuel)?
                && self.alpha_at(b, d, type_scope, term_scope, fuel)?),
            (
                Node::KindRef {
                    src: left_source,
                    ix: left_foreign,
                },
                Node::KindRef {
                    src: right_source,
                    ix: right_foreign,
                },
            ) => Ok(left_source == right_source && left_foreign == right_foreign),
            _ => Ok(false),
        }
    }

    fn alpha_type<E>(
        &self,
        left: Node,
        right: Node,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match (left, right) {
            (Node::BoolTy, Node::BoolTy) => Ok(true),
            (Node::TyArr(a, b), Node::TyArr(c, d)) | (Node::TyApp(a, b), Node::TyApp(c, d)) => {
                Ok(self.alpha_at(a, c, type_scope, term_scope, fuel)?
                    && self.alpha_at(b, d, type_scope, term_scope, fuel)?)
            }
            (Node::TyLam(left_binder, left_body), Node::TyLam(right_binder, right_body)) => {
                let (left_name, left_kind) = self.ty_variable::<E>(left_binder)?;
                let (right_name, right_kind) = self.ty_variable::<E>(right_binder)?;
                if self.alpha_at(left_kind, right_kind, type_scope, term_scope, fuel)? {
                    let mut scope = type_scope.to_vec();
                    scope.push(TypeBinding {
                        left_name,
                        left_kind: Some(left_kind),
                        right_name,
                        right_kind: Some(right_kind),
                    });
                    self.alpha_at(left_body, right_body, &scope, term_scope, fuel)
                } else {
                    Ok(false)
                }
            }
            (
                Node::TyFv {
                    name: left_name,
                    kind: left_kind,
                },
                Node::TyFv {
                    name: right_name,
                    kind: right_kind,
                },
            ) => self.alpha_type_variable(
                TypedName {
                    name: left_name,
                    classifier: left_kind,
                },
                TypedName {
                    name: right_name,
                    classifier: right_kind,
                },
                type_scope,
                term_scope,
                fuel,
            ),
            (
                Node::Model {
                    name: left_name,
                    predicate: left_predicate,
                },
                Node::Model {
                    name: right_name,
                    predicate: right_predicate,
                },
            ) => {
                let mut scope = type_scope.to_vec();
                scope.push(TypeBinding {
                    left_name,
                    left_kind: None,
                    right_name,
                    right_kind: None,
                });
                self.alpha_at(left_predicate, right_predicate, &scope, term_scope, fuel)
            }
            (
                Node::TyRef {
                    src: left_source,
                    ix: left_foreign,
                },
                Node::TyRef {
                    src: right_source,
                    ix: right_foreign,
                },
            ) => Ok(left_source == right_source && left_foreign == right_foreign),
            _ => Ok(false),
        }
    }

    fn alpha_term<E>(
        &self,
        left: Node,
        right: Node,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match (left, right) {
            (Node::Bool(left), Node::Bool(right)) => Ok(left == right),
            (Node::App(a, b), Node::App(c, d)) | (Node::Eq(a, b), Node::Eq(c, d)) => Ok(self
                .alpha_at(a, c, type_scope, term_scope, fuel)?
                && self.alpha_at(b, d, type_scope, term_scope, fuel)?),
            (Node::Lam(left_binder, left_body), Node::Lam(right_binder, right_body)) => {
                let (left_name, left_ty) = self.tm_variable::<E>(left_binder)?;
                let (right_name, right_ty) = self.tm_variable::<E>(right_binder)?;
                if self.alpha_at(left_ty, right_ty, type_scope, term_scope, fuel)? {
                    let mut scope = term_scope.to_vec();
                    scope.push(TermBinding {
                        left_name,
                        left_ty,
                        right_name,
                        right_ty,
                    });
                    self.alpha_at(left_body, right_body, type_scope, &scope, fuel)
                } else {
                    Ok(false)
                }
            }
            (
                Node::TmFv {
                    name: left_name,
                    ty: left_ty,
                },
                Node::TmFv {
                    name: right_name,
                    ty: right_ty,
                },
            ) => self.alpha_term_variable(
                TypedName {
                    name: left_name,
                    classifier: left_ty,
                },
                TypedName {
                    name: right_name,
                    classifier: right_ty,
                },
                type_scope,
                term_scope,
                fuel,
            ),
            (
                Node::TyExists {
                    name: left_name,
                    predicate: left_predicate,
                },
                Node::TyExists {
                    name: right_name,
                    predicate: right_predicate,
                },
            ) => {
                let mut scope = type_scope.to_vec();
                scope.push(TypeBinding {
                    left_name,
                    left_kind: None,
                    right_name,
                    right_kind: None,
                });
                self.alpha_at(left_predicate, right_predicate, &scope, term_scope, fuel)
            }
            (
                Node::Eps {
                    ty: left_ty,
                    predicate: left_predicate,
                },
                Node::Eps {
                    ty: right_ty,
                    predicate: right_predicate,
                },
            ) => Ok(
                self.alpha_at(left_ty, right_ty, type_scope, term_scope, fuel)?
                    && self.alpha_at(
                        left_predicate,
                        right_predicate,
                        type_scope,
                        term_scope,
                        fuel,
                    )?,
            ),
            (
                Node::TmRef {
                    src: left_source,
                    ix: left_foreign,
                },
                Node::TmRef {
                    src: right_source,
                    ix: right_foreign,
                },
            ) => Ok(left_source == right_source && left_foreign == right_foreign),
            _ => Ok(false),
        }
    }

    fn alpha_type_variable<E>(
        &self,
        left: TypedName,
        right: TypedName,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        for binding in type_scope.iter().rev() {
            if binding.left_name == left.name
                && self.alpha_optional_kind(
                    left.classifier,
                    binding.left_kind,
                    type_scope,
                    term_scope,
                    fuel,
                )?
            {
                return Ok(binding.right_name == right.name
                    && self.alpha_optional_kind(
                        right.classifier,
                        binding.right_kind,
                        type_scope,
                        term_scope,
                        fuel,
                    )?);
            }
        }
        Ok(left.name == right.name
            && self.alpha_at(
                left.classifier,
                right.classifier,
                type_scope,
                term_scope,
                fuel,
            )?)
    }

    fn alpha_optional_kind<E>(
        &self,
        actual: Ref,
        expected: Option<Ref>,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        match expected {
            Some(expected) => self.alpha_at(actual, expected, type_scope, term_scope, fuel),
            None => Ok(matches!(self.row::<E>(actual)?.expr(), Node::KindStar)),
        }
    }

    fn alpha_term_variable<E>(
        &self,
        left: TypedName,
        right: TypedName,
        type_scope: &[TypeBinding],
        term_scope: &[TermBinding],
        fuel: usize,
    ) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        for binding in term_scope.iter().rev() {
            if binding.left_name == left.name
                && self.alpha_at(
                    left.classifier,
                    binding.left_ty,
                    type_scope,
                    term_scope,
                    fuel,
                )?
            {
                return Ok(binding.right_name == right.name
                    && self.alpha_at(
                        right.classifier,
                        binding.right_ty,
                        type_scope,
                        term_scope,
                        fuel,
                    )?);
            }
        }
        Ok(left.name == right.name
            && self.alpha_at(
                left.classifier,
                right.classifier,
                type_scope,
                term_scope,
                fuel,
            )?)
    }

    fn resolve_foreign<R: Resolver + ?Sized>(
        &self,
        resolver: &mut R,
        source: ImportId,
        foreign: Ref,
    ) -> Result<Sort, KernelError<R::Error>> {
        self.arena
            .resolve_foreign(resolver, source, foreign)
            .map(|expression| expression.tag().sort())
            .map_err(|source| KernelError::Resolve { source })
    }

    fn push<E>(&mut self, row: Row) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .push_row(row)
            .ok_or(KernelError::TooManyDefinitions)
    }

    fn push_import<E>(&mut self, import: Import) -> Result<ImportId, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .push_import(import)
            .ok_or(KernelError::TooManyImports)
    }

    fn row<E>(&self, reference: Ref) -> Result<&Row, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .row(reference)
            .ok_or(KernelError::MissingDefinition { reference })
    }

    fn category_as<E>(&self, reference: Ref) -> Result<Sort, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.arena
            .tag(reference)
            .map(Tag::sort)
            .ok_or(KernelError::MissingDefinition { reference })
    }

    fn classifier_as<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.row::<E>(reference)?
            .sort()
            .ok_or(KernelError::MissingSort { reference })
    }

    fn require_category<E>(&self, reference: Ref, expected: Sort) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let actual = self.category_as::<E>(reference)?;
        if actual == expected {
            Ok(())
        } else {
            Err(KernelError::WrongCategory {
                reference,
                expected,
                actual,
            })
        }
    }

    fn require_form<E>(
        &self,
        reference: Ref,
        expected: &'static str,
        predicate: impl FnOnce(&Node) -> bool,
    ) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if predicate(row.expr()) {
            Ok(())
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected,
                actual: row.tag(),
            })
        }
    }

    fn require_star<E>(&self, reference: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_form(reference, "kind.star", |node| {
            matches!(node, Node::KindStar)
        })
    }

    fn require_star_type<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Ty)?;
        let kind = self.classifier_as::<E>(reference)?;
        self.require_star(kind)?;
        Ok(kind)
    }

    fn require_bool_type<E>(&self, reference: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_star_type(reference)?;
        let representative = self.find_as::<E>(reference)?;
        for candidate in self.references::<E>()? {
            if self.find_as::<E>(candidate)? == representative
                && matches!(self.row::<E>(candidate)?.expr(), Node::BoolTy)
            {
                return Ok(());
            }
        }
        Err(KernelError::WrongForm {
            reference,
            expected: "a type class containing ty.bool",
            actual: self.row::<E>(reference)?.tag(),
        })
    }

    fn require_bool_term<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Tm)?;
        let ty = self.classifier_as::<E>(reference)?;
        self.require_bool_type(ty)?;
        Ok(ty)
    }

    fn kind_arrow<E>(&self, reference: Ref) -> Result<(Ref, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if let Node::KindArr(domain, codomain) = *row.expr() {
            Ok((domain, codomain))
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected: "kind.arr",
                actual: row.tag(),
            })
        }
    }

    fn type_arrow_member<E>(&self, reference: Ref) -> Result<(Ref, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.require_category(reference, Sort::Ty)?;
        let representative = self.find_as::<E>(reference)?;
        for candidate in self.references::<E>()? {
            if self.category_as::<E>(candidate)? == Sort::Ty
                && self.find_as::<E>(candidate)? == representative
                && let Node::TyArr(domain, codomain) = *self.row::<E>(candidate)?.expr()
            {
                return Ok((domain, codomain));
            }
        }
        Err(KernelError::WrongForm {
            reference,
            expected: "a type class containing ty.arr",
            actual: self.row::<E>(reference)?.tag(),
        })
    }

    fn ty_variable<E>(&self, reference: Ref) -> Result<(u64, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if let Node::TyFv { name, kind } = *row.expr() {
            Ok((name, kind))
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected: "ty.fv",
                actual: row.tag(),
            })
        }
    }

    fn tm_variable<E>(&self, reference: Ref) -> Result<(u64, Ref), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let row = self.row::<E>(reference)?;
        if let Node::TmFv { name, ty } = *row.expr() {
            Ok((name, ty))
        } else {
            Err(KernelError::WrongForm {
                reference,
                expected: "tm.fv",
                actual: row.tag(),
            })
        }
    }

    fn find_path<E>(&self, reference: Ref) -> Result<(Ref, SmallVec<[Ref; 8]>), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let category = self.category_as::<E>(reference)?;
        let mut path = SmallVec::<[Ref; 8]>::new();
        let mut current = reference;
        loop {
            if let Some(cycle_start) = path.iter().position(|member| *member == current) {
                let representative = path[cycle_start..]
                    .iter()
                    .copied()
                    .min()
                    .expect("a repeated member starts a nonempty cycle");
                return Ok((representative, path));
            }
            path.push(current);
            let Some(parent) = self.row::<E>(current)?.eq() else {
                return Ok((current, path));
            };
            let parent_category = self.category_as::<E>(parent)?;
            if parent_category != category {
                return Err(KernelError::WrongCategory {
                    reference: parent,
                    expected: category,
                    actual: parent_category,
                });
            }
            current = parent;
        }
    }

    fn find_as<E>(&self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        self.find_path(reference)
            .map(|(representative, _)| representative)
    }

    fn find_mut_as<E>(&mut self, reference: Ref) -> Result<Ref, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let (representative, path) = self.find_path(reference)?;
        for member in path {
            let parent = (member != representative).then_some(representative);
            let recorded = self.arena.set_eq(member, parent);
            debug_assert!(recorded, "find path contains only resident rows");
        }
        Ok(representative)
    }

    fn equivalent_as<E>(&self, left: Ref, right: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if self.category_as::<E>(left)? != self.category_as::<E>(right)? {
            return Ok(false);
        }
        Ok(self.find_as::<E>(left)? == self.find_as::<E>(right)?)
    }

    fn equivalent_mut_as<E>(&mut self, left: Ref, right: Ref) -> Result<bool, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        if self.category_as::<E>(left)? != self.category_as::<E>(right)? {
            return Ok(false);
        }
        Ok(self.find_mut_as::<E>(left)? == self.find_mut_as::<E>(right)?)
    }

    fn union<E>(&mut self, left: Ref, right: Ref) -> Result<(), KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        let left_root = self.find_mut_as::<E>(left)?;
        let right_root = self.find_mut_as::<E>(right)?;
        if left_root == right_root {
            return Ok(());
        }
        let (child, parent) = if left_root > right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        let recorded = self.arena.set_eq(child, Some(parent));
        debug_assert!(recorded, "union roots name resident rows");
        Ok(())
    }

    fn references<E>(&self) -> Result<Vec<Ref>, KernelError<E>>
    where
        E: std::error::Error + 'static,
    {
        (1..=self.arena.len())
            .map(|position| {
                u64::try_from(position)
                    .ok()
                    .and_then(Ref::new)
                    .ok_or(KernelError::TooManyDefinitions)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{KindTag, LinkFormat, Table, TmTag, TyTag};

    struct OneTable(Table);

    impl Resolver for OneTable {
        type Error = Infallible;

        fn resolve(&mut self, _: &Link) -> Result<Table, Self::Error> {
            Ok(self.0.clone())
        }
    }

    #[test]
    fn constructs_typed_rows_using_only_local_references() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let variable = kernel.tm_fv(0, bool_ty).unwrap();
        let identity = kernel.lam(variable, variable).unwrap();
        let truth = kernel.bool(bool_ty, true).unwrap();
        let application = kernel.app(identity, truth).unwrap();
        let equation = kernel.eq(bool_ty, application, truth).unwrap();
        kernel.add_context(equation).unwrap();

        assert_eq!(kernel.classifier(application).unwrap(), bool_ty);
        assert_eq!(kernel.arena().tag(identity), Some(Tag::Tm(TmTag::Lam)));
        assert_eq!(kernel.arena().context().collect::<Vec<_>>(), [equation]);
    }

    #[test]
    fn constructs_higher_kinded_rows() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let arrow = kernel.kind_arr(star, star).unwrap();
        let family = kernel.ty_fv(0, arrow).unwrap();
        let argument = kernel.ty_fv(1, star).unwrap();
        let application = kernel.ty_app(family, argument).unwrap();
        let abstraction = kernel.ty_lam(argument, application).unwrap();

        assert_eq!(kernel.classifier(application).unwrap(), star);
        assert_eq!(kernel.arena().tag(abstraction), Some(Tag::Ty(TyTag::Lam)));
        assert_eq!(
            kernel.arena().tag(kernel.classifier(abstraction).unwrap()),
            Some(Tag::Kind(KindTag::Arr))
        );
    }

    #[test]
    fn alpha_equivalence_unions_rows_directly() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let left_var = kernel.tm_fv(1, bool_ty).unwrap();
        let left = kernel.lam(left_var, left_var).unwrap();
        let right_var = kernel.tm_fv(2, bool_ty).unwrap();
        let right = kernel.lam(right_var, right_var).unwrap();

        assert!(!kernel.tm_eq(left, right).unwrap());
        assert!(kernel.tm_alpha(left, right).unwrap());
        assert!(kernel.tm_eq(left, right).unwrap());
        assert_eq!(
            kernel.representative(left).unwrap(),
            kernel.representative(right).unwrap()
        );
    }

    #[test]
    fn alpha_renames_model_binders_without_using_the_equality_class() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();

        let left_ty = kernel.ty_fv(1, star).unwrap();
        let left_value = kernel.tm_fv(0, left_ty).unwrap();
        let left_predicate = kernel.eq(bool_ty, left_value, left_value).unwrap();
        let left = kernel.model(1, left_predicate).unwrap();

        let right_ty = kernel.ty_fv(2, star).unwrap();
        let right_value = kernel.tm_fv(0, right_ty).unwrap();
        let right_predicate = kernel.eq(bool_ty, right_value, right_value).unwrap();
        let right = kernel.model(2, right_predicate).unwrap();

        assert!(kernel.ty_alpha(left, right).unwrap());

        let falsehood = kernel.bool(bool_ty, false).unwrap();
        let different = kernel.model(2, falsehood).unwrap();
        assert!(!kernel.ty_alpha(left, different).unwrap());
    }

    #[test]
    fn equality_cycles_have_a_canonical_member_and_can_be_compressed() {
        let mut kernel = Kernel::new();
        let left = kernel.star().unwrap();
        let right = kernel.star().unwrap();
        assert!(kernel.arena.set_eq(left, Some(right)));
        assert!(kernel.arena.set_eq(right, Some(left)));

        assert_eq!(kernel.find(left).unwrap(), left);
        assert_eq!(kernel.find(right).unwrap(), left);
        assert_eq!(kernel.find_mut(right).unwrap(), left);
        assert_eq!(kernel.arena.eq(left), None);
        assert_eq!(kernel.arena.eq(right), Some(left));
    }

    #[test]
    fn imported_rows_are_local_proxies_with_explicit_premises() {
        let mut imported = Kernel::new();
        let imported_star = imported.star().unwrap();
        let imported_bool_ty = imported.bool_ty(imported_star).unwrap();
        let imported_truth = imported.bool(imported_bool_ty, true).unwrap();
        let table = Table::from_arena(imported.into_arena()).unwrap();

        let mut owner = Kernel::new();
        let star = owner.star().unwrap();
        let bool_ty = owner.bool_ty(star).unwrap();
        let source = owner
            .import_link(Link {
                format: LinkFormat::Cbor,
                blake3: table.address(),
            })
            .unwrap();
        let mut resolver = OneTable(table);
        let proxy = owner
            .tm_ref(&mut resolver, source, imported_truth, bool_ty)
            .unwrap();

        assert_eq!(owner.arena().tag(proxy), Some(Tag::Tm(TmTag::Ref)));
        assert_eq!(
            owner.arena().assumptions(),
            [Meta::Wf {
                src: source,
                ix: imported_truth,
                sort: bool_ty,
            }]
        );
    }
}
