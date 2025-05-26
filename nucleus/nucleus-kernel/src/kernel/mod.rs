use egg::Id;
use thiserror::Error;
use typed_generational_arena::{SmallArena, SmallIndex};

mod ctx;
use ctx::*;

use crate::term::Close;
pub use crate::term::ULevel;

/// An instance of the `nucleus` kernel
#[derive(Default, Clone)]
pub struct Kernel {
    /// This kernel's currently active contexts
    ctx: SmallArena<Ctx>,
}

/// # Context Management
///
/// Functions for creating, editing, inspecting and deleting contexts
impl Kernel {
    /// Construct a new context
    ///
    /// # Example
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.parent(ctx), None);
    /// let child = ker.new_ctx(Some(ctx)).unwrap();
    /// assert_eq!(ker.parent(child), Some(ctx));
    /// ```
    pub fn new_ctx(&mut self, parent: Option<CtxId>) -> Result<CtxId, Error> {
        if let Some(parent) = parent {
            self.check_ctx(parent)?;
        }
        Ok(CtxId(self.ctx.insert(Ctx::new(parent))))
    }

    /// Add a parameter to a context
    ///
    /// Returns the new parameter's index
    pub fn add_param(&mut self, ctx: CtxId, param: TermId, erased: bool) -> Result<u32, Error> {
        self.ctx[ctx.0].add_param(param, erased)
    }

    /// Get a parameter's type
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.param_ty(ctx, 0), Err(Error::InvalidParam(0)));
    /// assert_eq!(ker.param_ty(ctx, 1), Err(Error::InvalidParam(1)));
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// assert_eq!(ker.add_param(ctx, set, false), Ok(0));
    /// assert_eq!(ker.param_ty(ctx, 0), Ok(set));
    /// assert_eq!(ker.param_ty(ctx, 1), Err(Error::InvalidParam(1)));
    /// ```
    pub fn param_ty(&self, ctx: CtxId, ix: u32) -> Result<TermId, Error> {
        self.ctx[ctx.0].param_ty(ix).ok_or(Error::InvalidParam(ix))
    }

    /// Get whether a parameter is erased
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.param_erased(ctx, 0), Err(Error::InvalidParam(0)));
    /// assert_eq!(ker.param_erased(ctx, 1), Err(Error::InvalidParam(1)));
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// assert_eq!(ker.add_param(ctx, set, true), Ok(0));
    /// assert_eq!(ker.param_erased(ctx, 0), Ok(true));
    /// assert_eq!(ker.param_erased(ctx, 1), Err(Error::InvalidParam(1)));
    /// ```
    pub fn param_erased(&self, ctx: CtxId, ix: u32) -> Result<bool, Error> {
        self.ctx[ctx.0]
            .param_erased(ix)
            .ok_or(Error::InvalidParam(ix))
    }

    /// Get the current number of parameters for a context
    ///
    /// # Example
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.num_params(ctx), 0);
    /// ```
    pub fn num_params(&self, ctx: CtxId) -> usize {
        self.ctx[ctx.0].num_params()
    }

    /// Get a context's parent
    pub fn parent(&self, ctx: CtxId) -> Option<CtxId> {
        self.ctx[ctx.0].parent()
    }

    /// Check whether a context is clean
    pub fn is_clean(&self, ctx: CtxId) -> bool {
        self.ctx[ctx.0].is_clean()
    }

    /// Check whether a context is sealed
    pub fn is_sealed(&self, ctx: CtxId) -> bool {
        self.ctx[ctx.0].is_sealed()
    }

    /// Seal a context
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert!(!ker.is_sealed(ctx));
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert_eq!(ker.add_param(ctx, prop, false), Ok(0));
    /// assert!(!ker.is_sealed(ctx));
    /// ker.seal(ctx);
    /// assert!(ker.is_sealed(ctx));
    /// assert!(ker.add_param(ctx, prop, false).is_err());
    /// ```
    pub fn seal(&mut self, ctx: CtxId) {
        self.ctx[ctx.0].seal()
    }

    /// Rebuild a context
    pub fn rebuild(&mut self, ctx: CtxId) -> usize {
        self.ctx[ctx.0].rebuild()
    }

    /// Check whether a context is valid
    ///
    /// The behaviour of this function is unspecified if mixing contexts between kernels
    ///
    /// # Example
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.check_ctx(ctx), Ok(()));
    /// ker.free_ctx(ctx);
    /// assert!(ker.check_ctx(ctx).is_err());
    /// ```
    pub fn check_ctx(&self, ctx: CtxId) -> Result<(), Error> {
        if !self.ctx.contains(ctx.0) {
            return Err(Error::InvalidContext(
                "did not find context (Kernel::check_ctx)",
            ));
        }
        Ok(())
    }

    /// Delete a context
    ///
    /// Returns whether any changes were made
    ///
    /// # Example
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert!(ker.free_ctx(ctx));
    /// assert!(!ker.free_ctx(ctx));
    /// ```
    pub fn free_ctx(&mut self, ctx: CtxId) -> bool {
        self.ctx.remove(ctx.0).is_some()
    }
}

/// # Term Management
///
/// Functions for creating, editing, and inspecting terms in a given context
impl Kernel {
    /// Insert a node into a context
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let x = ker.add(ctx, Node::Bv(0));
    /// let u = ker.add(ctx, Node::U(ULevel::SET));
    /// let emp = ker.add(ctx, Node::Pi([u, x]));
    /// assert_eq!(ker.node(ctx, x), Node::Bv(0));
    /// assert_eq!(ker.node(ctx, u), Node::U(ULevel::SET));
    /// assert_eq!(ker.node(ctx, emp), Node::Pi([u, x]));
    /// ```
    pub fn add(&mut self, ctx: CtxId, node: Node) -> TermId {
        self.ctx[ctx.0].add(node)
    }

    /// Get the equivalence class of a node
    pub fn repr(&mut self, ctx: CtxId, node: Node) -> TermId {
        self.ctx[ctx.0].repr(node)
    }

    /// Get the node corresponding to a term
    pub fn node(&self, ctx: CtxId, tm: TermId) -> Node {
        self.ctx[ctx.0].node(tm)
    }

    /// Try to lookup a node in this context
    pub fn lookup(&self, ctx: CtxId, node: Node) -> Option<TermId> {
        self.ctx[ctx.0].lookup(node)
    }

    /// Find the current representative of a term
    pub fn find(&self, ctx: CtxId, tm: TermId) -> TermId {
        self.ctx[ctx.0].find(tm)
    }

    /// Check whether two terms are equal in a given context
    pub fn eq_in(&self, ctx: CtxId, lhs: TermId, rhs: TermId) -> bool {
        self.ctx[ctx.0].eq(lhs, rhs)
    }

    /// Get whether a term is syntax
    pub fn is_syntax(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_syntax(tm)
    }

    /// Get whether a term is a well-formed term
    pub fn is_tm(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_tm(tm)
    }

    /// Get whether a term is a type
    pub fn is_ty(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_ty(tm)
    }

    /// Get whether a term is a proposition
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// assert!(ker.is_prop(ctx, tt));
    /// assert!(ker.is_prop(ctx, ff));
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// // The type of propositions is _not_ itself a proposition!
    /// assert!(!ker.is_prop(ctx, prop));
    /// // _But_ its truncation _is_
    /// let t = ker.check_trunc(ctx, prop).unwrap();
    /// assert!(ker.is_prop(ctx, t));
    /// ```
    pub fn is_prop(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_prop(tm)
    }

    /// Get whether a term is a proof of a proposition
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let e_prop = ker.check_epsilon(ctx, prop).unwrap();
    /// assert!(!ker.is_proof(ctx, e_prop));
    /// let e_tt = ker.check_epsilon(ctx, tt).unwrap();
    /// assert!(ker.is_proof(ctx, e_tt));
    /// ```
    pub fn is_proof(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_proof(tm)
    }

    /// Get whether a term is a sort
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// assert!(!ker.is_sort(ctx, tt));
    /// assert!(ker.is_sort(ctx, prop));
    /// assert!(ker.is_sort(ctx, set));
    /// ```
    pub fn is_sort(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_sort(tm)
    }

    /// Check whether a term is an inhabited type
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert!(ker.is_inhab(ctx, tt));
    /// assert!(!ker.is_inhab(ctx, ff));
    /// assert!(ker.is_inhab(ctx, prop));
    /// ```
    pub fn is_inhab(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_inhab(tm)
    }

    /// Check whether a term is an empty type
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert!(!ker.is_empty(ctx, tt));
    /// assert!(ker.is_empty(ctx, ff));
    /// assert!(!ker.is_empty(ctx, prop));
    /// ```
    pub fn is_empty(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_empty(tm)
    }

    /// Get this term as a sort
    ///
    /// Returns `None` if this term is not a sort
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let set = ker.add(ctx, Node::U(ULevel::SET));
    /// assert_eq!(ker.as_sort(ctx, set), Some(ULevel::SET));
    /// let prop = ker.add(ctx, Node::U(ULevel::PROP));
    /// assert_eq!(ker.as_sort(ctx, prop), Some(ULevel::PROP));
    /// let tt = ker.add(ctx, Node::Bool(true));
    /// assert_eq!(ker.as_sort(ctx, tt), None);
    /// ```
    pub fn as_sort(&self, ctx: CtxId, tm: TermId) -> Option<ULevel> {
        self.ctx[ctx.0].as_sort(tm)
    }

    /// Get this term's sort
    ///
    /// Returns `None` if this term is not a type
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let set = ker.add(ctx, Node::U(ULevel::SET));
    /// assert_eq!(ker.sort(ctx, set), Some(ULevel::SET.succ()));
    /// let prop = ker.add(ctx, Node::U(ULevel::PROP));
    /// assert_eq!(ker.sort(ctx, prop), Some(ULevel::SET));
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// assert_eq!(ker.sort(ctx, tt), Some(ULevel::PROP));
    /// ```
    pub fn sort(&self, ctx: CtxId, tm: TermId) -> Option<ULevel> {
        self.ctx[ctx.0].sort(tm)
    }

    /// Get the upper bound for this term's bound variables
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let x = ker.add(ctx, Node::Bv(0));
    /// let u = ker.add(ctx, Node::U(ULevel::SET));
    /// let emp = ker.add(ctx, Node::Pi([u, x]));
    /// assert_eq!(ker.bv(ctx, x), 1);
    /// assert_eq!(ker.bv(ctx, u), 0);
    /// assert_eq!(ker.bv(ctx, emp), 0);
    /// let y = ker.add(ctx, Node::Bv(1));
    /// let t = ker.add(ctx, Node::Pi([u, y]));
    /// assert_eq!(ker.bv(ctx, y), 2);
    /// assert_eq!(ker.bv(ctx, t), 1);
    /// ```
    pub fn bv(&self, ctx: CtxId, tm: TermId) -> u16 {
        self.ctx[ctx.0].bv(tm)
    }

    /// Get whether a term is locally-closed
    ///
    /// `a` is locally closed if and only if `bv(a) == 0`
    pub fn is_lc(&self, ctx: CtxId, tm: TermId) -> bool {
        self.ctx[ctx.0].is_lc(tm)
    }
}

/// # Type checking
///
/// Functions for constructing well-typed terms
impl Kernel {
    /// Check a term has a given type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ A ≡ B
    /// ===
    /// Γ ⊢ a : B
    /// ```
    pub fn check_ty(&mut self, ctx: CtxId, term: TermId, ty: TermId) -> Result<(), Error> {
        if self.ctx[ctx.0].check_ty(term, ty) {
            Ok(())
        } else {
            Err(Error::TypeMismatch("Kernel::check_ty"))
        }
    }

    /// Typecheck a parameter to a context
    ///
    /// Corresponds to the rule
    /// ```text
    /// (x : A) ∈ Δ
    /// Δ ≤ Γ
    /// ===
    /// Γ ⊢ x : A
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert!(ker.check_param(ctx, ctx, 0, prop).is_err());
    /// assert_eq!(ker.add_param(ctx, prop, false), Ok(0));
    /// let x = ker.check_param(ctx, ctx, 0, prop).unwrap();
    /// assert_eq!(ker.check_ty(ctx, x, prop), Ok(()));
    /// ```
    pub fn check_param(
        &mut self,
        ctx: CtxId,
        src: CtxId,
        ix: u32,
        ty: TermId,
    ) -> Result<TermId, Error> {
        if ctx != src {
            return Err(Error::NotImplemented(
                "Kernel::check_param (foreign parameter)",
            ));
        }
        let param_ty = self.param_ty(ctx, ix)?;
        if !self.eq_in(ctx, param_ty, ty) {
            return Err(Error::TypeMismatch("Kernel::check_param (type)"));
        }
        let result = self.add(ctx, Node::Cv(ctx, ix));
        self.ctx[ctx.0].set_ty(result, param_ty);
        Ok(result)
    }

    /// Typecheck a universe
    ///
    /// Corresponds to the rule
    /// ```text
    /// ===
    /// Γ ⊢ U n : U (n + 1)
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let u = ker.check_u(ctx, ULevel::SET).unwrap();
    /// assert_eq!(ker.node(ctx, u), Node::U(ULevel::SET));
    /// assert!(ker.is_ty(ctx, u));
    /// let u1 = ker.check_u(ctx, ULevel::SET.succ()).unwrap();
    /// assert_eq!(ker.node(ctx, u1), Node::U(ULevel::SET.succ()));
    /// assert_eq!(ker.check_ty(ctx, u, u1), Ok(()))
    /// ```
    pub fn check_u(&mut self, ctx: CtxId, level: ULevel) -> Result<TermId, Error> {
        let result = self.add(ctx, Node::U(level));
        let ty = self.add(ctx, Node::U(level.succ()));
        debug_assert!(self.is_ty(ctx, result));
        debug_assert!(self.is_ty(ctx, ty));
        self.ctx[ctx.0].set_ty(result, ty);
        Ok(result)
    }

    /// Typecheck a dependent function type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ B : U m
    /// ===
    /// Γ ⊢ Π x : A. B : U (imax n m)
    /// ```
    /// Automatically inserts the following facts, if possible:
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ B : U m
    /// Γ, x : A ⊢ B inhab
    /// ===
    /// Γ ⊢ Π x : A . B inhab
    /// ```
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ B : U m
    /// Γ ⊢ A empty
    /// ===
    /// Γ ⊢ Π x : A . B inhab
    /// ```
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ B : U m
    /// Γ ⊢ A inhab
    /// Γ, x : A ⊢ B empty
    /// ===
    /// Γ ⊢ Π x : A . B empty
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let b2b = ker.check_pi(ctx, prop, prop).unwrap();
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// assert_eq!(ker.check_ty(ctx, b2b, set), Ok(()));
    /// assert!(ker.is_inhab(ctx, b2b));
    /// ```
    pub fn check_pi(&mut self, ctx: CtxId, param: TermId, body: TermId) -> Result<TermId, Error> {
        let Some(param_sort) = self.sort(ctx, param) else {
            return Err(Error::ExpectedType("Kernel::check_pi (param)"));
        };
        let Some(body_sort) = self.sort_under_binder(ctx, param, body) else {
            return Err(Error::ExpectedType("Kernel::check_pi (body)"));
        };
        let result_sort = param_sort.imax(body_sort);
        let result_ty = self.check_u(ctx, result_sort)?;
        let result = self.add(ctx, Node::Pi([param, body]));
        self.ctx[ctx.0].set_ty(result, result_ty);
        if self.is_empty(ctx, param) || self.inhab_under_binder(ctx, param, body) {
            self.ctx[ctx.0].set_inhab(result);
            if result_sort == ULevel::PROP {
                let tt = self.check_bool(ctx, true).unwrap();
                self.ctx[ctx.0].union(result, tt);
            }
        }
        if self.is_inhab(ctx, param) && self.empty_under_binder(ctx, param, body) {
            self.ctx[ctx.0].set_empty(result);
            if result_sort == ULevel::PROP {
                let ff = self.check_bool(ctx, false).unwrap();
                self.ctx[ctx.0].union(result, ff);
            }
        }
        Ok(result)
    }

    /// Typecheck a lambda abstraction
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ t : B
    /// ===
    /// Γ ⊢ λ x : A. t : Π x : A. B
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let att = ker.check_abs(ctx, prop, tt, prop).unwrap();
    /// let aff = ker.check_abs(ctx, prop, ff, prop).unwrap();
    /// let b2b = ker.check_pi(ctx, prop, prop).unwrap();
    /// assert_eq!(ker.check_ty(ctx, att, b2b), Ok(()));
    /// assert_eq!(ker.check_ty(ctx, aff, b2b), Ok(()));
    /// assert_ne!(att, aff);
    /// ```
    pub fn check_abs(
        &mut self,
        ctx: CtxId,
        param: TermId,
        body: TermId,
        body_ty: TermId,
    ) -> Result<TermId, Error> {
        if self.check_under_binder(ctx, param, body, body_ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_abs (body)"));
        }
        let result_ty = self.check_pi(ctx, param, body_ty)?;
        let result = self.add(ctx, Node::Abs([param, body]));
        self.ctx[ctx.0].set_ty(result, result_ty);
        Ok(result)
    }

    /// Typecheck an application
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ, x : A ⊢ B : U m
    /// Γ ⊢ s : Π x : A. B
    /// Γ ⊢ t : A
    /// Γ ⊢ [t/x]B ≡ C : U l
    /// ===
    /// Γ ⊢ s t : C
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let att = ker.check_abs(ctx, prop, tt, prop).unwrap();
    /// let tta = ker.check_app(ctx, prop, prop, att, tt, prop).unwrap();
    /// assert_eq!(ker.check_ty(ctx, tta, prop), Ok(()));
    /// assert!(ker.check_app(ctx, prop, tt, att, tt, prop).is_err());
    /// ```
    pub fn check_app(
        &mut self,
        ctx: CtxId,
        arg_ty: TermId,
        body_ty: TermId,
        func: TermId,
        arg: TermId,
        result_ty: TermId,
    ) -> Result<TermId, Error> {
        if self.check_ty(ctx, arg, arg_ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_app (arg)"));
        }
        let Some(body_sort) = self.sort_under_binder(ctx, arg_ty, body_ty) else {
            return Err(Error::ExpectedType("Kernel::check_app (body_ty)"));
        };
        let function_ty = self.check_pi(ctx, arg_ty, body_ty)?;
        if self.check_ty(ctx, func, function_ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_app (func)"));
        }
        if !self.check_eq_subst0_in(ctx, result_ty, arg, body_ty) {
            return Err(Error::TypeMismatch("Kernel::check_app (result)"));
        }
        let body_sort_id = self.check_u(ctx, body_sort).unwrap();
        self.ctx[ctx.0].set_ty(result_ty, body_sort_id);
        debug_assert!(self.is_ty(ctx, result_ty));
        debug_assert_eq!(self.sort(ctx, result_ty), Some(body_sort));
        let result = self.add(ctx, Node::App([arg_ty, body_ty, func, arg]));
        self.ctx[ctx.0].set_ty(result, result_ty);
        Ok(result)
    }

    /// Typecheck a let-binding
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ ⊢ a : A
    /// Γ, x : A ⊢ b : B
    /// Γ ⊢ [a/x]B ≡ C : U m
    /// ===
    /// Γ ⊢ let x : A = a in b : C
    /// ```
    /// We automatically insert the following equations, if possible:
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ ⊢ a : A
    /// Γ, _ : A ⊢ b : B
    /// Γ ⊢ [a/x]B ≡ C : U m
    /// ===
    /// Γ ⊢ let x : A = a in b ≡ b : C
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let ff2 = ker.check_let(ctx, prop, tt, ff, prop, prop).unwrap();
    /// assert!(ker.eq_in(ctx, ff, ff2));
    /// assert!(!ker.eq_in(ctx, tt, ff2));
    /// ```
    pub fn check_let(
        &mut self,
        ctx: CtxId,
        bound_ty: TermId,
        bound: TermId,
        body: TermId,
        body_ty: TermId,
        result_ty: TermId,
    ) -> Result<TermId, Error> {
        if self.check_ty(ctx, bound, bound_ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_let (bound)"));
        }
        let Some(body_sort) = self.sort_under_binder(ctx, bound, body_ty) else {
            return Err(Error::ExpectedType("Kernel::check_app (body_ty)"));
        };
        if self
            .check_under_binder(ctx, bound_ty, body, body_ty)
            .is_err()
        {
            return Err(Error::TypeMismatch("Kernel::check_let (body)"));
        }
        if !self.check_eq_subst0_in(ctx, result_ty, bound, body_ty) {
            return Err(Error::TypeMismatch("Kernel::check_let (result)"));
        }
        let body_sort_id = self.check_u(ctx, body_sort).unwrap();
        self.ctx[ctx.0].set_ty(result_ty, body_sort_id);
        debug_assert!(self.is_ty(ctx, result_ty));
        debug_assert_eq!(self.sort(ctx, result_ty), Some(body_sort));
        let result = self.add(ctx, Node::Let([bound_ty, bound, body]));
        self.ctx[ctx.0].set_ty(result, result_ty);
        if self.is_lc(ctx, body) {
            self.ctx[ctx.0].union(result, body);
        }
        Ok(result)
    }

    /// Typecheck an identity type
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// ===
    /// Γ ⊢ a = b : Prop
    /// ```
    /// We automatically insert the following equations, if possible:
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// Γ ⊢ a ≡ b : A
    /// ===
    /// Γ ⊢ (a = b) ≡ ⊤ : Prop
    /// ```
    /// ```text
    /// Γ ⊢ A : U n
    /// Γ ⊢ a : A
    /// Γ ⊢ b : A
    /// incompatible(a, b)
    /// ===
    /// Γ ⊢ (a = b) ≡ ⊥ : Prop
    /// ```
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// for x in [tt, ff] {
    ///     for y in [tt, ff] {
    ///         let eq = ker.check_is(ctx, prop, x, y).unwrap();
    ///         assert_eq!(ker.node(ctx, eq), Node::Is([prop, x, y]));
    ///         assert!(ker.is_prop(ctx, eq));
    ///         assert_eq!(ker.check_ty(ctx, eq, prop), Ok(()));
    ///         assert_eq!(ker.eq_in(ctx, eq, tt), x == y);
    ///     }
    /// }
    /// ```
    pub fn check_is(
        &mut self,
        ctx: CtxId,
        ty: TermId,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<TermId, Error> {
        if self.check_ty(ctx, lhs, ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_is (lhs)"));
        }
        debug_assert!(self.is_ty(ctx, ty));
        if self.check_ty(ctx, rhs, ty).is_err() {
            return Err(Error::TypeMismatch("Kernel::check_is (rhs)"));
        }
        let result_ty = self.check_u(ctx, ULevel::PROP)?;
        let result = self.add(ctx, Node::Is([result_ty, lhs, rhs]));
        self.ctx[ctx.0].set_ty(result, result_ty);
        debug_assert!(self.is_ty(ctx, result));
        if self.eq_in(ctx, lhs, rhs) {
            let tt = self.check_bool(ctx, true).unwrap();
            self.ctx[ctx.0].union(result, tt);
        }
        if self.node(ctx, lhs).incompatible(&self.node(ctx, rhs)) {
            let ff = self.check_bool(ctx, false).unwrap();
            self.ctx[ctx.0].union(result, ff);
        }
        Ok(result)
    }

    /// Typecheck an annotation
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ A ≡ B
    /// ===
    /// Γ ⊢ (a : B) : B
    /// ```
    /// Automatically inserts the following equations:
    /// ```text
    /// Γ ⊢ a : A
    /// Γ ⊢ A ≡ B
    /// ===
    /// Γ ⊢ (a : B) ≡ a : B
    /// ```
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let tta = ker.check_annot(ctx, tt, prop).unwrap();
    /// assert_ne!(tt, tta);
    /// assert!(ker.eq_in(ctx, tta, tt));
    /// ```
    pub fn check_annot(&mut self, ctx: CtxId, term: TermId, ty: TermId) -> Result<TermId, Error> {
        if !self.ctx[ctx.0].check_ty(term, ty) {
            return Err(Error::TypeMismatch("Kernel::check_annot"));
        };
        let result = self.add(ctx, Node::Annot([term, ty]));
        self.ctx[ctx.0].set_ty(result, ty);
        self.ctx[ctx.0].union(result, term);
        Ok(result)
    }

    /// Typecheck a boolean
    ///
    /// Corresponds to the rule
    /// ```text
    /// b ∈ {⊤, ⊥}
    /// ===
    /// Γ ⊢ b : Prop
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// assert_ne!(tt, ff);
    /// assert_eq!(ker.node(ctx, tt), Node::Bool(true));
    /// assert_eq!(ker.node(ctx, ff), Node::Bool(false));
    /// let p = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert_eq!(ker.check_ty(ctx, tt, p), Ok(()));
    /// assert_eq!(ker.check_ty(ctx, ff, p), Ok(()));
    /// ```
    pub fn check_bool(&mut self, ctx: CtxId, b: bool) -> Result<TermId, Error> {
        let result = self.add(ctx, Node::Bool(b));
        debug_assert!(self.is_ty(ctx, result));
        let ty = self.add(ctx, Node::U(ULevel::PROP));
        debug_assert!(self.is_ty(ctx, ty));
        self.ctx[ctx.0].set_ty(result, ty);
        debug_assert_eq!(self.check_ty(ctx, result, ty), Ok(()));
        Ok(result)
    }

    /// Typecheck a dependent-if-then-else
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ b : Prop
    /// Γ ⊢ A : U n
    /// Γ, x : b = ⊤ ⊢ s : A
    /// Γ, y : b = ⊥ ⊢ t : A
    /// ===
    /// Γ ⊢ dite b A s t : A
    /// ```
    /// We automatically insert the following equations, if possible:
    /// ```text
    /// Γ ⊢ b : Prop
    /// Γ ⊢ A : U n
    /// Γ ⊢ b ≡ ⊤ : Prop
    /// Γ, _ : b = ⊤ ⊢ s : A
    /// Γ, y : b = ⊥ ⊢ t : A
    /// ===
    /// Γ ⊢ dite b A s t ≡ s : A
    /// ```
    /// ```text
    /// Γ ⊢ b : Prop
    /// Γ ⊢ A : U n
    /// Γ ⊢ b ≡ ⊥ : Prop
    /// Γ, x : b = ⊤ ⊢ s : A
    /// Γ, _ : b = ⊥ ⊢ t : A
    /// ===
    /// Γ ⊢ dite b A s t ≡ t : A
    /// ```
    /// ```text
    /// Γ ⊢ b : Prop
    /// Γ ⊢ A : U n
    /// Γ, _ : b = ⊤ ⊢ t : A
    /// Γ, _ : b = ⊥ ⊢ t : A
    /// ===
    /// Γ ⊢ dite b A t t ≡ t : A
    /// ```
    /// If the variables `x` and `y` are used in the body of `s` or `t` respectively, we need to use
    /// the corresponding β-rule for dependent-if-then-else to avoid unnecessary substitutions.
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let not_tt = ker.check_dite(ctx, tt, prop, ff, tt).unwrap();
    /// assert_ne!(not_tt, ff);
    /// assert!(ker.eq_in(ctx, not_tt, ff));
    /// ```
    pub fn check_dite(
        &mut self,
        ctx: CtxId,
        disc: TermId,
        ty: TermId,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<TermId, Error> {
        if !self.is_prop(ctx, disc) {
            return Err(Error::ExpectedType("Kernel::check_dite (disc)"));
        }
        // Note that we avoid generating equalities in the common case
        let prop = self.check_u(ctx, ULevel::PROP)?;
        let tt = self.check_bool(ctx, true)?;
        let ff = self.check_bool(ctx, false)?;
        if !self.check_ty(ctx, lhs, ty).is_err() {
            let disc_eq_tt = self.check_is(ctx, prop, disc, tt)?;
            if self.check_under_binder(ctx, disc_eq_tt, lhs, ty).is_err() {
                return Err(Error::TypeMismatch("Kernel::check_dite (lhs)"));
            }
        }
        if !self.check_ty(ctx, rhs, ty).is_err() {
            let disc_eq_ff = self.check_is(ctx, prop, disc, ff)?;
            if self.check_under_binder(ctx, disc_eq_ff, rhs, ty).is_err() {
                return Err(Error::TypeMismatch("Kernel::check_dite (rhs)"));
            }
        }
        let result = self.add(ctx, Node::Dite([disc, ty, lhs, rhs]));
        self.ctx[ctx.0].set_ty(result, ty);
        if (lhs == rhs || self.eq_in(ctx, disc, tt)) && self.is_lc(ctx, lhs) {
            self.ctx[ctx.0].union(result, lhs);
        }
        if self.eq_in(ctx, disc, ff) && self.is_lc(ctx, rhs) {
            self.ctx[ctx.0].union(result, rhs);
        }
        Ok(result)
    }

    /// Typecheck a propositional truncation
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A : U n
    /// ===
    /// Γ ⊢ ∃A : Prop
    /// ```
    /// We automatically insert the following equations, if possible:
    /// ```text
    /// Γ ⊢ A inhab
    /// ===
    /// Γ ⊢ ∃A ≡ ⊤ : Prop
    /// ```
    /// ```text
    /// Γ ⊢ A empty
    /// ===
    /// Γ ⊢ ∃A ≡ ⊥ : Prop
    /// ```
    /// ```text
    /// Γ ⊢ A : Prop
    /// ===
    /// Γ ⊢ ∃A ≡ A : Prop
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// let ttp = ker.check_trunc(ctx, tt).unwrap();
    /// let ffp = ker.check_trunc(ctx, ff).unwrap();
    /// assert!(ker.eq_in(ctx, ttp, tt));
    /// assert!(ker.eq_in(ctx, ffp, ff));
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// let setp = ker.check_trunc(ctx, set).unwrap();
    /// assert!(ker.eq_in(ctx, setp, tt));
    /// ```
    pub fn check_trunc(&mut self, ctx: CtxId, ty: TermId) -> Result<TermId, Error> {
        if !self.is_ty(ctx, ty) {
            return Err(Error::ExpectedType("Kernel::check_trunc"));
        }
        let result = self.add(ctx, Node::Trunc([ty]));
        let result_ty = self.add(ctx, Node::U(ULevel::PROP));
        self.ctx[ctx.0].set_ty(result, result_ty);
        debug_assert!(self.is_ty(ctx, result));
        if self.is_prop(ctx, ty) {
            self.ctx[ctx.0].union(result, ty);
        }
        if self.is_inhab(ctx, ty) {
            let tt = self.check_bool(ctx, true).unwrap();
            self.ctx[ctx.0].union(result, tt);
        }
        if self.is_empty(ctx, ty) {
            let ff = self.check_bool(ctx, false).unwrap();
            self.ctx[ctx.0].union(result, ff);
        }
        Ok(result)
    }

    /// Typecheck Hilbert's ε operator
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ A inhab
    /// ===
    /// Γ ⊢ ε A : A
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let tt = ker.check_bool(ctx, true).unwrap();
    /// let nil = ker.check_epsilon(ctx, tt).unwrap();
    /// assert_eq!(ker.check_ty(ctx, nil, tt), Ok(()));
    /// let ff = ker.check_bool(ctx, false).unwrap();
    /// assert!(ker.check_epsilon(ctx, ff).is_err());
    /// ```
    pub fn check_epsilon(&mut self, ctx: CtxId, ty: TermId) -> Result<TermId, Error> {
        if !self.is_inhab(ctx, ty) {
            return Err(Error::ExpectedInhab("Kernel::check_epsilon"));
        }
        let result = self.add(ctx, Node::Epsilon([ty]));
        self.ctx[ctx.0].set_ty(result, ty);
        Ok(result)
    }

    /// Check a structure
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ ⊢ Δ ok (U n)
    /// ===
    /// Γ ⊢ struct(Δ) : U n
    /// ```
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let child = ker.new_ctx(Some(ctx)).unwrap();
    /// ```
    pub fn check_struct(&mut self, parent: CtxId, child: CtxId) -> Result<TermId, Error> {
        if self.parent(child).is_some_and(|x| x != parent) {
            return Err(Error::NotImplemented("Kernel::check_struct (chain)"));
        }
        if !self.is_sealed(child) {
            return Err(Error::InvalidContext("Kernel::check_struct (not sealed)"));
        }
        let result = self.add(parent, Node::Struct(child));
        let sort = self.ctx_sort(child);
        let result_ty = self.check_u(parent, sort).expect("sort is valid");
        self.ctx[parent.0].set_ty(result, result_ty);
        Ok(result)
    }
}

/// # Equations
///
/// Functions for constructing equations between terms
impl Kernel {}

/// A context parameter
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Param {
    /// This parameter's type
    pub ty: TermId,
    /// Whether this parameter is erased
    ///
    /// An erased parameter is marked inhabited, _but_ cannot appear in terms.
    ///
    /// This is useful for handing propositional parameters, e.g. in a dependent if-then-else
    pub erased: bool,
}

/// A subcontext ID
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SubCtxId(TermId);

/// # Substitutions
///
/// Functions for constructing substitutions and subcontexts
impl Kernel {
    /// Get the sort of this context
    pub fn ctx_sort(&self, ctx: CtxId) -> ULevel {
        self.ctx[ctx.0].ctx_sort()
    }

    /// Get the length of a subcontext
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let nil = ker.nil_subctx(ctx);
    /// assert_eq!(ker.subctx_len(ctx, nil), Some(0));
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// let sc1 = ker.cons_subctx(ctx, nil, prop);
    /// assert_eq!(ker.subctx_len(ctx, sc1), Some(1));
    /// let set = ker.check_u(ctx, ULevel::SET).unwrap();
    /// let sc2 = ker.cons_subctx(ctx, sc1, set);
    /// assert_eq!(ker.subctx_len(ctx, sc2), Some(2));
    /// let sc2_ = ker.cons_subctx(ctx, sc1, prop);
    /// assert_eq!(ker.subctx_len(ctx, sc2_), Some(2));
    /// ```
    pub fn subctx_len(&self, ctx: CtxId, subctx: SubCtxId) -> Option<u16> {
        self.ctx[ctx.0].subctx_len(subctx)
    }

    /// Destruct a subcontext
    pub fn subctx_uncons(&self, ctx: CtxId, subctx: SubCtxId) -> Option<(SubCtxId, TermId)> {
        self.ctx[ctx.0].subctx_uncons(subctx)
    }

    /// Get the head of a subcontext
    pub fn subctx_head(&self, ctx: CtxId, subctx: SubCtxId) -> Option<TermId> {
        self.ctx[ctx.0].subctx_head(subctx)
    }

    /// Get the tail of a subcontext
    pub fn subctx_tail(&self, ctx: CtxId, subctx: SubCtxId) -> Option<SubCtxId> {
        self.ctx[ctx.0].subctx_tail(subctx)
    }

    /// Check whether a subcontext is valid
    pub fn is_valid_subctx(&self, ctx: CtxId, subctx: SubCtxId) -> bool {
        self.ctx[ctx.0].is_valid_subctx(subctx)
    }

    /// Check whether a subcontext is inhabited
    pub fn is_inhab_subctx(&self, ctx: CtxId, subctx: SubCtxId) -> bool {
        self.ctx[ctx.0].is_inhab_subctx(subctx)
    }

    /// Get a subcontext's sort
    pub fn subctx_sort(&self, ctx: CtxId, subctx: SubCtxId) -> Option<ULevel> {
        self.ctx[ctx.0].subctx_sort(subctx)
    }

    /// Get the empty subcontext
    pub fn nil_subctx(&mut self, ctx: CtxId) -> SubCtxId {
        let result = self.add(ctx, Node::NilCtx);
        debug_assert!(self.is_inhab(ctx, result));
        SubCtxId(result)
    }

    /// Append a type to a subcontext
    pub fn cons_subctx(&mut self, ctx: CtxId, subctx: SubCtxId, ty: TermId) -> SubCtxId {
        let len = self.ctx[ctx.0]
            .subctx_len(subctx)
            .expect("invalid subcontext");
        len.checked_add(1).expect("subcontext length overflow");
        let result = SubCtxId(self.add(ctx, Node::ConsCtx(len, [subctx.0, ty])));
        if let Some(subctx_sort) = self.subctx_sort(ctx, subctx) {
            if let Some(ty_sort) = self.sort(ctx, ty) {
                self.ctx[ctx.0].set_subctx_sort(result, subctx_sort.max(ty_sort));
                if self.is_inhab_subctx(ctx, subctx) && self.is_inhab(ctx, ty) {
                    self.ctx[ctx.0].set_inhab_subctx(result);
                }
            }
        }
        result
    }

    /// Get whether a context is a potential instance of a subcontext
    ///
    /// If it is, return its level
    pub fn is_subctx(
        &self,
        parent: CtxId,
        subctx: SubCtxId,
        child: CtxId,
    ) -> Result<ULevel, Error> {
        let Some(child_struct) = self.lookup(parent, Node::Struct(child)) else {
            return Err(Error::InvalidContext("Kernel::is_subctx (not a struct)"));
        };
        if self.eq_in(parent, child_struct, subctx.0) {
            debug_assert!(self.is_sealed(child));
            return Ok(self
                .sort(parent, child_struct)
                .expect("equated child struct must have a sort"));
        }
        Err(Error::InvalidSubctx(
            "Kernel::is_subctx (does not match context)",
        ))
    }

    /// Check whether a context is a _potential_ instance of a subcontext
    ///
    /// If it is, return its level
    ///
    /// # Examples
    /// ```
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let ctx = ker.new_ctx(None).unwrap();
    /// let nil = ker.nil_subctx(ctx);
    /// let child = ker.new_ctx(Some(ctx)).unwrap();
    /// assert_eq!(ker.compute_subctx_sort(ctx, nil, child), Ok(ULevel::PROP));
    /// let prop_ = ker.check_u(child, ULevel::PROP).unwrap();
    /// let prop = ker.check_u(ctx, ULevel::PROP).unwrap();
    /// assert_eq!(ker.add_param(child, prop_, false), Ok(0));
    /// assert!(ker.compute_subctx_sort(ctx, nil, child).is_err());
    /// let prop_ctx = ker.cons_subctx(ctx, nil, prop);
    /// assert!(ker.compute_subctx_sort(ctx, prop_ctx, child).is_err());
    /// assert_eq!(ker.closed(child, prop_, 0, 0, ctx), Ok(prop));
    /// assert_eq!(ker.compute_subctx_sort(ctx, prop_ctx, child), Ok(ULevel::SET));
    /// let bv0 = ker.add(ctx, Node::Bv(0));
    /// let true_ctx = ker.cons_subctx(ctx, prop_ctx, bv0);
    /// assert!(ker.compute_subctx_sort(ctx, true_ctx, child).is_err());
    /// let x = ker.check_param(child, child, 0, prop_).unwrap();
    /// assert_eq!(ker.add_param(child, x, true), Ok(1));
    /// assert!(ker.compute_subctx_sort(ctx, true_ctx, child).is_err());
    /// assert_eq!(ker.closed(child, x, 0, 1, ctx), Ok(bv0));
    /// assert_eq!(ker.compute_subctx_sort(ctx, true_ctx, child), Ok(ULevel::SET));
    /// ```
    pub fn compute_subctx_sort(
        &self,
        parent: CtxId,
        subctx: SubCtxId,
        child: CtxId,
    ) -> Result<ULevel, Error> {
        if let Ok(sort) = self.is_subctx(parent, subctx, child) {
            return Ok(sort);
        }
        let child_params = self.num_params(child);
        if child_params > u16::MAX as usize {
            return Err(Error::NotImplemented(
                "Kernel::is_subctx (child_params > u16::MAX)",
            ));
        }
        let child_params = child_params as u16;
        let subctx_params = self.subctx_len(parent, subctx).expect("invalid subcontext");
        if self.parent(child).is_some_and(|x| x != parent) {
            return Err(Error::NotImplemented("Kernel::check_struct (chain)"));
        }
        if child_params < subctx_params {
            return Err(Error::NotImplemented("Kernel::is_subctx (subchain)"));
        }
        if child_params > subctx_params {
            return Err(Error::ParamsMismatch(
                "Kernel::is_subctx (child_params > subctx_params)",
            ));
        }
        let mut ptr = subctx;
        for ix in (0..child_params).rev() {
            let Node::ConsCtx(len, [prev, ty]) = self.node(parent, ptr.0) else {
                return Err(Error::InvalidSubctx(
                    "Kernel::is_subctx (subctx of length > 0 not a cons)",
                ));
            };
            if len != ix {
                return Err(Error::InvalidSubctx(
                    "Kernel::is_subctx (invalid subctx binders)",
                ));
            }
            debug_assert_eq!(self.subctx_head(parent, ptr), Some(ty));
            debug_assert_eq!(self.subctx_tail(parent, ptr), Some(SubCtxId(prev)));
            let child_ty = self
                .param_ty(child, ix as u32)
                .expect("valid child parameter");
            self.check_eq_closed(parent, ty, child, child_ty, 0, ix)?;
            ptr = SubCtxId(prev);
        }
        let Node::NilCtx = self.node(parent, ptr.0) else {
            return Err(Error::InvalidSubctx(
                "Kernel::is_subctx (subctx of length 0 not a nil)",
            ));
        };
        Ok(self.ctx_sort(child))
    }

    /// Mark a context as being an instance of a subcontext
    ///
    /// Note that this _seals_ the context, disallowing any further parameters from being added!
    pub fn register_subctx(
        &mut self,
        parent: CtxId,
        subctx: SubCtxId,
        child: CtxId,
    ) -> Result<(), Error> {
        let sort = self.compute_subctx_sort(parent, subctx, child)?;
        self.seal(child);
        let child_struct = self.check_struct(parent, child)?;
        debug_assert_eq!(self.sort(parent, child_struct), Some(sort));
        self.ctx[parent.0].union(child_struct, subctx.0);
        debug_assert!(self.is_valid_subctx(parent, subctx));
        Err(Error::NotImplemented(
            "Kernel::register_subctx (not implemented)",
        ))
    }
}

/// # Helpers
///
/// Helper functions for implementing rules
impl Kernel {
    /// Check a term has a given type under a binder
    ///
    /// Corresponds to the rule
    /// ```text
    /// Γ, x : A ⊢ a : B
    /// Γ, x : A ⊢ B ≡ C
    /// ===
    /// Γ, x : A ⊢ a : C
    /// ```
    pub fn check_under_binder(
        &mut self,
        ctx: CtxId,
        _binder: TermId,
        term: TermId,
        ty: TermId,
    ) -> Result<(), Error> {
        if self.ctx[ctx.0].check_ty(term, ty) {
            return Ok(());
        }
        // TODO: use the binder for inter-context lore
        Err(Error::NotImplemented(
            "Kernel::check_under_binder (non-binder fallback)",
        ))
    }

    /// Get the sort of a term under a binder
    ///
    /// Returns `None` if this term is not a type under the binder
    pub fn sort_under_binder(
        &mut self,
        ctx: CtxId,
        _binder: TermId,
        term: TermId,
    ) -> Option<ULevel> {
        self.sort(ctx, term)
        //TODO: general case
    }

    /// Get whether a term is inhabited under a binder
    pub fn inhab_under_binder(&mut self, ctx: CtxId, _binder: TermId, term: TermId) -> bool {
        self.is_inhab(ctx, term)
        //TODO: general case
    }

    /// Get whether a term is empty under a binder
    pub fn empty_under_binder(&mut self, ctx: CtxId, _binder: TermId, term: TermId) -> bool {
        self.is_empty(ctx, term)
        //TODO: general case
    }

    /// Check whether `lhs ≡ [term/0]body` in the given context
    ///
    /// This function performs caching: calling it twice with the same inputs will be fast.
    pub fn check_eq_subst0_in(
        &mut self,
        ctx: CtxId,
        lhs: TermId,
        term: TermId,
        body: TermId,
    ) -> bool {
        if self.is_lc(ctx, body) {
            return self.eq_in(ctx, lhs, body);
        }
        todo!("Kernel::check_eq_subst0_in")
    }

    /// Insert the closure of `levels` under `binders`
    ///
    /// # Examples
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// # let mut ker = Kernel::default();
    /// # let src = ker.new_ctx(None).unwrap();
    /// # let dst = ker.new_ctx(None).unwrap();
    /// let cv1 = ker.add(src, Node::Cv(src, 1));
    /// let set = ker.add(src, Node::U(ULevel::SET));
    /// let pi_cv1 = ker.add(src, Node::Pi([set, cv1]));
    /// let set_ = ker.add(dst, Node::U(ULevel::SET));
    /// let bv2_ = ker.add(dst, Node::Bv(2));
    /// let pi_bv2_ = ker.add(dst, Node::Pi([set_, bv2_]));
    /// assert_eq!(
    ///     ker.closed(src, pi_cv1, 0, 3, dst),
    ///     Ok(pi_bv2_)
    /// );
    /// assert_eq!(
    ///     ker.check_eq_closed(dst, pi_bv2_, src, pi_cv1, 0, 3),
    ///     Ok(())
    /// );
    /// let bv3_ = ker.add(dst, Node::Bv(3));
    /// let pi_bv3_ = ker.add(dst, Node::Pi([set_, bv3_]));
    /// assert_eq!(
    ///     ker.closed(src, pi_cv1, 1, 3, dst),
    ///     Ok(pi_bv3_)
    /// );
    /// assert_eq!(
    ///     ker.check_eq_closed(dst, pi_bv3_, src, pi_cv1, 1, 3),
    ///     Ok(())
    /// );
    /// assert!(
    ///     ker.check_eq_closed(dst, pi_bv3_, src, pi_cv1, 0, 3).is_err()
    /// );
    /// ```
    pub fn closed(
        &mut self,
        src: CtxId,
        levels: TermId,
        binders: u16,
        params: u16,
        dst: CtxId,
    ) -> Result<TermId, Error> {
        let inserted = self.insert_closed(src, levels, binders, params, dst)?;
        let closure = self.add(
            dst,
            Node::Close(Close {
                binders,
                params,
                src,
                tm: levels,
            }),
        );
        self.ctx[dst.0].union(inserted, closure);
        debug_assert_eq!(self.bv(dst, inserted), self.bv(dst, closure));
        Ok(inserted)
    }

    /// Insert the closure of `levels` under `binders`
    ///
    /// Does not add any equalities
    pub fn insert_closed(
        &mut self,
        src: CtxId,
        levels: TermId,
        binders: u16,
        params: u16,
        dst: CtxId,
    ) -> Result<TermId, Error> {
        match self.node(src, levels) {
            Node::Bv(x) => {
                if x <= binders {
                    Ok(self.add(dst, Node::Bv(x)))
                } else {
                    let xb = x.checked_add(params).ok_or(Error::BoundsError(
                        "Kernel::insert_close (bound variable overflow)",
                    ))?;
                    Ok(self.add(dst, Node::Bv(xb)))
                }
            }
            Node::Cv(c, x) => {
                if c == src {
                    if x >= params as u32 {
                        Err(Error::InvalidParam(x))
                    } else {
                        let xb = binders.checked_add(params - x as u16 - 1).ok_or(
                            Error::BoundsError("Kernel::insert_close (closed variable overflow)"),
                        )?;
                        Ok(self.add(dst, Node::Bv(xb)))
                    }
                } else {
                    // TODO: look things up in the ancestor cache...
                    let mut ancestor = dst;
                    while ancestor != c {
                        ancestor = self.parent(ancestor).ok_or(Error::InvalidContext(
                            "Kernel::insert_close (ancestor not found)",
                        ))?;
                    }
                    Ok(self.add(dst, Node::Cv(c, x)))
                }
            }
            Node::Close(_) => Err(Error::NotImplemented("Kernel::insert_closed (close)")),
            node => {
                let result = node.with_binders().map_err(|(b, x)| {
                    let xb = binders.checked_add(b).ok_or(Error::BoundsError(
                        "Kernel::insert_close (internal binder overflow)",
                    ))?;
                    self.insert_closed(src, x, xb, params, dst)
                })?;
                Ok(self.add(dst, result))
            }
        }
    }

    /// Check whether the closure of `levels` is equal to `indices` under `binders`.
    pub fn check_eq_closed(
        &self,
        lhs: CtxId,
        indices: TermId,
        rhs: CtxId,
        levels: TermId,
        binders: u16,
        params: u16,
    ) -> Result<(), Error> {
        if !self.is_syntax(lhs, indices) {
            return Err(Error::ExpectedSyntax("Kernel::check_eq_closed (indices)"));
        }
        let closed = self
            .lookup(
                lhs,
                Node::Close(Close {
                    binders,
                    params,
                    src: rhs,
                    tm: levels,
                }),
            )
            .ok_or(Error::CacheMiss(
                "Kernel::check-eq_closed (closure of levels in lhs)",
            ))?;
        if self.eq_in(lhs, closed, indices) {
            debug_assert!(self.is_syntax(lhs, closed));
            Ok(())
        } else {
            Err(Error::TypeMismatch(
                "Kernel::check_eq_closed (not equal to closure)",
            ))
        }
    }
}

/// # Debugging utilities
///
/// Functions for inspecting the kernel's internal state, primarily useful for debugging
impl Kernel {
    /// Get the number of live contexts in this kernel
    ///
    /// # Example
    /// ```rust
    /// # use nucleus_kernel::kernel::*;
    /// let mut ker = Kernel::default();
    /// assert_eq!(ker.num_live_ctx(), 0);
    /// let ctx = ker.new_ctx(None).unwrap();
    /// assert_eq!(ker.num_live_ctx(), 1);
    /// ker.free_ctx(ctx);
    /// assert_eq!(ker.num_live_ctx(), 0);
    /// ```
    pub fn num_live_ctx(&self) -> usize {
        self.ctx.len()
    }

    /// Get the number of terms in a context
    pub fn num_terms(&self, ctx: CtxId) -> usize {
        self.ctx[ctx.0].num_terms()
    }
}

/// A handle for a context
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CtxId(SmallIndex<Ctx>);

/// A handle for a term
///
/// In a [`Kernel`], a term-in-context is identified by a ([`CtxId`], [`TermId`]) pair.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
pub struct TermId(Id);

impl Default for TermId {
    fn default() -> Self {
        TermId(Id::from(0x12345678))
    }
}

impl TermId {
    pub fn ix(&self) -> usize {
        self.0.into()
    }
}

/// A node in a term
pub type Node = crate::term::GNode<TermId>;

/// A kernel error
#[derive(Error, Debug, Eq, PartialEq)]
pub enum Error {
    /// Invalid parameter
    #[error("invalid parameter: {0}")]
    InvalidParam(u32),
    /// Erased parameter
    #[error("erased parameter: {0}")]
    ErasedParam(u32),
    /// Expected syntax
    #[error("expected syntax: {0}")]
    ExpectedSyntax(&'static str),
    /// Expected a type
    #[error("expected type: {0}")]
    ExpectedType(&'static str),
    /// Expected a proposition
    #[error("expected proposition: {0}")]
    ExpectedProp(&'static str),
    /// Expected an inhabited type
    #[error("expected inhabited type: {0}")]
    ExpectedInhab(&'static str),
    /// Expected a sort
    #[error("expected sort {0}")]
    ExpectedSort(&'static str),
    /// Type mismatch
    #[error("type mismatch: {0}")]
    TypeMismatch(&'static str),
    /// Invalid context
    #[error("invalid context: {0}")]
    InvalidContext(&'static str),
    /// Inference failure
    #[error("inference failure: {0}")]
    InferenceFailure(&'static str),
    /// Invalid subcontext
    #[error("invalid subcontext: {0}")]
    InvalidSubctx(&'static str),
    /// Parameter count mismatch
    #[error("parameter count mismatch: {0}")]
    ParamsMismatch(&'static str),
    /// Bounds error
    #[error("bounds error: {0}")]
    BoundsError(&'static str),
    /// Cache miss
    #[error("cache miss: {0}")]
    CacheMiss(&'static str),
    /// Not implemented
    #[error("not implemented: {0}")]
    NotImplemented(&'static str),
}
