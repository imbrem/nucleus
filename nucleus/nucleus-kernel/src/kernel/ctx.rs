use ref_cast::RefCast;

use bitflags::bitflags;
use egg::{Analysis, DidMerge, EGraph, Language};

use super::*;

#[derive(Default, Clone, RefCast)]
#[repr(transparent)]
pub(super) struct Ctx {
    e: EGraph<Node, CtxInner>,
}

impl Ctx {
    /// Construct a new context with the given parent
    pub fn new(parent: Option<CtxId>) -> Self {
        let inner = CtxInner {
            flags: CtxFlags::default(),
            parent,
            params: Vec::new(),
            term_data: Vec::new(),
            sort: ULevel::PROP,
            pending: Vec::new(),
        };
        // TODO: optimize, using custom congruence closure or somesuch?
        let mut e = EGraph::new(inner).with_explanations_enabled();
        e.rebuild();
        Self { e }
    }

    /// Get this context's parent
    pub fn parent(&self) -> Option<CtxId> {
        self.e.analysis.parent
    }

    /// Get this context's sort
    pub fn ctx_sort(&self) -> ULevel {
        self.e.analysis.sort
    }

    /// Get a parameter's type
    pub fn param_ty(&self, ix: u32) -> Option<TermId> {
        self.e
            .analysis
            .params
            .get(ix as usize)
            .map(|param| param.ty)
    }

    /// Get whether a parameter is erased
    pub fn param_erased(&self, ix: u32) -> Option<bool> {
        self.e
            .analysis
            .params
            .get(ix as usize)
            .map(|param| param.erased)
    }

    /// Check whether a context is clean
    pub fn is_clean(&self) -> bool {
        self.e.clean
    }

    /// Check whether a context is sealed
    pub fn is_sealed(&self) -> bool {
        self.e.analysis.flags.contains(CtxFlags::SEALED)
    }

    /// Seal a context
    ///
    /// Returns if the context was already sealed
    pub fn seal(&mut self) {
        self.e.analysis.flags.set(CtxFlags::SEALED, true);
    }

    /// Add a parameter to this context
    pub fn add_param(&mut self, param: TermId, erased: bool) -> Result<u32, Error> {
        if self.is_sealed() {
            return Err(Error::InvalidContext("Ctx::add_param (context sealed)"));
        }
        let Some(sort) = self.sort(param) else {
            return Err(Error::ExpectedType("Ctx::add_param (invalid sort)"));
        };
        let ix = self.e.analysis.params.len();
        if ix > u32::MAX as usize {
            return Err(Error::InvalidContext("Ctx::add_param (too many params)"));
        }
        self.e.analysis.params.push(Param { ty: param, erased });
        self.e.analysis.sort = self.e.analysis.sort.max(sort);
        Ok(ix as u32)
    }

    /// Get the number of terms in this context
    pub fn num_terms(&self) -> usize {
        self.e.analysis.term_data.len()
    }

    /// Rebuild a context
    pub fn rebuild(&mut self) -> usize {
        self.e.rebuild()
    }

    /// Check whether a term is valid syntax
    pub fn is_syntax(&self, id: TermId) -> bool {
        self.e.analysis.term_data[id.ix()]
            .flags
            .contains(TermFlags::IS_SYNTAX)
    }

    /// Get the upper bound for this term's bound variables
    pub fn bv(&self, tm: TermId) -> u16 {
        self.e[tm.0].data.bv
    }

    /// Get whether a term is locally closed
    pub fn is_lc(&self, tm: TermId) -> bool {
        self.bv(tm) == 0
    }

    /// Get the upper bound for this node's bound variables
    pub fn node_bv(&self, node: Node) -> u16 {
        match node {
            Node::Bv(x) => x + 1,
            Node::Close(_) => u16::MAX,
            node => node
                .children()
                .iter()
                .zip(node.binders())
                .map(|(x, b)| self.bv(*x).saturating_sub(b))
                .max()
                .unwrap_or(0),
        }
    }

    /// Add a term to the context
    fn add_helper(&mut self, node: Node, class: bool) -> TermId {
        let id = if class {
            self.e.add(node)
        } else {
            self.e.add_uncanonical(node)
        };
        let result = TermId(id);
        let ix: usize = id.into();
        while ix >= self.e.analysis.term_data.len() {
            self.e.analysis.term_data.push(TermData::default());
        }
        if !class
            && node.is_syntax()
            && !self.is_syntax(result)
            && node.children().iter().all(|x| self.is_syntax(*x))
        {
            self.e.analysis.term_data[ix]
                .flags
                .set(TermFlags::IS_SYNTAX, true);
        }
        result
    }

    /// Insert a node into a context
    pub fn add(&mut self, node: Node) -> TermId {
        self.add_helper(node, false)
    }

    /// Get the equivalence class of a ndoe
    pub fn repr(&mut self, node: Node) -> TermId {
        self.add_helper(node, true)
    }

    /// Get the node corresponding to a term
    pub fn node(&self, id: TermId) -> Node {
        *self.e.id_to_node(id.0)
    }

    /// Try to lookup a node in this context
    pub fn lookup(&self, node: Node) -> Option<TermId> {
        self.e.lookup(node).map(TermId)
    }

    /// Find the current representative of a term
    pub fn find(&self, id: TermId) -> TermId {
        TermId(self.e.find(id.0))
    }

    /// Check whether two terms are equal in this context
    pub fn eq(&self, lhs: TermId, rhs: TermId) -> bool {
        self.find(lhs) == self.find(rhs)
    }

    /// Check whether a term is well-formed
    pub fn is_tm(&self, tm: TermId) -> bool {
        self.e[tm.0].data.flags.contains(ClassFlags::IS_TM)
    }

    /// Check whether a term is a proposition
    pub fn is_prop(&self, tm: TermId) -> bool {
        let result = self.e[tm.0].data.flags.contains(ClassFlags::IS_PROP);
        debug_assert!(!result || self.ty(tm).is_none_or(|ty| self.as_prop_sort(ty).is_some()));
        result
    }

    /// Check whether a term is a proof of a proposition
    pub fn is_proof(&self, tm: TermId) -> bool {
        self.ty(tm).is_some_and(|tm| self.is_prop(tm))
    }

    /// Check whether a term is a type
    pub fn is_ty(&self, tm: TermId) -> bool {
        self.e[tm.0].data.is_ty()
    }

    /// Check whether a term is a sort
    pub fn is_sort(&self, tm: TermId) -> bool {
        self.e[tm.0].data.is_sort()
    }

    /// Check whether a term is an inhabited type
    pub fn is_inhab(&self, tm: TermId) -> bool {
        self.e[tm.0].data.is_inhab()
    }

    /// Check whether a term is an empty type
    pub fn is_empty(&self, tm: TermId) -> bool {
        self.e[tm.0].data.is_empty()
    }

    /// Check whether a term is equal to the type of propositions
    pub fn as_prop_sort(&self, tm: TermId) -> Option<TermId> {
        let p = self.lookup(Node::U(ULevel::PROP))?;
        if self.find(tm) == p { Some(p) } else { None }
    }

    /// Check whether a term is equal to the sort of propositions
    pub fn is_prop_sort(&self, tm: TermId) -> bool {
        self.as_prop_sort(tm).is_some()
    }

    /// Get this term as a sort
    ///
    /// Returns `None` if this term is not a sort
    pub fn as_sort(&self, tm: TermId) -> Option<ULevel> {
        let eclass = &self.e[tm.0].nodes;
        debug_assert!(eclass.windows(2).all(|w| w[0] < w[1]));
        let ix = eclass
            .binary_search(&Node::U(ULevel::PROP))
            .unwrap_or_else(|x| x);
        match eclass.get(ix) {
            Some(Node::U(l)) => Some(*l),
            _ => None,
        }
    }

    /// Get this term's sort
    ///
    /// Returns `None` if this term is not a type
    pub fn sort(&self, tm: TermId) -> Option<ULevel> {
        let result = if let Some(ty) = self.ty(tm) {
            self.as_sort(ty)
        } else {
            self.as_sort(tm).map(|l| l.succ())
        };
        debug_assert!(result.is_none() || self.is_ty(tm));
        result
    }

    /// Get a term's type, if any
    pub fn ty(&self, tm: TermId) -> Option<TermId> {
        self.e[tm.0].data.ty()
    }

    /// Check a term has the given type
    pub fn check_ty(&self, tm: TermId, ty: TermId) -> bool {
        if let Some(term_ty) = self.ty(tm) {
            self.eq(term_ty, ty)
        } else {
            false
        }
    }

    /// Union two terms, returning if anything has changed
    pub fn union(&mut self, lhs: TermId, rhs: TermId) -> bool {
        self.e.union(lhs.0, rhs.0)
    }

    /// Update the analysis data for a term
    pub fn update_analysis(&mut self, tm: TermId) {
        self.e.set_analysis_data(tm.0, self.e[tm.0].data);
    }

    /// Set a type as inhabited
    pub fn set_inhab(&mut self, ty: TermId) {
        if self.e[ty.0].data.set_inhab() {
            self.update_analysis(ty);
        }
    }

    /// Set a type as empty
    pub fn set_empty(&mut self, ty: TermId) {
        if self.e[ty.0].data.set_empty() {
            self.update_analysis(ty);
        }
    }

    /// Set a term's type, returning if anything has changed
    pub fn set_ty(&mut self, tm: TermId, ty: TermId) -> bool {
        debug_assert!(self.is_ty(ty));
        let (changed, mut analysis) = if let Some(term_ty) = self.ty(tm) {
            (self.union(term_ty, ty), false)
        } else {
            self.set_inhab(ty);
            self.e[tm.0].data.set_ty(ty);
            (true, true)
        };
        if self.is_sort(ty) {
            analysis |= self.e[tm.0].data.set_is_ty();
        }
        if self.is_prop_sort(ty) {
            analysis |= self.e[tm.0].data.set_is_prop();
        }
        if analysis {
            self.update_analysis(tm);
        }
        changed || analysis
    }

    /// Get the current number of parameters of this context
    pub fn num_params(&self) -> usize {
        self.e.analysis.params.len()
    }

    /// Get this subcontext's length, if any
    pub fn subctx_len(&self, ctx: SubCtxId) -> Option<u16> {
        match self.node(ctx.0) {
            Node::ConsCtx(l, _) => l.checked_add(1),
            Node::NilCtx => Some(0),
            _ => None,
        }
    }

    /// Destruct a subcontext
    pub fn subctx_uncons(&self, ctx: SubCtxId) -> Option<(SubCtxId, TermId)> {
        match self.node(ctx.0) {
            Node::ConsCtx(_, [x, y]) => Some((SubCtxId(x), y)),
            _ => None,
        }
    }

    /// Get this subcontext's head, if any
    pub fn subctx_head(&self, ctx: SubCtxId) -> Option<TermId> {
        match self.node(ctx.0) {
            Node::ConsCtx(_, [_, x]) => Some(x),
            _ => None,
        }
    }

    /// Get this subcontext's tail, if any
    pub fn subctx_tail(&self, ctx: SubCtxId) -> Option<SubCtxId> {
        match self.node(ctx.0) {
            Node::ConsCtx(_, [x, _]) => Some(SubCtxId(x)),
            _ => None,
        }
    }

    /// Get this subcontext's sort, if any
    pub fn subctx_sort(&self, ctx: SubCtxId) -> Option<ULevel> {
        match self.node(ctx.0) {
            Node::ConsCtx(_, _) => self.sort(ctx.0),
            Node::NilCtx => Some(ULevel::PROP),
            _ => None,
        }
    }

    /// Get whether a subcontext is valid
    pub fn is_valid_subctx(&self, ctx: SubCtxId) -> bool {
        self.is_ty(ctx.0) && self.subctx_len(ctx).is_some()
    }

    /// Get whether a subcontext is inhabited
    pub fn is_inhab_subctx(&self, ctx: SubCtxId) -> bool {
        self.is_inhab(ctx.0) && self.subctx_len(ctx).is_some()
    }

    /// Set a subcontext's sort
    ///
    /// Returns whether any change was made
    pub fn set_subctx_sort(&mut self, ctx: SubCtxId, sort: ULevel) -> bool {
        let ty = self.add(Node::U(sort));
        self.set_ty(ctx.0, ty)
    }

    /// Set a subcontext as inhabited
    pub fn set_inhab_subctx(&mut self, ctx: SubCtxId) {
        self.set_inhab(ctx.0);
    }
}

#[derive(Default, Clone)]
pub(super) struct CtxInner {
    /// This context's flags
    flags: CtxFlags,
    /// This context's parent
    parent: Option<CtxId>,
    /// This context's parameter types
    params: Vec<Param>,
    /// The data for each term in this context
    term_data: Vec<TermData>,
    /// This context's sort
    sort: ULevel,
    /// Pending merges
    pending: Vec<(TermId, TermId)>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
struct TermData {
    /// This term's flags
    flags: TermFlags,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub(super) struct ClassData {
    /// This class's type, if any
    ty: TermId,
    /// This class's flags
    flags: ClassFlags,
    /// The upper bound (exclusive) for bound variables in this class
    bv: u16,
}

impl ClassData {
    pub fn set_ty(&mut self, ty: TermId) {
        self.flags.set(ClassFlags::IS_TM, true);
        self.flags.set(ClassFlags::HAS_TY, true);
        self.ty = ty;
    }

    pub fn set_is_ty(&mut self) -> bool {
        debug_assert!(self.is_tm());
        if self.flags.contains(ClassFlags::IS_TY) {
            return false;
        }
        self.flags.set(ClassFlags::IS_TY, true);
        true
    }

    pub fn set_is_prop(&mut self) -> bool {
        debug_assert!(self.is_ty());
        if self.flags.contains(ClassFlags::IS_PROP) {
            return false;
        }
        self.flags.set(ClassFlags::IS_PROP, true);
        true
    }

    pub fn set_inhab(&mut self) -> bool {
        debug_assert!(self.is_ty());
        if self.flags.contains(ClassFlags::IS_INHAB) {
            return false;
        }
        self.flags.set(ClassFlags::IS_INHAB, true);
        true
    }

    pub fn set_empty(&mut self) -> bool {
        debug_assert!(self.is_ty());
        if self.flags.contains(ClassFlags::IS_EMPTY) {
            return false;
        }
        self.flags.set(ClassFlags::IS_EMPTY, true);
        true
    }

    pub fn is_tm(&self) -> bool {
        self.flags.contains(ClassFlags::IS_TM)
    }

    pub fn is_ty(&self) -> bool {
        if self.flags.contains(ClassFlags::IS_TY) {
            debug_assert!(self.is_tm());
            true
        } else {
            false
        }
    }

    pub fn is_inhab(&self) -> bool {
        if self.flags.contains(ClassFlags::IS_INHAB) {
            debug_assert!(self.is_ty());
            true
        } else {
            false
        }
    }

    pub fn is_empty(&self) -> bool {
        if self.flags.contains(ClassFlags::IS_EMPTY) {
            debug_assert!(self.is_ty());
            true
        } else {
            false
        }
    }

    pub fn is_sort(&self) -> bool {
        if self.flags.contains(ClassFlags::IS_SORT) {
            debug_assert!(self.is_ty());
            true
        } else {
            false
        }
    }

    pub fn ty(&self) -> Option<TermId> {
        if self.flags.contains(ClassFlags::HAS_TY) {
            debug_assert!(self.is_tm());
            Some(self.ty)
        } else {
            None
        }
    }
}

bitflags! {
    /// Flags for a context
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
    struct CtxFlags: u8 {
        /// Whether this context is sealed, i.e. allows adding no more parameters
        const SEALED = 1 << 0;
    }

    /// Flags for a subcontext
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
    struct SubCtxFlags: u8 {
        /// Whether this subcontext is well-formed
        const IS_WF = 1 << 0;
    }

    /// Flags for a term
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
    struct TermFlags : u8 {
        /// Whether this term has a unique definition
        const IS_SYNTAX = 1 << 1;
        /// Whether this term has been evaluated
        const IS_EVAL = 1 << 2;
    }

    /// Flags for an equivalence class of terms
    #[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
    struct ClassFlags : u8 {
        /// Whether this class is a well-formed termn
        const IS_TM = 1 << 0;
        /// Whether this class has a type
        const HAS_TY = 1 << 1;
        /// Whether this class is a type
        const IS_TY = 1 << 2;
        /// Whether this class is a proposition
        const IS_PROP = 1 << 3;
        /// Whether this class is a sort
        const IS_SORT = 1 << 4;
        /// Whether this class is inhabited
        const IS_INHAB = 1 << 5;
        /// Whether this class is empty
        const IS_EMPTY = 1 << 6;
    }
}

impl Node {
    fn flags(&self) -> ClassFlags {
        match self {
            Node::U(_) => {
                ClassFlags::IS_SORT | ClassFlags::IS_TY | ClassFlags::IS_TM | ClassFlags::IS_INHAB
            }
            // NOTE: booleans are types since they are propositions
            Node::Bool(true) => {
                ClassFlags::IS_TY | ClassFlags::IS_TM | ClassFlags::IS_INHAB | ClassFlags::IS_PROP
            }
            Node::Bool(false) => {
                ClassFlags::IS_TY | ClassFlags::IS_TM | ClassFlags::IS_EMPTY | ClassFlags::IS_PROP
            }
            Node::NilCtx | Node::Nat | Node::Int => {
                ClassFlags::IS_TY | ClassFlags::IS_TM | ClassFlags::IS_INHAB
            }
            Node::SmallNat(_) | Node::SmallInt(_) => ClassFlags::IS_TM | ClassFlags::IS_INHAB,
            _ => ClassFlags::default(),
        }
    }

    fn is_syntax(&self) -> bool {
        match self {
            Node::Close(_) => false,
            _ => true,
        }
    }
}

impl Analysis<Node> for CtxInner {
    type Data = ClassData;

    fn make(egraph: &mut EGraph<Node, Self>, enode: &Node) -> Self::Data {
        let ctx: &mut Ctx = RefCast::ref_cast_mut(egraph);
        ClassData {
            ty: TermId::default(),
            flags: enode.flags(),
            bv: ctx.node_bv(*enode),
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let (ty, mut a_changed, mut b_changed) = match (a.ty(), b.ty()) {
            (Some(a_ty), Some(b_ty)) => {
                if a_ty != b_ty {
                    self.pending.push((a_ty, b_ty));
                }
                (a_ty, false, false)
            }
            (Some(a_ty), None) => (a_ty, false, true),
            (None, Some(b_ty)) => (b_ty, true, false),
            (None, None) => (TermId::default(), false, false),
        };
        let flags = a.flags | b.flags;
        a_changed |= flags != a.flags;
        b_changed |= flags != b.flags;
        let bv = a.bv.min(b.bv);
        a_changed |= bv != a.bv;
        b_changed |= bv != b.bv;
        a.ty = ty;
        a.flags = flags;
        a.bv = bv;
        DidMerge(a_changed, b_changed)
    }
}

impl Language for Node {
    type Discriminant = std::mem::Discriminant<Node>;

    fn discriminant(&self) -> Self::Discriminant {
        std::mem::discriminant(self)
    }

    fn matches(&self, other: &Self) -> bool {
        match (self, other) {
            (Node::Cv(c, x), Node::Cv(c_, y)) => c == c_ && x == y,
            (Node::Bv(x), Node::Bv(y)) => x == y,
            (Node::U(x), Node::U(y)) => x == y,
            (Node::Pi(_), Node::Pi(_)) => true,
            (Node::Abs(_), Node::Abs(_)) => true,
            (Node::App(_), Node::App(_)) => true,
            (Node::Let(_), Node::Let(_)) => true,
            (Node::Is(_), Node::Is(_)) => true,
            (Node::Annot(_), Node::Annot(_)) => true,
            (Node::Bool(x), Node::Bool(y)) => x == y,
            (Node::Dite(_), Node::Dite(_)) => true,
            (Node::Trunc(_), Node::Trunc(_)) => true,
            (Node::Epsilon(_), Node::Epsilon(_)) => true,
            (Node::Nat, Node::Nat) => true,
            (Node::SmallNat(x), Node::SmallNat(y)) => x == y,
            (Node::Int, Node::Int) => true,
            (Node::SmallInt(x), Node::SmallInt(y)) => x == y,
            (Node::Struct(x), Node::Struct(y)) => x == y,
            (Node::Mk(x), Node::Mk(y)) => x == y,
            (Node::Proj(x, y), Node::Proj(z, w)) => x == z && y == w,
            (Node::Close(c), Node::Close(c_)) => c == c_,
            (Node::NilCtx, Node::NilCtx) => true,
            (Node::ConsCtx(x, _), Node::ConsCtx(y, _)) => x == y,
            _ => false,
        }
    }

    fn children(&self) -> &[Id] {
        let children = self.children();
        unsafe { std::slice::from_raw_parts(children.as_ptr() as *const _, children.len()) }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        let children = self.children_mut();
        unsafe { std::slice::from_raw_parts_mut(children.as_mut_ptr() as *mut _, children.len()) }
    }
}
