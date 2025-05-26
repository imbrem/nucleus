pub mod kernel;
pub mod term;

pub use kernel::*;

impl Kernel {
    /// Construct a new child subcontext with a given parameter
    ///
    /// Note the parameter is here with respect to the _parent_ context (since, of course, the child
    /// context does not yet exist!)
    ///
    /// The resulting parameter always has index 0
    pub fn with_param(
        &mut self,
        parent: CtxId,
        param: TermId,
        erased: bool,
    ) -> Result<CtxId, Error> {
        Err(Error::NotImplemented("Kernel::with_param"))
    }

    /// Create a subcontext from an iterator of parameters
    pub fn subctx_from_iter(
        &mut self,
        ctx: CtxId,
        iter: impl IntoIterator<Item = TermId>,
    ) -> SubCtxId {
        let mut result = self.nil_subctx(ctx);
        for param in iter {
            result = self.cons_subctx(ctx, result, param);
        }
        result
    }

    /// Register a subcontext with a single parameter
    pub fn one_subctx(&mut self, ctx: CtxId, param: TermId) -> SubCtxId {
        self.subctx_from_iter(ctx, [param])
    }
}
