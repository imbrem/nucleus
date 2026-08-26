//! Language-independent userspace interfaces for coproduct construction.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_hol::{Kernel, KernelError, Ref, Sort, Tag, TyTag};

use crate::{ModelError, substitute};

/// Failure to specialize or derive a userspace coproduct package.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CoproductError {
    /// Checked type substitution rejected the open schema.
    #[snafu(display("could not specialize coproduct schema: {source}"))]
    Substitution {
        /// Underlying userspace substitution failure.
        source: ModelError,
    },
    /// A checked kernel query rejected one of the specialized rows.
    #[snafu(display("could not inspect specialized coproduct schema: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The supplied schema did not specialize to a Boolean term.
    #[snafu(display("coproduct schema did not specialize to a Boolean term"))]
    NotBoolean,
}

/// An open universal-property predicate for coproducts.
///
/// This descriptor groups three free type variables with the checked Boolean
/// term that mentions them. A source compiler may populate it, but neither the
/// descriptor nor future derivations depend on a particular surface language.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductSchema {
    /// Open left summand type variable.
    pub left: Ref,
    /// Open right summand type variable.
    pub right: Ref,
    /// Open candidate coproduct type variable.
    pub coproduct: Ref,
    /// `IsCoprod left right coproduct`, encoded as an open Boolean term.
    pub predicate: Ref,
}

impl CoproductSchema {
    /// Iterates the schema's complete checked syntax interface.
    #[must_use]
    pub fn references(&self) -> impl ExactSizeIterator<Item = Ref> {
        [self.left, self.right, self.coproduct, self.predicate].into_iter()
    }

    /// Remaps every checked reference while preserving the schema roles.
    ///
    /// # Errors
    ///
    /// Returns the first error produced by `map`.
    pub fn try_map<E>(self, mut map: impl FnMut(Ref) -> Result<Ref, E>) -> Result<Self, E> {
        Ok(Self {
            left: map(self.left)?,
            right: map(self.right)?,
            coproduct: map(self.coproduct)?,
            predicate: map(self.predicate)?,
        })
    }

    /// Specializes the three open type variables to checked resident types.
    ///
    /// The operation is transactional: a rejected schema or type leaves
    /// `kernel` unchanged. The returned term is checked Boolean syntax, but no
    /// theorem asserting it is introduced.
    ///
    /// # Errors
    ///
    /// Returns an error if any checked substitution fails, a resulting row is
    /// malformed, or the fully specialized expression is not Boolean.
    pub fn specialize(
        self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
        coproduct: Ref,
    ) -> Result<Ref, CoproductError> {
        let mut staged = kernel.fork();
        let predicate = substitute(&mut staged, self.left, left, self.predicate)
            .context(SubstitutionSnafu)?
            .output;
        let predicate = substitute(&mut staged, self.right, right, predicate)
            .context(SubstitutionSnafu)?
            .output;
        let predicate = substitute(&mut staged, self.coproduct, coproduct, predicate)
            .context(SubstitutionSnafu)?
            .output;
        let classifier = staged.classifier(predicate).context(KernelSnafu)?;
        if staged.category(predicate).context(KernelSnafu)? != Sort::Tm
            || staged.arena().tag(classifier) != Some(Tag::Ty(TyTag::Bool))
        {
            return Err(CoproductError::NotBoolean);
        }
        *kernel = staged;
        Ok(predicate)
    }
}
