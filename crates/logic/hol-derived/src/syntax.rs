//! Userspace certificates for structurally identical checked syntax.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, SynRel, Tag, TmTag, TyTag};

/// Failure to certify two checked rows as structurally identical.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SyntaxError {
    /// A checked syntactic rule rejected the derived certificate.
    #[snafu(display("syntax certification was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The two checked trees differ structurally.
    #[snafu(display("checked syntax is not structurally identical"))]
    Different,
}

impl From<KernelError> for SyntaxError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

/// Certifies and joins two structurally identical checked syntax trees.
///
/// This is untrusted traversal: every congruence edge is checked by the
/// kernel, and a mismatch simply returns an error.
///
/// # Errors
///
/// Returns an error if either tree is absent, their syntax differs, or a
/// checked reflexivity, congruence, binder, or union operation rejects the
/// derived evidence.
pub fn join_same_syntax(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
) -> Result<SynFactId, SyntaxError> {
    fn derive(
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
        memo: &mut BTreeMap<(Ref, Ref), SynFactId>,
    ) -> Result<SynFactId, SyntaxError> {
        if let Some(fact) = memo.get(&(left, right)) {
            return Ok(*fact);
        }
        if left == right {
            let fact = kernel.syn_refl(None, SynRel::Syn, left)?;
            memo.insert((left, right), fact);
            return Ok(fact);
        }
        let tag = kernel.arena().tag(left);
        if tag.is_none()
            || tag != kernel.arena().tag(right)
            || kernel.arena().name(left) != kernel.arena().name(right)
            || kernel.arena().bool_value(left) != kernel.arena().bool_value(right)
            || kernel.arena().op1(left) != kernel.arena().op1(right)
            || kernel.arena().op2(left) != kernel.arena().op2(right)
        {
            return Err(SyntaxError::Different);
        }
        let left_children = kernel
            .arena()
            .children(left)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        let right_children = kernel
            .arena()
            .children(right)
            .ok_or(SyntaxError::Different)?
            .collect::<Vec<_>>();
        if left_children.len() != right_children.len() {
            return Err(SyntaxError::Different);
        }
        let facts = left_children
            .iter()
            .zip(&right_children)
            .map(|(&left, &right)| derive(kernel, left, right, memo))
            .collect::<Result<Vec<_>, _>>()?;
        let fact = match tag {
            Some(Tag::Tm(TmTag::Lam) | Tag::Ty(TyTag::Lam)) if facts.len() == 2 => kernel
                .syn_binder_congr(
                    None,
                    SynRel::Syn,
                    None,
                    None,
                    left,
                    right,
                    facts[0],
                    facts[1],
                ),
            _ => kernel.syn_congr(None, SynRel::Syn, None, None, left, right, &facts),
        }?;
        memo.insert((left, right), fact);
        Ok(fact)
    }

    let fact = derive(kernel, left, right, &mut BTreeMap::new())?;
    kernel.union_syn_fact(fact)?;
    Ok(fact)
}
