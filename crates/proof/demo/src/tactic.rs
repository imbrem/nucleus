//! Tiny userspace tactic linked into the proof component.

use super::bindings::nucleus::proof::{
    host::Kernel,
    tactics::{RewriteDirection, RewriteResult, rewrite_proposition},
};

pub(crate) fn rewrite(
    kernel: &Kernel,
    bool_type: u64,
    equality_theorem: u64,
    premise_theorem: u64,
) -> Result<RewriteResult, String> {
    rewrite_proposition(
        kernel,
        bool_type,
        equality_theorem,
        premise_theorem,
        RewriteDirection::Forward,
    )
}
