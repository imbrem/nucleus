use std::{
    cmp::Ordering,
    collections::HashMap,
    hash::{Hash, Hasher},
};

use covalence_lib_error::snafu::Snafu;

use super::{Formula, FormulaPath, Ref, Sequent, Side, Word, WordError};

const PAYLOAD_WIDTH: u32 = 31;
const RESERVED_WORDS: usize = 4;
const CLASS_MASK: u32 = 0x1f;
const MAX_SIZE_CLASS: usize = 29;
const REFCOUNT_MAX: u32 = (1 << 25) - 1;

/// A failure to build or mutate checked classical syntax.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RuntimeError {
    /// Raw storage did not satisfy the complete allocator and ownership check.
    #[snafu(display("invalid tagged runtime arena"))]
    InvalidArena,
    /// An abstract formula or allocation exceeded the fixed runtime bounds.
    #[snafu(display("tagged runtime resource bound exceeded: {reason}"))]
    ResourceBound {
        /// The bound that could not be satisfied.
        reason: &'static str,
    },
    /// A formula could not be represented as a packed word.
    #[snafu(transparent)]
    Word {
        /// Underlying fixed-word construction failure.
        source: WordError,
    },
    /// The semantic builder produced storage that failed its internal check.
    #[snafu(display("tagged runtime builder failed its internal check"))]
    PackerPostcheck,
    /// A shared block's reference count cannot be incremented.
    #[snafu(display("tagged runtime reference count overflow"))]
    RefcountOverflow,
    /// A mutation selected an absent table member or child.
    #[snafu(display("tagged runtime index is out of bounds"))]
    Index,
    /// A mutation selected a node with the wrong constructor or polarity.
    #[snafu(display("tagged runtime node has the wrong shape"))]
    Shape,
}

mod arena;
mod checked;
mod cow;
mod decode;
mod mutation;
mod pack;
mod types;
mod views;

pub(crate) use arena::Arena;
pub(crate) use pack::pack;
pub use views::{Checked, FormulaKind, FormulaView, SequentView};

use decode::Expand;
use pack::least_size_class;
use types::{Block, Coverage, Frame, Header, NullablePointer, Token, node};

#[cfg(test)]
mod allocator_tests;
