//! Immutable JSON values for Covalence.
//!
//! [`Json<I>`] is a JSON tree parametrized over an [`Index`] family `I`, which
//! chooses the indirection every nested slot goes through:
//!
//! - [`Shared`] (`Arc`, the default) — the shared immutable view: O(1) clone,
//!   structural sharing, subtree extraction without copying, `Send + Sync`;
//! - [`Local`] (`Rc`) — the same shape without atomics;
//! - [`Refs<'a>`] — a borrowed view over storage that outlives it, such as an
//!   arena.
//!
//! Strictness is carried by construction rather than checked on use. An
//! object is a [`Map`]: entries sorted strictly by key, so duplicate keys are
//! unrepresentable and compact serialization is already in sorted-key,
//! whitespace-free "almost canonical" form. Numbers are `serde_json`'s, which
//! cannot be non-finite. Parsing rejects what the invariants cannot hold —
//! a duplicate key is an error, not a last-wins overwrite.
//!
//! There is deliberately no mutation: a changed tree is a new tree sharing
//! the unchanged subtrees. Sharing pays off in comparison too — equality and
//! the total order both begin with a pointer check, so a value never descends
//! into a subtree it shares with the other side. Numbers stay in
//! `serde_json`'s representation, where `1` and `1.0` are distinct values,
//! exactly as they are distinct JSON texts.
//!
//! This is the value type behind the Python bindings' `covalence.data.json`
//! and a candidate carrier for HOL-JSON work, where validate-once and
//! hash-stable bytes matter more than in-place update.

mod index;
mod map;
mod order;
mod wire;

use std::fmt;
use std::hash::{Hash, Hasher};

pub use covalence_lib_json::Number;

pub use crate::index::{Build, Index, Local, Refs, Shared};
pub use crate::map::{Entry, Map, MapError};
pub use crate::wire::{ParseError, from_slice, from_str};

/// A JSON value, threaded through the indirection family `I`.
///
/// The default family is [`Shared`], the `Arc`-backed immutable view.
pub enum Json<I: Index = Shared> {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// A finite number.
    Number(Number),
    /// A string.
    String(I::Str),
    /// An array.
    Array(I::Array),
    /// An object; see [`Map`] for the invariant.
    Object(Map<I>),
}

impl<I: Index> Json<I> {
    /// Whether this is `null`.
    #[must_use]
    pub fn is_null(&self) -> bool {
        matches!(self, Json::Null)
    }

    /// The boolean, if this is one.
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(value) => Some(*value),
            _ => None,
        }
    }

    /// The number, if this is one.
    #[must_use]
    pub fn as_number(&self) -> Option<&Number> {
        match self {
            Json::Number(value) => Some(value),
            _ => None,
        }
    }

    /// The string contents, if this is a string.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::String(value) => Some(value),
            _ => None,
        }
    }

    /// The elements, if this is an array.
    #[must_use]
    pub fn as_array(&self) -> Option<&[Json<I>]> {
        match self {
            Json::Array(values) => Some(values),
            _ => None,
        }
    }

    /// The map, if this is an object.
    #[must_use]
    pub fn as_object(&self) -> Option<&Map<I>> {
        match self {
            Json::Object(map) => Some(map),
            _ => None,
        }
    }

    /// The value under `key`, if this is an object that has it.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&Json<I>> {
        self.as_object().and_then(|map| map.get(key))
    }

    /// The element at `index`, if this is an array that long.
    #[must_use]
    pub fn get_index(&self, index: usize) -> Option<&Json<I>> {
        self.as_array().and_then(|values| values.get(index))
    }

    /// A name for the variant: `"null"`, `"bool"`, `"number"`, `"string"`,
    /// `"array"`, or `"object"`.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Json::Null => "null",
            Json::Bool(_) => "bool",
            Json::Number(_) => "number",
            Json::String(_) => "string",
            Json::Array(_) => "array",
            Json::Object(_) => "object",
        }
    }
}

impl<I: Build> Json<I> {
    /// A string value, copying `value` into the family's storage.
    #[must_use]
    pub fn string(value: &str) -> Self {
        Json::String(I::str(value))
    }

    /// An array of `values`.
    #[must_use]
    pub fn array(values: impl IntoIterator<Item = Json<I>>) -> Self {
        Json::Array(I::array(values.into_iter().collect()))
    }

    /// An object from key–value pairs, in any order.
    ///
    /// # Errors
    ///
    /// [`MapError::Duplicate`] if two pairs share a key.
    pub fn object<K: AsRef<str>>(
        pairs: impl IntoIterator<Item = (K, Json<I>)>,
    ) -> Result<Self, MapError> {
        Map::from_entries(
            pairs
                .into_iter()
                .map(|(key, value)| Entry {
                    key: I::str(key.as_ref()),
                    value,
                })
                .collect(),
        )
        .map(Json::Object)
    }

    /// A number from a float, if it is finite; JSON has no other kind.
    #[must_use]
    pub fn from_f64(value: f64) -> Option<Self> {
        Number::from_f64(value).map(Json::Number)
    }
}

impl<I: Index> From<bool> for Json<I> {
    fn from(value: bool) -> Self {
        Json::Bool(value)
    }
}

impl<I: Index> From<Number> for Json<I> {
    fn from(value: Number) -> Self {
        Json::Number(value)
    }
}

impl<I: Index> From<i64> for Json<I> {
    fn from(value: i64) -> Self {
        Json::Number(value.into())
    }
}

impl<I: Index> From<u64> for Json<I> {
    fn from(value: u64) -> Self {
        Json::Number(value.into())
    }
}

impl<I: Index> From<i32> for Json<I> {
    fn from(value: i32) -> Self {
        Json::Number(value.into())
    }
}

impl<I: Index> From<u32> for Json<I> {
    fn from(value: u32) -> Self {
        Json::Number(value.into())
    }
}

impl<I: Index> Clone for Json<I> {
    fn clone(&self) -> Self {
        match self {
            Json::Null => Json::Null,
            Json::Bool(value) => Json::Bool(*value),
            Json::Number(value) => Json::Number(value.clone()),
            Json::String(value) => Json::String(value.clone()),
            Json::Array(values) => Json::Array(values.clone()),
            Json::Object(map) => Json::Object(map.clone()),
        }
    }
}

/// Equality is structural and works across index families; shared storage is
/// recognized first, so comparing a tree with its own clone or extracted
/// subtree never descends.
///
/// Numbers compare the way `serde_json`'s do: `1` and `1.0` are distinct
/// JSON numbers, exactly as they are distinct JSON texts.
impl<I: Index, J: Index> PartialEq<Json<J>> for Json<I> {
    fn eq(&self, other: &Json<J>) -> bool {
        match (self, other) {
            (Json::Null, Json::Null) => true,
            (Json::Bool(left), Json::Bool(right)) => left == right,
            (Json::Number(left), Json::Number(right)) => left == right,
            (Json::String(left), Json::String(right)) => {
                order::same_str(left, right) || **left == **right
            }
            (Json::Array(left), Json::Array(right)) => {
                order::same_slice(left, right)
                    || (left.len() == right.len()
                        && left.iter().zip(right.iter()).all(|(l, r)| l == r))
            }
            (Json::Object(left), Json::Object(right)) => left == right,
            _ => false,
        }
    }
}

impl<I: Index> Eq for Json<I> {}

impl<I: Index> Hash for Json<I> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Json::Null => state.write_u8(0),
            Json::Bool(value) => {
                state.write_u8(1);
                value.hash(state);
            }
            Json::Number(value) => {
                state.write_u8(2);
                value.hash(state);
            }
            Json::String(value) => {
                state.write_u8(3);
                value.hash(state);
            }
            Json::Array(values) => {
                state.write_u8(4);
                state.write_usize(values.len());
                for value in values.iter() {
                    value.hash(state);
                }
            }
            Json::Object(map) => {
                state.write_u8(5);
                state.write_usize(map.len());
                for entry in map {
                    (*entry.key).hash(state);
                    entry.value.hash(state);
                }
            }
        }
    }
}

impl<I: Index> fmt::Display for Json<I> {
    /// Compact JSON, as [`Json::to_json_string`].
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.to_json_string())
    }
}

impl<I: Index> fmt::Debug for Json<I> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}
