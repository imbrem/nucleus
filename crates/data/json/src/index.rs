//! Index families: the indirection a [`Json`] tree is threaded through.
//!
//! `Json<I>` never names a concrete pointer. Every indirect slot — string
//! contents, array elements, object entries — goes through the associated
//! types of an [`Index`] implementation, so one enum serves as a shared
//! immutable tree ([`Shared`]), a single-threaded one ([`Local`]), and a
//! borrowed view over someone else's storage ([`Refs`]).
//!
//! Per-slot associated types rather than a GAT pointer family: the tree has
//! exactly three indirect slots, and naming them individually is what lets
//! `Refs<'a>` use plain references without the trait having to thread a
//! lifetime through a generic `Ptr<T>`. Integer indices into a side table
//! do not fit this shape — resolving one needs the table in hand, which
//! `Deref` cannot express — and stay future work.

use std::{marker::PhantomData, ops::Deref, rc::Rc, sync::Arc};

use smol_str::SmolStr;

use crate::{Entry, Json};

/// A family of pointers threading a [`Json`] tree together.
///
/// Implementations are type-level markers — uninhabited or zero-sized — and
/// the trait carries no methods: a value of the family is never needed, only
/// its choice of pointer types. See [`Build`] for the families that can also
/// construct.
pub trait Index: Sized {
    /// String contents.
    type Str: Deref<Target = str> + Clone;
    /// Array elements, in order.
    type Array: Deref<Target = [Json<Self>]> + Clone;
    /// Object entries. [`Map`](crate::Map) keeps them sorted and unique.
    type Entries: Deref<Target = [Entry<Self>]> + Clone;
}

/// An [`Index`] whose pointers can be made from owned data.
///
/// [`Refs`] deliberately does not implement this: a borrowed view has nowhere
/// to put a new allocation. Constructing one means building the storage
/// yourself — an arena, a `Vec` kept alive elsewhere — and borrowing it.
pub trait Build: Index {
    /// Copies string contents in.
    fn str(value: &str) -> Self::Str;
    /// Takes ownership of array elements.
    fn array(values: Vec<Json<Self>>) -> Self::Array;
    /// Takes ownership of object entries, which the caller has sorted.
    fn entries(entries: Vec<Entry<Self>>) -> Self::Entries;
}

/// The `Arc`-backed family: `Json<Shared>` is the shared immutable view.
///
/// Cloning is a reference-count bump at every level, a subtree is extracted by
/// cloning the value that names it, and the whole tree is `Send + Sync`. This
/// is the default `I` and the representation the Python bindings wrap.
///
/// Strings are [`SmolStr`]: object keys and most JSON strings fit its 23-byte
/// inline form and never allocate, and longer strings sit behind an internal
/// `Arc`, so cloning stays O(1) either way.
pub enum Shared {}

impl Index for Shared {
    type Str = SmolStr;
    type Array = Arc<[Json<Shared>]>;
    type Entries = Arc<[Entry<Shared>]>;
}

impl Build for Shared {
    fn str(value: &str) -> Self::Str {
        SmolStr::new(value)
    }

    fn array(values: Vec<Json<Self>>) -> Self::Array {
        Arc::from(values)
    }

    fn entries(entries: Vec<Entry<Self>>) -> Self::Entries {
        Arc::from(entries)
    }
}

/// The `Rc`-backed family: [`Shared`] without atomics, for trees that stay on
/// one thread.
///
/// Strings are [`SmolStr`] here too. Its long-string form is atomically
/// counted even in this family; the common short string is inline and pays
/// nothing, and sharing one string type keeps the families interchangeable.
pub enum Local {}

impl Index for Local {
    type Str = SmolStr;
    type Array = Rc<[Json<Local>]>;
    type Entries = Rc<[Entry<Local>]>;
}

impl Build for Local {
    fn str(value: &str) -> Self::Str {
        SmolStr::new(value)
    }

    fn array(values: Vec<Json<Self>>) -> Self::Array {
        Rc::from(values)
    }

    fn entries(entries: Vec<Entry<Self>>) -> Self::Entries {
        Rc::from(entries)
    }
}

/// The borrowed family: `Json<Refs<'a>>` is a view of storage that lives at
/// least `'a` — an arena, statics, or slices someone else owns.
///
/// A view is `Copy`-cheap to clone and allocates nothing, and in exchange
/// cannot be built from owned data; see [`Build`].
///
/// A struct holding [`PhantomData`] rather than an uninhabited enum like its
/// siblings, because an enum may not carry a lifetime parameter it never
/// uses.
pub struct Refs<'a>(PhantomData<&'a ()>);

impl<'a> Index for Refs<'a> {
    type Str = &'a str;
    type Array = &'a [Json<Refs<'a>>];
    type Entries = &'a [Entry<Refs<'a>>];
}
