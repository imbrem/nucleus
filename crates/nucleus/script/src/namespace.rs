//! Immutable navigation metadata for checked kernel rows.

use std::collections::BTreeMap;

use covalence_logic_hol::Ref;

/// A hierarchical mapping from source names to local HOL rows.
///
/// Namespaces are ordinary userspace metadata. They neither create theorem
/// facts nor change the kernel arena. The API uses explicit child and binding
/// accessors so host bindings can expose the same tree without leaking Rust
/// collection types.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Namespace {
    bindings: BTreeMap<String, Ref>,
    children: BTreeMap<String, Self>,
}

impl Namespace {
    /// Resolves a dot-separated binding from this namespace root.
    #[must_use]
    pub fn resolve(&self, path: &str) -> Option<Ref> {
        let mut parts = path.split('.').peekable();
        let mut namespace = self;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                return namespace.binding(part);
            }
            namespace = namespace.child(part)?;
        }
        None
    }

    /// Resolves a dot-separated binding from this namespace root.
    ///
    /// This compatibility alias is equivalent to [`resolve`](Self::resolve).
    #[must_use]
    pub fn get(&self, path: &str) -> Option<Ref> {
        self.resolve(path)
    }

    /// Returns one binding directly contained in this namespace.
    #[must_use]
    pub fn binding(&self, name: &str) -> Option<Ref> {
        self.bindings.get(name).copied()
    }

    /// Returns one immediate child namespace.
    #[must_use]
    pub fn child(&self, name: &str) -> Option<&Self> {
        self.children.get(name)
    }

    /// Returns the number of bindings directly contained here.
    #[must_use]
    pub fn binding_count(&self) -> u64 {
        self.bindings.len() as u64
    }

    /// Returns the number of immediate child namespaces.
    #[must_use]
    pub fn child_count(&self) -> u64 {
        self.children.len() as u64
    }

    /// Returns whether this namespace contains no bindings or children.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty() && self.children.is_empty()
    }

    /// Iterates bindings directly contained in this namespace.
    #[must_use]
    pub fn bindings(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.bindings
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Iterates immediate child namespaces.
    #[must_use]
    pub fn children(&self) -> impl ExactSizeIterator<Item = (&str, &Self)> {
        self.children
            .iter()
            .map(|(name, namespace)| (name.as_str(), namespace))
    }

    pub(crate) fn insert(&mut self, path: &str, reference: Ref) {
        let mut parts = path.split('.').peekable();
        let mut namespace = self;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                namespace.bindings.insert(part.to_owned(), reference);
                return;
            }
            namespace = namespace.children.entry(part.to_owned()).or_default();
        }
    }
}
