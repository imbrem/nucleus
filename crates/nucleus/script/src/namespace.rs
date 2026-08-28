//! Immutable hierarchical navigation metadata for checked kernel rows.

use std::{collections::BTreeMap, sync::Arc};

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_hol::Ref;
use smol_str::SmolStr;

/// Stable node ID within one immutable resident namespace table.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NamespaceId(u64);

impl NamespaceId {
    /// Returns the portable zero-based node index.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0
    }
}

/// One directly contained namespace binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamespaceBinding {
    name: SmolStr,
    reference: Ref,
}

impl NamespaceBinding {
    /// Returns the local binding name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the one-based row in this namespace's arena.
    #[must_use]
    pub const fn reference(&self) -> Ref {
        self.reference
    }
}

/// A name resolved to an arena identity and one-based row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolvedName {
    arena: Option<O256>,
    reference: Ref,
}

impl ResolvedName {
    /// Returns the foreign arena identity, or `None` for caller-local rows.
    #[must_use]
    pub const fn arena(self) -> Option<O256> {
        self.arena
    }

    /// Returns the one-based row in [`arena`](Self::arena).
    #[must_use]
    pub const fn reference(self) -> Ref {
        self.reference
    }
}

/// A resident or opaque foreign child namespace.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NamespaceChild {
    /// A cheap handle to already resident metadata.
    Resident(Namespace),
    /// A content address which is not loaded until name resolution requires it.
    Foreign(O256),
}

/// Resolves opaque content-addressed namespace metadata on demand.
pub trait NamespaceResolver {
    /// Resolver-specific failure.
    type Error;

    /// Resolves one exact foreign namespace address.
    ///
    /// # Errors
    ///
    /// Returns an error if the address is unavailable, malformed, rejected by
    /// policy, or cannot be decoded as namespace metadata.
    fn resolve(&mut self, address: O256) -> Result<Namespace, Self::Error>;
}

impl<F, E> NamespaceResolver for F
where
    F: FnMut(O256) -> Result<Namespace, E>,
{
    type Error = E;

    fn resolve(&mut self, address: O256) -> Result<Namespace, Self::Error> {
        self(address)
    }
}

/// Default resolver failure for an attempted foreign lookup.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("foreign namespace {address} requires an explicit resolver"))]
pub struct ForeignNamespaceError {
    /// Address which the default resolver refused to load.
    pub address: O256,
}

/// A resolver which refuses every foreign namespace.
#[derive(Clone, Copy, Debug, Default)]
pub struct RejectForeignNamespaces;

impl NamespaceResolver for RejectForeignNamespaces {
    type Error = ForeignNamespaceError;

    fn resolve(&mut self, address: O256) -> Result<Namespace, Self::Error> {
        Err(ForeignNamespaceError { address })
    }
}

/// A cheap immutable handle to one node in shared namespace metadata.
///
/// Each local non-root node is a `(parent ID, child name)` relationship.
/// Child edges may instead share another resident namespace or retain only a
/// foreign namespace hash. None of these navigation forms carries theorem
/// authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Namespace {
    data: Arc<NamespaceData>,
    root: NamespaceId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamespaceData {
    arena: Option<O256>,
    nodes: Vec<NamespaceNode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct NamespaceNode {
    parent: Option<NamespaceId>,
    name: Option<SmolStr>,
    bindings: BTreeMap<SmolStr, Ref>,
    children: BTreeMap<SmolStr, ChildEdge>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ChildEdge {
    Local(NamespaceId),
    Shared(Namespace),
    Foreign(O256),
}

impl Default for Namespace {
    fn default() -> Self {
        Self::new(None)
    }
}

impl Namespace {
    /// Creates empty metadata for rows in `arena`, or caller-local rows when
    /// `arena` is absent.
    #[must_use]
    pub fn new(arena: Option<O256>) -> Self {
        Self {
            data: Arc::new(NamespaceData {
                arena,
                nodes: vec![NamespaceNode {
                    parent: None,
                    name: None,
                    bindings: BTreeMap::new(),
                    children: BTreeMap::new(),
                }],
            }),
            root: NamespaceId(0),
        }
    }

    /// Returns the arena whose rows resident bindings name, when external.
    #[must_use]
    pub fn arena(&self) -> Option<O256> {
        self.data.arena
    }

    /// Returns this handle's resident node ID.
    #[must_use]
    pub const fn id(&self) -> NamespaceId {
        self.root
    }

    /// Returns this node's local name, or `None` for a table root.
    #[must_use]
    pub fn name(&self) -> Option<&str> {
        self.node().name.as_deref()
    }

    /// Returns this node's local parent, or `None` at a table/shared root.
    #[must_use]
    pub fn parent(&self) -> Option<Self> {
        self.node().parent.map(|root| Self {
            data: self.data.clone(),
            root,
        })
    }

    /// Returns one binding directly contained in this node.
    #[must_use]
    pub fn binding(&self, name: &str) -> Option<Ref> {
        self.node().bindings.get(name).copied()
    }

    /// Returns one immediate resident or opaque foreign child.
    #[must_use]
    pub fn child(&self, name: &str) -> Option<NamespaceChild> {
        self.node().children.get(name).map(|edge| match edge {
            ChildEdge::Local(root) => NamespaceChild::Resident(Self {
                data: self.data.clone(),
                root: *root,
            }),
            ChildEdge::Shared(namespace) => NamespaceChild::Resident(namespace.clone()),
            ChildEdge::Foreign(address) => NamespaceChild::Foreign(*address),
        })
    }

    /// Resolves a name without permitting foreign namespace I/O.
    ///
    /// # Errors
    ///
    /// Returns [`ForeignNamespaceError`] if lookup reaches an opaque foreign
    /// edge. Missing resident names return `Ok(None)`.
    pub fn resolve(&self, path: &str) -> Result<Option<ResolvedName>, ForeignNamespaceError> {
        self.resolve_with(path, &mut RejectForeignNamespaces)
    }

    /// Resolves a name, loading opaque namespace edges through `resolver`.
    ///
    /// # Errors
    ///
    /// Propagates any resolver failure encountered while walking the path.
    pub fn resolve_with<R: NamespaceResolver>(
        &self,
        path: &str,
        resolver: &mut R,
    ) -> Result<Option<ResolvedName>, R::Error> {
        let mut parts = path.split('.').peekable();
        let mut namespace = self.clone();
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                return Ok(namespace.binding(part).map(|reference| ResolvedName {
                    arena: namespace.arena(),
                    reference,
                }));
            }
            namespace = match namespace.child(part) {
                Some(NamespaceChild::Resident(child)) => child,
                Some(NamespaceChild::Foreign(address)) => resolver.resolve(address)?,
                None => return Ok(None),
            };
        }
        Ok(None)
    }

    /// Resolves a purely resident name to its row for compatibility.
    #[must_use]
    pub fn get(&self, path: &str) -> Option<Ref> {
        self.resolve_with(path, &mut |_address| -> Result<Namespace, ()> { Err(()) })
            .ok()
            .flatten()
            .map(ResolvedName::reference)
    }

    /// Returns the number of bindings directly contained here.
    #[must_use]
    pub fn binding_count(&self) -> u64 {
        u64::try_from(self.node().bindings.len()).unwrap_or(u64::MAX)
    }

    /// Returns the number of immediate child namespaces.
    #[must_use]
    pub fn child_count(&self) -> u64 {
        u64::try_from(self.node().children.len()).unwrap_or(u64::MAX)
    }

    /// Returns whether this node contains no bindings or children.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.node().bindings.is_empty() && self.node().children.is_empty()
    }

    /// Iterates bindings directly contained in this node.
    #[must_use]
    pub fn bindings(&self) -> impl ExactSizeIterator<Item = NamespaceBinding> + '_ {
        self.node()
            .bindings
            .iter()
            .map(|(name, reference)| NamespaceBinding {
                name: name.clone(),
                reference: *reference,
            })
    }

    /// Iterates immediate child names and handles without resolving foreign
    /// edges.
    #[must_use]
    pub fn children(&self) -> impl ExactSizeIterator<Item = (&str, NamespaceChild)> + '_ {
        self.node().children.iter().map(|(name, edge)| {
            let child = match edge {
                ChildEdge::Local(root) => NamespaceChild::Resident(Self {
                    data: self.data.clone(),
                    root: *root,
                }),
                ChildEdge::Shared(namespace) => NamespaceChild::Resident(namespace.clone()),
                ChildEdge::Foreign(address) => NamespaceChild::Foreign(*address),
            };
            (name.as_str(), child)
        })
    }

    /// Returns a copy with `namespace` mounted under `name` without walking it.
    #[must_use]
    pub fn with_namespace(&self, name: impl Into<SmolStr>, namespace: Self) -> Self {
        let mut result = self.clone();
        Arc::make_mut(&mut result.data).nodes[usize_from_id(result.root)]
            .children
            .insert(name.into(), ChildEdge::Shared(namespace));
        result
    }

    /// Returns a copy with an opaque foreign namespace mounted under `name`.
    #[must_use]
    pub fn with_foreign(&self, name: impl Into<SmolStr>, address: O256) -> Self {
        let mut result = self.clone();
        Arc::make_mut(&mut result.data).nodes[usize_from_id(result.root)]
            .children
            .insert(name.into(), ChildEdge::Foreign(address));
        result
    }

    pub(crate) fn mount(&mut self, path: &str, namespace: Self) {
        let data = Arc::make_mut(&mut self.data);
        let mut parts = path.split('.').peekable();
        let mut node = self.root;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                data.nodes[usize_from_id(node)]
                    .children
                    .insert(SmolStr::new(part), ChildEdge::Shared(namespace));
                return;
            }
            let existing = data.nodes[usize_from_id(node)].children.get(part).cloned();
            node = match existing {
                Some(ChildEdge::Local(child)) => child,
                Some(ChildEdge::Shared(_) | ChildEdge::Foreign(_)) => {
                    panic!("cannot mount through a mounted namespace")
                }
                None => {
                    let child = NamespaceId(
                        u64::try_from(data.nodes.len())
                            .expect("an in-memory node index fits in u64"),
                    );
                    data.nodes.push(NamespaceNode {
                        parent: Some(node),
                        name: Some(SmolStr::new(part)),
                        bindings: BTreeMap::new(),
                        children: BTreeMap::new(),
                    });
                    data.nodes[usize_from_id(node)]
                        .children
                        .insert(SmolStr::new(part), ChildEdge::Local(child));
                    child
                }
            };
        }
    }

    pub(crate) fn insert(&mut self, path: &str, reference: Ref) {
        let data = Arc::make_mut(&mut self.data);
        let mut parts = path.split('.').peekable();
        let mut node = self.root;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                data.nodes[usize_from_id(node)]
                    .bindings
                    .insert(SmolStr::new(part), reference);
                return;
            }
            let existing = data.nodes[usize_from_id(node)].children.get(part).cloned();
            node = match existing {
                Some(ChildEdge::Local(child)) => child,
                Some(ChildEdge::Shared(_) | ChildEdge::Foreign(_)) => {
                    panic!("cannot insert through a mounted namespace")
                }
                None => {
                    let child = NamespaceId(
                        u64::try_from(data.nodes.len())
                            .expect("an in-memory node index fits in u64"),
                    );
                    data.nodes.push(NamespaceNode {
                        parent: Some(node),
                        name: Some(SmolStr::new(part)),
                        bindings: BTreeMap::new(),
                        children: BTreeMap::new(),
                    });
                    data.nodes[usize_from_id(node)]
                        .children
                        .insert(SmolStr::new(part), ChildEdge::Local(child));
                    child
                }
            };
        }
    }

    fn node(&self) -> &NamespaceNode {
        &self.data.nodes[usize_from_id(self.root)]
    }
}

fn usize_from_id(id: NamespaceId) -> usize {
    usize::try_from(id.0).expect("resident namespace IDs fit in memory")
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;

    #[test]
    fn paths_are_parent_child_relations_and_clones_share_storage() {
        let mut namespace = Namespace::default();
        namespace.insert("logic.basic.and.comm", Ref::new(1).expect("reference"));
        let clone = namespace.clone();
        assert!(Arc::ptr_eq(&namespace.data, &clone.data));

        let NamespaceChild::Resident(logic) = namespace.child("logic").expect("logic") else {
            panic!("resident logic");
        };
        let NamespaceChild::Resident(basic) = logic.child("basic").expect("basic") else {
            panic!("resident basic");
        };
        let NamespaceChild::Resident(and) = basic.child("and").expect("and") else {
            panic!("resident and");
        };
        assert_eq!(and.name(), Some("and"));
        assert_eq!(and.parent().expect("parent").id(), basic.id());
        assert_eq!(and.binding("comm"), Ref::new(1));

        namespace.insert("logic.basic.or.comm", Ref::new(2).expect("reference"));
        assert!(!Arc::ptr_eq(&namespace.data, &clone.data));
        assert_eq!(clone.get("logic.basic.or.comm"), None);
    }

    #[test]
    fn foreign_namespaces_are_lazy_and_require_an_explicit_resolver() {
        let address = O256::from_bytes(b"large namespace");
        let root = Namespace::default().with_foreign("library", address);
        assert_eq!(
            root.child("library"),
            Some(NamespaceChild::Foreign(address))
        );
        assert_eq!(root.get("library.value"), None);
        assert_eq!(
            root.resolve("library.value")
                .expect_err("default rejection"),
            ForeignNamespaceError { address }
        );

        let mut foreign = Namespace::new(Some(address));
        foreign.insert("value", Ref::new(7).expect("reference"));
        let mut calls = 0;
        let resolved = root
            .resolve_with("library.value", &mut |requested| {
                calls += 1;
                assert_eq!(requested, address);
                Ok::<_, Infallible>(foreign.clone())
            })
            .expect("resolve")
            .expect("name");
        assert_eq!(calls, 1);
        assert_eq!(resolved.arena(), Some(address));
        assert_eq!(resolved.reference(), Ref::new(7).expect("reference"));
    }

    #[test]
    fn shared_exports_do_not_copy_or_enumerate_the_child() {
        let mut child = Namespace::default();
        child.insert("deep.value", Ref::new(3).expect("reference"));
        let child_data = child.data.clone();
        let root = Namespace::default().with_namespace("renamed", child);
        let NamespaceChild::Resident(mounted) = root.child("renamed").expect("mount") else {
            panic!("resident mount");
        };
        assert!(Arc::ptr_eq(&mounted.data, &child_data));
        assert_eq!(root.get("renamed.deep.value"), Ref::new(3));
    }

    #[test]
    fn path_mount_preserves_existing_spines_and_shares_the_child() {
        let mut child = Namespace::default();
        child.insert("value", Ref::new(3).expect("reference"));
        let child_data = child.data.clone();
        let mut root = Namespace::default();
        root.insert("package.local", Ref::new(1).expect("reference"));
        root.mount("package.imported", child);
        assert_eq!(root.get("package.local"), Ref::new(1));
        assert_eq!(root.get("package.imported.value"), Ref::new(3));
        let NamespaceChild::Resident(package) = root.child("package").expect("package") else {
            panic!("resident package");
        };
        let NamespaceChild::Resident(imported) = package.child("imported").expect("imported")
        else {
            panic!("resident import");
        };
        assert!(Arc::ptr_eq(&imported.data, &child_data));
    }

    #[test]
    fn deep_names_are_inserted_and_resolved_iteratively() {
        let path = std::iter::repeat_n("n", 10_000)
            .chain(["value"])
            .collect::<Vec<_>>()
            .join(".");
        let mut namespace = Namespace::default();
        namespace.insert(&path, Ref::new(1).expect("reference"));
        assert_eq!(namespace.get(&path), Ref::new(1));
    }
}
