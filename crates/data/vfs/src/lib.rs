//! Untrusted resolution of opaque resource names to immutable bytes.
//!
//! [`ResourceVfs`] does not interpret a name as a filesystem path or the bytes
//! as a particular format. Source readers, database adapters, Wasm runtimes,
//! and verified format checkers layer those interpretations on top.

use std::{collections::BTreeMap, io, sync::Arc};

pub use bytes::Bytes;

/// A virtual store of complete immutable byte resources.
pub trait ResourceVfs: Send + Sync {
    /// Reads one complete resource.
    ///
    /// # Errors
    ///
    /// Returns an error if `resource` is absent or cannot be read completely.
    fn read(&self, resource: &str) -> io::Result<Bytes>;
}

impl<T: ResourceVfs + ?Sized> ResourceVfs for &T {
    fn read(&self, resource: &str) -> io::Result<Bytes> {
        (**self).read(resource)
    }
}

impl<T: ResourceVfs + ?Sized> ResourceVfs for Arc<T> {
    fn read(&self, resource: &str) -> io::Result<Bytes> {
        (**self).read(resource)
    }
}

/// An immutable in-memory resource mount.
#[derive(Clone, Debug, Default)]
pub struct MemoryVfs {
    resources: Arc<BTreeMap<String, Bytes>>,
}

impl MemoryVfs {
    /// Creates a mount from complete resource contents.
    #[must_use]
    pub fn new(resources: BTreeMap<String, Bytes>) -> Self {
        Self {
            resources: Arc::new(resources),
        }
    }

    /// Borrows a resident resource without performing I/O.
    #[must_use]
    pub fn get(&self, resource: &str) -> Option<&Bytes> {
        self.resources.get(resource)
    }

    /// Iterates resident resource names and bytes in lexical order.
    #[must_use]
    pub fn resources(&self) -> impl ExactSizeIterator<Item = (&str, &Bytes)> {
        self.resources
            .iter()
            .map(|(name, bytes)| (name.as_str(), bytes))
    }
}

impl ResourceVfs for MemoryVfs {
    fn read(&self, resource: &str) -> io::Result<Bytes> {
        self.get(resource)
            .cloned()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, resource.to_owned()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_mount_returns_shared_bytes_and_not_found() {
        let mount = MemoryVfs::new(BTreeMap::from([(
            "logic.defs".to_owned(),
            Bytes::from_static(b"(define true)"),
        )]));
        let bytes = mount.read("logic.defs").expect("mounted resource");
        assert_eq!(bytes, Bytes::from_static(b"(define true)"));
        assert_eq!(
            mount.read("missing").expect_err("missing resource").kind(),
            io::ErrorKind::NotFound
        );
    }
}
