//! Whole-resource resolution layered over the low-level `SQLite` VFS.

use std::io;

use covalence_lib_sqlite::vfs::{ReadOnlyVfs, Vfs};

use crate::Bytes;

/// An `SQLite` VFS that also resolves whole immutable resources by key.
///
/// This is the common userspace mount boundary for source files, tactic
/// `Wasm`, binary constants, and databases. `SQLite` uses the inherited
/// random-access API; language frontends receive cheaply cloneable bytes.
pub trait ResourceVfs: Vfs {
    /// Reads one complete resource.
    ///
    /// # Errors
    ///
    /// Returns an error if `resource` is absent or cannot be read completely.
    fn read(&self, resource: &str) -> io::Result<Bytes>;
}

impl ResourceVfs for ReadOnlyVfs<Bytes> {
    fn read(&self, resource: &str) -> io::Result<Bytes> {
        self.get(resource)
            .cloned()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, resource.to_owned()))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use covalence_lib_sqlite::vfs::{File, OpenFlags, OpenKind};

    use super::*;

    #[test]
    fn one_mount_serves_whole_resources_and_sqlite_files() {
        let resources = ReadOnlyVfs::new(HashMap::from([(
            "tactics/cache.sqlite".to_owned(),
            Bytes::from_static(b"SQLite format 3\0"),
        )]));
        let whole = ResourceVfs::read(&resources, "tactics/cache.sqlite").expect("resource");
        let opened = resources
            .open(
                Some("tactics/cache.sqlite"),
                OpenKind::MainDb,
                OpenFlags::READ_ONLY,
            )
            .expect("SQLite file");
        let mut prefix = [0; 6];
        assert_eq!(opened.read(&mut prefix, 0).expect("prefix"), 6);
        assert_eq!(&prefix, &whole[..6]);
    }
}
