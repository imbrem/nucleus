//! Adapter from whole-resource resolution to the low-level `SQLite` VFS.

use std::io;

use covalence_data_vfs::ResourceVfs;
use covalence_lib_sqlite::vfs::{AccessCheck, OpenFlags, OpenKind, OpenedFile, ReadOnlyFile, Vfs};

use crate::Bytes;

/// Exposes complete immutable resources through `SQLite` random-access I/O.
#[derive(Clone, Debug)]
pub struct ResourceVfsAdapter<R> {
    resources: R,
}

impl<R> ResourceVfsAdapter<R> {
    /// Wraps a format-neutral resource resolver.
    #[must_use]
    pub const fn new(resources: R) -> Self {
        Self { resources }
    }

    /// Borrows the underlying format-neutral resolver.
    #[must_use]
    pub const fn resources(&self) -> &R {
        &self.resources
    }

    /// Returns the underlying format-neutral resolver.
    #[must_use]
    pub fn into_inner(self) -> R {
        self.resources
    }
}

impl<R: ResourceVfs> Vfs for ResourceVfsAdapter<R> {
    type File = ReadOnlyFile<Bytes>;

    fn open(
        &self,
        path: Option<&str>,
        _kind: OpenKind,
        _flags: OpenFlags,
    ) -> io::Result<OpenedFile<Self::File>> {
        let path = path
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "resource name required"))?;
        let bytes = self.resources.read(path)?;
        Ok(OpenedFile::new(
            ReadOnlyFile::new(bytes),
            OpenFlags::READ_ONLY,
        ))
    }

    fn delete(&self, _path: &str, _sync_dir: bool) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only resource VFS",
        ))
    }

    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool> {
        match check {
            AccessCheck::Exists | AccessCheck::Read => match self.resources.read(path) {
                Ok(_) => Ok(true),
                Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
                Err(error) => Err(error),
            },
            AccessCheck::ReadWrite => Ok(false),
        }
    }

    fn full_pathname(&self, path: &str) -> io::Result<String> {
        Ok(path.to_owned())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use covalence_data_vfs::{MemoryVfs, ResourceVfs};
    use covalence_lib_sqlite::vfs::{File, OpenFlags, OpenKind};

    use super::*;

    #[test]
    fn one_mount_serves_whole_resources_and_sqlite_files() {
        let resources = MemoryVfs::new(BTreeMap::from([(
            "tactics/cache.sqlite".to_owned(),
            Bytes::from_static(b"SQLite format 3\0"),
        )]));
        let whole = resources.read("tactics/cache.sqlite").expect("resource");
        let sqlite = ResourceVfsAdapter::new(resources);
        let opened = sqlite
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
