//! Immutable O256-addressed `SQLite` files.

use std::io;
use std::str::FromStr;
use std::sync::Arc;

use covalence_data_cas::Cas;
use covalence_lib_hash::O256;

use super::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, OpenedFile,
    SyncFlags, Vfs,
};

/// A VFS exposing immutable CAS objects under their hexadecimal O256 address.
pub struct CasVfs<C: ?Sized> {
    cas: Arc<C>,
}

impl<C: ?Sized> CasVfs<C> {
    /// Constructs a CAS-backed VFS.
    #[must_use]
    pub const fn new(cas: Arc<C>) -> Self {
        Self { cas }
    }

    /// Borrows the backing CAS.
    #[must_use]
    pub fn cas(&self) -> &C {
        &self.cas
    }
}

/// An immutable `SQLite` file backed by authenticated CAS range reads.
pub struct CasFile<C: ?Sized> {
    cas: Arc<C>,
    address: O256,
    len: u64,
}

impl<C: ?Sized> std::fmt::Debug for CasFile<C> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CasFile")
            .field("address", &self.address)
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

fn address(path: &str) -> io::Result<O256> {
    O256::from_str(path).map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))
}

fn source_error(error: impl std::error::Error + Send + Sync + 'static) -> io::Error {
    io::Error::other(error)
}

impl<C> Vfs for CasVfs<C>
where
    C: Cas + ?Sized + 'static,
    C::Error: std::error::Error + Send + Sync + 'static,
{
    type File = CasFile<C>;

    fn open(
        &self,
        path: Option<&str>,
        kind: OpenKind,
        flags: OpenFlags,
    ) -> io::Result<OpenedFile<Self::File>> {
        if kind != OpenKind::MainDb
            || flags
                .intersects(OpenFlags::CREATE | OpenFlags::READ_WRITE | OpenFlags::DELETE_ON_CLOSE)
        {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "CAS VFS only opens immutable main databases",
            ));
        }
        let path = path.ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "content address required")
        })?;
        let address = address(path)?;
        let len = self
            .cas
            .len(address)
            .map_err(source_error)?
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, path.to_owned()))?;
        Ok(OpenedFile::new(
            CasFile {
                cas: Arc::clone(&self.cas),
                address,
                len,
            },
            OpenFlags::READ_ONLY,
        ))
    }

    fn delete(&self, _path: &str, _sync_dir: bool) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "immutable CAS",
        ))
    }

    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool> {
        if check == AccessCheck::ReadWrite {
            return Ok(false);
        }
        let Ok(address) = address(path) else {
            return Ok(false);
        };
        self.cas
            .len(address)
            .map(|length| length.is_some())
            .map_err(source_error)
    }

    fn full_pathname(&self, path: &str) -> io::Result<String> {
        address(path)?;
        Ok(path.to_owned())
    }
}

impl<C> File for CasFile<C>
where
    C: Cas + ?Sized,
    C::Error: std::error::Error + Send + Sync + 'static,
{
    fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<usize> {
        let available = self.len.saturating_sub(offset);
        let read_len = available.min(buf.len() as u64);
        if read_len == 0 {
            buf.fill(0);
            return Ok(0);
        }
        let end = offset
            .checked_add(read_len)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "range overflow"))?;
        let data = self
            .cas
            .read(self.address, offset..end)
            .map_err(source_error)?
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "CAS object disappeared"))?;
        if data.len() as u64 != read_len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "CAS returned the wrong range length",
            ));
        }
        let read_len = data.len();
        buf[..read_len].copy_from_slice(&data);
        buf[read_len..].fill(0);
        Ok(read_len)
    }

    fn write(&self, _buf: &[u8], _offset: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "immutable CAS",
        ))
    }

    fn truncate(&self, _size: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "immutable CAS",
        ))
    }

    fn sync(&self, _flags: SyncFlags) -> io::Result<()> {
        Ok(())
    }

    fn file_size(&self) -> io::Result<u64> {
        Ok(self.len)
    }

    fn lock(&self, _level: LockLevel) -> io::Result<()> {
        Ok(())
    }

    fn unlock(&self, _level: LockLevel) -> io::Result<()> {
        Ok(())
    }

    fn current_lock(&self) -> LockLevel {
        LockLevel::None
    }

    fn device_characteristics(&self) -> DeviceCharacteristics {
        DeviceCharacteristics::IMMUTABLE
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;
    use std::sync::Mutex;

    use bytes::Bytes;
    use covalence_lib_hash::Obj;

    use super::*;

    const ADDRESS: O256 = Obj::from_array([0x42; 32]);

    struct MemoryCas {
        data: Bytes,
        reads: Mutex<Vec<Range<u64>>>,
    }

    impl Cas for MemoryCas {
        type Error = io::Error;

        fn len(&self, address: O256) -> io::Result<Option<u64>> {
            Ok((address == ADDRESS).then_some(self.data.len() as u64))
        }

        fn read(&self, address: O256, range: Range<u64>) -> io::Result<Option<Bytes>> {
            if address != ADDRESS {
                return Ok(None);
            }
            self.reads.lock().unwrap().push(range.clone());
            let start = usize::try_from(range.start)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            let end = usize::try_from(range.end)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            Ok(self.data.get(start..end).map(Bytes::copy_from_slice))
        }
    }

    #[test]
    fn file_reads_only_the_requested_range() {
        let cas = Arc::new(MemoryCas {
            data: Bytes::from_static(b"abcdefgh"),
            reads: Mutex::new(Vec::new()),
        });
        let vfs = CasVfs::new(Arc::clone(&cas));
        let file = vfs
            .open(
                Some(&ADDRESS.to_string()),
                OpenKind::MainDb,
                OpenFlags::READ_ONLY,
            )
            .unwrap();

        let mut output = [0; 3];
        assert_eq!(file.read(&mut output, 2).unwrap(), 3);
        assert_eq!(&output, b"cde");
        let reads = cas.reads.lock().unwrap();
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0], 2..5);
    }

    #[test]
    fn rejects_non_addresses_and_writable_opens() {
        let vfs = CasVfs::new(Arc::new(MemoryCas {
            data: Bytes::new(),
            reads: Mutex::new(Vec::new()),
        }));

        assert_eq!(
            vfs.open(
                Some("not-an-address"),
                OpenKind::MainDb,
                OpenFlags::READ_ONLY
            )
            .unwrap_err()
            .kind(),
            io::ErrorKind::InvalidInput
        );
        assert_eq!(
            vfs.open(
                Some(&ADDRESS.to_string()),
                OpenKind::MainDb,
                OpenFlags::READ_WRITE,
            )
            .unwrap_err()
            .kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(
            vfs.open(
                Some(&ADDRESS.to_string()),
                OpenKind::MainDb,
                OpenFlags::READ_ONLY | OpenFlags::DELETE_ON_CLOSE,
            )
            .unwrap_err()
            .kind(),
            io::ErrorKind::PermissionDenied
        );
    }
}
