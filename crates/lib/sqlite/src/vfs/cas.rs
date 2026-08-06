//! Immutable O256-addressed `SQLite` files.
//!
//! A [`CasVfs`] serves one namespace: a logical path *is* a lowercase
//! hexadecimal O256 address. Nothing else resolves. Mounting one under the
//! conventional name [`CAS_VFS_NAME`] makes every resident object openable as
//! `file:<address>?vfs=cas`.

use std::io;
use std::str::FromStr;
use std::sync::Arc;

use covalence_data_cas::{Cas, CasObject};
use covalence_lib_hash::O256;

use super::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, OpenedFile,
    SyncFlags, Vfs,
};

/// The conventional `SQLite` VFS name for a mounted CAS.
///
/// Registering under this name is what makes `?vfs=cas` URIs work.
pub const CAS_VFS_NAME: &str = "cas";

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

/// Mounts a CAS as an `SQLite` VFS.
///
/// `name` selects the VFS in `?vfs=` URIs and in explicit open calls;
/// [`CAS_VFS_NAME`] is the conventional choice. The returned
/// [`RegisteredVfs`](super::RegisteredVfs) also carries the pointer identity,
/// which is what a trust-sensitive caller must compare against
/// [`ConnectionVfsExt::database_vfs`](super::ConnectionVfsExt::database_vfs);
/// a name alone proves nothing about what `SQLite` actually opened.
///
/// When `as_default` is set, this VFS becomes the one `SQLite` uses for paths
/// that name no VFS. That makes bare addresses openable, at the cost of making
/// ordinary filesystem paths unopenable unless they name the platform VFS
/// explicitly — `file:/path/to/db?vfs=unix` on Unix. Leaving it unset keeps
/// the platform default and reaches the CAS through `?vfs=cas`.
///
/// # Safety
///
/// Inherits the contract of [`register`](super::register): `SQLite`'s VFS
/// registry is process-global and has no atomic reserve-by-name operation, so
/// the caller must ensure nothing outside this registry concurrently registers
/// or unregisters this name.
///
/// # Errors
///
/// Returns an error for an invalid or already-registered name, or when
/// `SQLite` rejects the registration.
#[cfg(feature = "vfs-register")]
#[allow(
    unsafe_code,
    reason = "forwards the process-global contract of `register`"
)]
pub unsafe fn register_cas<C>(
    cas: Arc<C>,
    name: &str,
    as_default: bool,
) -> Result<super::RegisteredVfs, super::RegisterError>
where
    C: Cas + ?Sized + 'static,
    C::Error: std::error::Error + Send + Sync + 'static,
{
    // SAFETY: forwarded verbatim to the caller of this function.
    unsafe { super::register(name, CasVfs::new(cas), as_default) }
}

/// An immutable `SQLite` file backed by an opened CAS object.
///
/// The object is resolved once, when `SQLite` opens the file, and held for as
/// long as the file is open. That is what lets a database survive its address
/// being dropped from the store mid-query: the file is not holding an address
/// to re-resolve, it is holding the object.
pub struct CasFile<O> {
    address: O256,
    object: O,
    len: u64,
}

impl<O> std::fmt::Debug for CasFile<O> {
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
    type File = CasFile<C::Object>;

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
        let object = self
            .cas
            .open(address)
            .map_err(source_error)?
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, path.to_owned()))?;
        let len = object.len();
        Ok(OpenedFile::new(
            CasFile {
                address,
                object,
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

impl<O> File for CasFile<O>
where
    O: CasObject,
    O::Error: std::error::Error + Send + Sync + 'static,
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
        let data = self.object.read(offset..end).map_err(source_error)?;
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

    /// Builds a real `SQLite` database and returns its complete bytes.
    #[cfg(feature = "vfs-register")]
    fn database_image(stem: &str) -> Vec<u8> {
        let path = std::env::temp_dir().join(format!("{stem}.sqlite"));
        let _ = std::fs::remove_file(&path);
        {
            let connection = crate::Connection::open(&path).unwrap();
            connection
                .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
                .unwrap();
        }
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        bytes
    }

    /// Records the ranges the VFS actually asks for, so the tests can show
    /// that reads stay ranged rather than materialising whole objects.
    struct Recorder {
        data: Bytes,
        reads: Arc<Mutex<Vec<Range<u64>>>>,
    }

    struct RecorderObject {
        data: Bytes,
        reads: Arc<Mutex<Vec<Range<u64>>>>,
    }

    impl Cas for Recorder {
        type Error = io::Error;
        type Object = RecorderObject;

        fn open(&self, address: O256) -> io::Result<Option<Self::Object>> {
            if address != ADDRESS {
                return Ok(None);
            }
            Ok(Some(RecorderObject {
                data: self.data.clone(),
                reads: Arc::clone(&self.reads),
            }))
        }
    }

    impl CasObject for RecorderObject {
        type Error = io::Error;

        fn len(&self) -> u64 {
            self.data.len() as u64
        }

        fn read(&self, range: Range<u64>) -> io::Result<Bytes> {
            self.reads.lock().unwrap().push(range.clone());
            let start = usize::try_from(range.start)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            let end = usize::try_from(range.end)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "range too large"))?;
            self.data
                .get(start..end)
                .map(Bytes::copy_from_slice)
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "range out of bounds"))
        }
    }

    #[test]
    fn file_reads_only_the_requested_range() {
        let reads = Arc::new(Mutex::new(Vec::new()));
        let cas = Arc::new(Recorder {
            data: Bytes::from_static(b"abcdefgh"),
            reads: Arc::clone(&reads),
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
        // Opening resolved the object; only the requested page was fetched.
        let reads = reads.lock().unwrap();
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0], 2..5);
    }

    #[test]
    fn rejects_non_addresses_and_writable_opens() {
        let vfs = CasVfs::new(Arc::new(Recorder {
            data: Bytes::new(),
            reads: Arc::new(Mutex::new(Vec::new())),
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

    #[cfg(feature = "vfs-register")]
    #[test]
    #[allow(unsafe_code, reason = "registers a VFS name private to this test")]
    fn a_mounted_cas_opens_databases_by_address() {
        use covalence_data_cas::MemoryCas;

        use crate::vfs::ConnectionVfsExt;
        use crate::{Connection, OpenFlags as SqliteOpenFlags};

        let cas = Arc::new(MemoryCas::new());
        let address = cas.insert(database_image("cas-vfs-by-address")).unwrap();

        // A private name stands in for CAS_VFS_NAME: the test process must not
        // fight other tests over one process-global registration.
        // SAFETY: this name is unique to this test and nothing else registers it.
        let mounted =
            unsafe { register_cas(Arc::clone(&cas), "covalence-test-cas-address", false) }.unwrap();

        let connection = Connection::open_with_flags_and_vfs(
            address.to_string(),
            SqliteOpenFlags::SQLITE_OPEN_READ_ONLY,
            mounted.name().as_str(),
        )
        .unwrap();

        // The name only selected the VFS; this is the check that it was used.
        assert_eq!(connection.database_vfs("main").unwrap(), mounted.identity());
        assert_eq!(
            connection
                .query_row("SELECT n FROM value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );
    }

    #[cfg(feature = "vfs-register")]
    #[test]
    #[allow(unsafe_code, reason = "registers a VFS name private to this test")]
    fn a_mounted_cas_attaches_through_a_vfs_uri() {
        use covalence_data_cas::MemoryCas;

        use crate::Connection;
        use crate::vfs::ConnectionVfsExt;

        let cas = Arc::new(MemoryCas::new());
        let address = cas.insert(database_image("cas-vfs-uri")).unwrap();
        // SAFETY: this name is unique to this test and nothing else registers it.
        let mounted =
            unsafe { register_cas(Arc::clone(&cas), "covalence-test-cas-uri", false) }.unwrap();

        // This is the shape a REPL or shell user types: `?vfs=<name>`.
        let uri = format!(
            "file:{}?mode=ro&immutable=1&vfs={}",
            address.hex(),
            mounted.name().as_str()
        );
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute("ATTACH DATABASE ?1 AS object", [&uri])
            .unwrap();

        assert_eq!(
            connection.database_vfs("object").unwrap(),
            mounted.identity()
        );
        assert_ne!(connection.database_vfs("main").unwrap(), mounted.identity());
        assert_eq!(
            connection
                .query_row("SELECT n FROM object.value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );
        assert!(
            connection
                .execute("INSERT INTO object.value VALUES (7)", [])
                .is_err()
        );
    }

    #[cfg(feature = "vfs-register")]
    #[test]
    #[allow(unsafe_code, reason = "registers a VFS name private to this test")]
    fn an_open_database_survives_its_address_being_dropped() {
        use covalence_data_cas::MemoryCas;

        use crate::Connection;

        let cas = Arc::new(MemoryCas::new());
        let address = cas.insert(database_image("cas-vfs-dropped")).unwrap();
        // SAFETY: this name is unique to this test and nothing else registers it.
        let mounted =
            unsafe { register_cas(Arc::clone(&cas), "covalence-test-cas-dropped", false) }.unwrap();

        let uri = format!(
            "file:{}?mode=ro&immutable=1&vfs={}",
            address.hex(),
            mounted.name().as_str()
        );
        let connection = Connection::open_in_memory().unwrap();
        connection
            .execute("ATTACH DATABASE ?1 AS object", [&uri])
            .unwrap();

        // Drop it from the store while the database is open and attached.
        assert!(cas.remove(address));

        // The attached database keeps answering: the file holds the object,
        // not the address. This is the property the whole interface exists for.
        assert_eq!(
            connection
                .query_row("SELECT n FROM object.value", [], |row| row.get::<_, i64>(0))
                .unwrap(),
            42
        );

        // A fresh open of the same address does not resolve.
        let second = Connection::open_in_memory().unwrap();
        assert!(
            second
                .execute("ATTACH DATABASE ?1 AS object", [&uri])
                .is_err()
        );
    }

    #[cfg(feature = "vfs-register")]
    #[test]
    #[allow(unsafe_code, reason = "registers a VFS name private to this test")]
    fn an_unknown_address_does_not_resolve() {
        use covalence_data_cas::MemoryCas;

        use crate::{Connection, OpenFlags as SqliteOpenFlags};

        let cas = Arc::new(MemoryCas::new());
        // SAFETY: this name is unique to this test and nothing else registers it.
        let mounted =
            unsafe { register_cas(Arc::clone(&cas), "covalence-test-cas-absent", false) }.unwrap();

        // A well-formed address which was never admitted.
        assert!(
            Connection::open_with_flags_and_vfs(
                ADDRESS.to_string(),
                SqliteOpenFlags::SQLITE_OPEN_READ_ONLY,
                mounted.name().as_str(),
            )
            .is_err()
        );
        // A path which is not an address at all.
        assert!(
            Connection::open_with_flags_and_vfs(
                "/etc/passwd",
                SqliteOpenFlags::SQLITE_OPEN_READ_ONLY,
                mounted.name().as_str(),
            )
            .is_err()
        );
    }
}
