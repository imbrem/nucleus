use std::io;

use covalence_lib_sqlite::vfs::{
    AccessCheck, DeviceCharacteristics, File, LockLevel, OpenFlags, OpenKind, OpenedFile,
    SyncFlags, Vfs, register,
};

use crate::bindings;
use crate::bindings::covalence::sqlite_shell::read_only_vfs as host;

const VFS_NAME: &str = "cas";

struct HostVfs;

struct HostFile {
    file: host::File,
    len: u64,
}

impl std::fmt::Debug for HostFile {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HostFile")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

fn error(source: host::Error) -> io::Error {
    let kind = match source {
        host::Error::NotFound => io::ErrorKind::NotFound,
        host::Error::InvalidName | host::Error::InvalidRange => io::ErrorKind::InvalidInput,
        host::Error::TooLarge => io::ErrorKind::FileTooLarge,
        host::Error::Backend => io::ErrorKind::Other,
    };
    io::Error::new(kind, source)
}

impl Vfs for HostVfs {
    type File = HostFile;

    fn open(
        &self,
        path: Option<&str>,
        kind: OpenKind,
        _flags: OpenFlags,
    ) -> io::Result<OpenedFile<Self::File>> {
        if kind != OpenKind::MainDb {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "read-only VFS opens databases only",
            ));
        }
        let path = path
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "database name required"))?;
        let file = host::open(path).map_err(error)?;
        let len = file.size().map_err(error)?;
        Ok(OpenedFile::new(
            HostFile { file, len },
            OpenFlags::READ_ONLY,
        ))
    }

    fn delete(&self, _path: &str, _sync_dir: bool) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only VFS",
        ))
    }

    fn access(&self, path: &str, check: AccessCheck) -> io::Result<bool> {
        if check == AccessCheck::ReadWrite {
            return Ok(false);
        }
        match host::open(path) {
            Ok(_) => Ok(true),
            Err(host::Error::NotFound | host::Error::InvalidName) => Ok(false),
            Err(source) => Err(error(source)),
        }
    }

    fn full_pathname(&self, path: &str) -> io::Result<String> {
        if path.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "database name required",
            ));
        }
        Ok(path.to_owned())
    }
}

impl File for HostFile {
    fn read(&self, buf: &mut [u8], offset: u64) -> io::Result<usize> {
        let available = self.len.saturating_sub(offset);
        let wanted = available.min(buf.len() as u64);
        if wanted == 0 {
            buf.fill(0);
            return Ok(0);
        }
        let length = u32::try_from(wanted)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "read too large"))?;
        let bytes = self.file.read_at(offset, length).map_err(error)?;
        if bytes.len() != length as usize {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "VFS returned a short read",
            ));
        }
        buf[..bytes.len()].copy_from_slice(&bytes);
        buf[bytes.len()..].fill(0);
        Ok(bytes.len())
    }

    fn write(&self, _buf: &[u8], _offset: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only VFS",
        ))
    }

    fn truncate(&self, _size: u64) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "read-only VFS",
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

#[allow(unsafe_code, reason = "the vendored shell calls this C hook")]
#[unsafe(no_mangle)]
extern "C" fn covalence_shell_init() {
    if let Err(source) = register(VFS_NAME, HostVfs, true) {
        eprintln!("sqlite-shell: could not register host VFS: {source}");
    }
}

struct Component;

impl bindings::Guest for Component {
    fn run(arguments: Vec<String>) -> i32 {
        crate::run(&arguments).unwrap_or(1)
    }
}

bindings::export!(Component with_types_in bindings);
