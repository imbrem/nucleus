use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(unix)]
use std::os::unix::fs::{OpenOptionsExt as _, PermissionsExt as _};

const TEMP_ATTEMPTS: usize = 128;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// Complete command description passed to an injectable process launcher.
#[derive(Debug)]
pub(crate) struct SqliteShellInvocation {
    program: OsString,
    arguments: Vec<OsString>,
    snapshot_path: PathBuf,
}

impl SqliteShellInvocation {
    pub(crate) fn program(&self) -> &OsStr {
        &self.program
    }

    pub(crate) fn arguments(&self) -> &[OsString] {
        &self.arguments
    }

    pub(crate) fn snapshot_path(&self) -> &Path {
        &self.snapshot_path
    }
}

/// Injectable boundary around launching the real `SQLite` shell.
pub(crate) trait SqliteShellLauncher {
    fn launch(&mut self, invocation: &SqliteShellInvocation) -> io::Result<()>;
}

/// Launches the `sqlite3` executable inherited from the process environment.
pub(crate) struct SystemSqliteShell;

impl SqliteShellLauncher for SystemSqliteShell {
    fn launch(&mut self, invocation: &SqliteShellInvocation) -> io::Result<()> {
        if !invocation.snapshot_path().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                "SQLite shell snapshot disappeared before launch",
            ));
        }
        let status = Command::new(invocation.program())
            .args(invocation.arguments())
            .status()?;
        if status.success() {
            Ok(())
        } else {
            Err(io::Error::other(format!(
                "sqlite3 exited with status {status}"
            )))
        }
    }
}

/// Writes owned snapshot bytes, runs the actual shell, and removes the copy.
///
/// No live `SQLite` connection crosses this boundary. The temporary file is
/// owner-readable only, and [`TemporarySnapshot`] retries removal during drop
/// if explicit cleanup fails.
pub(crate) fn launch_snapshot(
    bytes: &[u8],
    launcher: &mut dyn SqliteShellLauncher,
) -> Result<(), SqliteShellError> {
    let mut snapshot = TemporarySnapshot::create(bytes).map_err(SqliteShellError::Create)?;
    let uri = immutable_uri(snapshot.path()).ok_or(SqliteShellError::NonUtf8Path)?;
    let invocation = SqliteShellInvocation {
        program: OsString::from("sqlite3"),
        arguments: ["-readonly", "-nofollow", "-noinit", "--"]
            .into_iter()
            .map(OsString::from)
            .chain([OsString::from(uri)])
            .collect(),
        snapshot_path: snapshot.path().to_owned(),
    };
    let launch_result = launcher
        .launch(&invocation)
        .map_err(SqliteShellError::Launch);
    let cleaned = snapshot.cleanup().map_err(SqliteShellError::Cleanup);
    launch_result.and(cleaned)
}

fn immutable_uri(path: &Path) -> Option<String> {
    let path = path.to_str()?;
    let mut uri = String::from("file:");
    for byte in path.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b':' | b'-' | b'_' | b'.' | b'~') {
            uri.push(char::from(byte));
        } else {
            use std::fmt::Write as _;
            write!(uri, "%{byte:02X}").expect("writing to a String cannot fail");
        }
    }
    uri.push_str("?immutable=1");
    Some(uri)
}

struct TemporarySnapshot {
    path: Option<PathBuf>,
}

impl TemporarySnapshot {
    fn create(bytes: &[u8]) -> io::Result<Self> {
        for _ in 0..TEMP_ATTEMPTS {
            let sequence = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "nucleus-sqlite-shell-{}-{sequence}.sqlite",
                std::process::id()
            ));
            let mut options = OpenOptions::new();
            options.write(true).create_new(true);
            #[cfg(unix)]
            options.mode(0o600);
            let mut file = match options.open(&path) {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            };
            let snapshot = Self { path: Some(path) };
            file.write_all(bytes)?;
            file.flush()?;
            make_owner_read_only(&file)?;
            drop(file);
            return Ok(snapshot);
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not allocate a unique SQLite shell snapshot",
        ))
    }

    fn path(&self) -> &Path {
        self.path.as_deref().expect("temporary snapshot is live")
    }

    fn cleanup(&mut self) -> io::Result<()> {
        let Some(path) = self.path.take() else {
            return Ok(());
        };
        match remove_snapshot(&path) {
            Ok(()) => Ok(()),
            Err(error) => {
                self.path = Some(path);
                Err(error)
            }
        }
    }
}

impl Drop for TemporarySnapshot {
    fn drop(&mut self) {
        if let Some(path) = self.path.take() {
            let _ = remove_snapshot(&path);
        }
    }
}

#[cfg(unix)]
fn make_owner_read_only(file: &fs::File) -> io::Result<()> {
    file.set_permissions(fs::Permissions::from_mode(0o400))
}

#[cfg(unix)]
fn remove_snapshot(path: &Path) -> io::Result<()> {
    fs::remove_file(path)
}

#[cfg(not(unix))]
fn remove_snapshot(path: &Path) -> io::Result<()> {
    let mut permissions = fs::metadata(path)?.permissions();
    permissions.set_readonly(false);
    fs::set_permissions(path, permissions)?;
    fs::remove_file(path)
}

#[cfg(not(unix))]
fn make_owner_read_only(file: &fs::File) -> io::Result<()> {
    let mut permissions = file.metadata()?.permissions();
    permissions.set_readonly(true);
    file.set_permissions(permissions)
}

#[derive(Debug)]
pub(crate) enum SqliteShellError {
    Create(io::Error),
    NonUtf8Path,
    Launch(io::Error),
    Cleanup(io::Error),
}

impl fmt::Display for SqliteShellError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Create(error) => write!(formatter, "could not create shell snapshot: {error}"),
            Self::NonUtf8Path => formatter.write_str("shell snapshot path is not UTF-8"),
            Self::Launch(error) => write!(formatter, "could not run sqlite3: {error}"),
            Self::Cleanup(error) => write!(formatter, "could not remove shell snapshot: {error}"),
        }
    }
}

impl std::error::Error for SqliteShellError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Create(error) | Self::Launch(error) | Self::Cleanup(error) => Some(error),
            Self::NonUtf8Path => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Default)]
    struct InspectingLauncher {
        path: Option<PathBuf>,
        bytes: Vec<u8>,
        arguments: Vec<OsString>,
        #[cfg(unix)]
        mode: u32,
    }

    impl SqliteShellLauncher for InspectingLauncher {
        fn launch(&mut self, invocation: &SqliteShellInvocation) -> io::Result<()> {
            assert_eq!(invocation.program(), "sqlite3");
            assert!(invocation.snapshot_path().is_file());
            self.path = Some(invocation.snapshot_path().to_owned());
            self.bytes = fs::read(invocation.snapshot_path())?;
            self.arguments = invocation.arguments().to_vec();
            #[cfg(unix)]
            {
                self.mode = fs::metadata(invocation.snapshot_path())?
                    .permissions()
                    .mode()
                    & 0o777;
            }
            Ok(())
        }
    }

    #[test]
    fn launches_actual_sqlite_cli_shape_and_removes_owner_only_snapshot() {
        let mut launcher = InspectingLauncher::default();
        launch_snapshot(b"snapshot bytes", &mut launcher).expect("launch snapshot");

        assert_eq!(launcher.bytes, b"snapshot bytes");
        assert_eq!(
            &launcher.arguments[..4],
            ["-readonly", "-nofollow", "-noinit", "--"].map(OsString::from)
        );
        let uri = launcher.arguments[4].to_str().expect("UTF-8 URI");
        assert!(uri.starts_with("file:"));
        assert!(uri.ends_with("?immutable=1"));
        #[cfg(unix)]
        assert_eq!(launcher.mode, 0o400);
        assert!(!launcher.path.expect("captured path").exists());
    }

    struct FailingLauncher {
        path: Option<PathBuf>,
    }

    impl SqliteShellLauncher for FailingLauncher {
        fn launch(&mut self, invocation: &SqliteShellInvocation) -> io::Result<()> {
            self.path = Some(invocation.snapshot_path().to_owned());
            Err(io::Error::other("injected launch failure"))
        }
    }

    #[test]
    fn removes_snapshot_after_launcher_failure() {
        let mut launcher = FailingLauncher { path: None };
        assert!(matches!(
            launch_snapshot(b"snapshot bytes", &mut launcher),
            Err(SqliteShellError::Launch(_))
        ));
        assert!(!launcher.path.expect("captured path").exists());
    }
}
