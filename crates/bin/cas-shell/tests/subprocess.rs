//! The shell binary, exercised the way it is actually used.
//!
//! These tests spawn the real binary against a real served store. That is not
//! incidental: the shell terminates the process on its fatal paths, so it
//! cannot be tested in-process at all. Running it as a subprocess is both how
//! it ships and the only way to observe those paths.

use std::io;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixListener;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_data_cas::MemoryCas;
use covalence_data_cas_wire::serve;
use covalence_lib_hash::O256;
use covalence_lib_sqlite::Connection;

const SHELL: &str = env!("CARGO_BIN_EXE_covalence-cas-shell");

/// Builds a real database and returns its complete bytes.
fn database_image() -> Vec<u8> {
    let connection = Connection::open_in_memory().unwrap();
    connection
        .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
        .unwrap();
    connection.serialize("main").unwrap()
}

/// A served store and the socket the shell connects to.
struct Served {
    directory: PathBuf,
    socket: PathBuf,
    store: Arc<MemoryCas>,
}

impl Served {
    fn start() -> io::Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "covalence-shell-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&directory);
        std::fs::create_dir(&directory)?;
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;

        let socket = directory.join("socket");
        let listener = UnixListener::bind(&socket)?;
        let store = Arc::new(MemoryCas::new());

        // Serve every connection the shell makes, for the test's lifetime.
        let served = Arc::clone(&store);
        std::thread::spawn(move || {
            while let Ok((stream, _)) = listener.accept() {
                let store = Arc::clone(&served);
                std::thread::spawn(move || {
                    let Ok(mut reader) = stream.try_clone() else {
                        return;
                    };
                    let mut writer = stream;
                    let _ = serve(store.as_ref(), &mut reader, &mut writer);
                });
            }
        });

        Ok(Self {
            directory,
            socket,
            store,
        })
    }

    /// Runs the shell and returns its exit status and captured stdout.
    fn shell(&self, arguments: &[&str]) -> (i32, String) {
        let output = Command::new(SHELL)
            .arg("--cas")
            .arg(&self.socket)
            .args(arguments)
            .stdin(Stdio::null())
            .output()
            .expect("spawn the shell binary");
        (
            output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&output.stdout).into_owned(),
        )
    }
}

impl Drop for Served {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

fn uri(address: O256) -> String {
    format!("file:{}?mode=ro&immutable=1&vfs=cas", address.hex())
}

#[test]
fn the_shell_queries_a_database_it_never_had_a_file_for() {
    let served = Served::start().unwrap();
    let address = served.store.insert(database_image()).unwrap();

    let (status, output) = served.shell(&[&uri(address), "-batch", "SELECT n FROM value;"]);

    assert_eq!(status, 0, "shell exited non-zero; output: {output}");
    assert_eq!(output.trim(), "42");
}

#[test]
fn the_shell_cannot_write_through_the_mount() {
    let served = Served::start().unwrap();
    let address = served.store.insert(database_image()).unwrap();

    let (status, _) = served.shell(&[&uri(address), "-batch", "INSERT INTO value VALUES (7);"]);

    assert_ne!(status, 0, "the mount must reject writes");
}

#[test]
fn an_address_which_does_not_resolve_fails_to_open() {
    let served = Served::start().unwrap();
    // Admitted, then dropped: well-formed, no longer resident.
    let address = served.store.insert(database_image()).unwrap();
    assert!(served.store.remove(address));

    let (status, _) = served.shell(&[&uri(address), "-batch", "SELECT n FROM value;"]);

    assert_ne!(status, 0);
}

#[test]
fn a_fatal_shell_path_terminates_only_the_shell() {
    let served = Served::start().unwrap();

    // An unrecognised option is one of `shell.c`'s direct `exit()` calls. With
    // the shell in its own process this is ordinary: it exits non-zero and the
    // parent carries on. In-process it would have taken this test with it.
    let (status, _) = served.shell(&["--no-such-option", "-batch"]);
    assert_ne!(status, 0);

    // The store is still served and the next shell still works.
    let address = served.store.insert(database_image()).unwrap();
    let (status, output) = served.shell(&[&uri(address), "-batch", "SELECT n FROM value;"]);
    assert_eq!(status, 0, "output: {output}");
    assert_eq!(output.trim(), "42");
}

#[test]
fn missing_arguments_are_refused() {
    let output = Command::new(SHELL)
        .stdin(Stdio::null())
        .output()
        .expect("spawn the shell binary");
    assert!(!output.status.success());
}
