use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use covalence_lib_crypto::ed25519::SigningKey;

static FIXTURE_ID: AtomicU64 = AtomicU64::new(0);

#[test]
fn no_arguments_preserves_the_component_smoke_command() {
    let Some(binary) = nucleus_binary() else {
        return;
    };
    let output = Command::new(binary).output().expect("run smoke command");
    assert!(output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("hello from nucleus: SQLite returned 42")
    );
}

#[test]
fn exports_then_imports_signed_facts_in_a_fresh_process() {
    let Some(binary) = nucleus_binary() else {
        return;
    };
    let paths = FixturePaths::new();
    fs::write(&paths.secret, [23; 32]).expect("write secret key");

    let export = export_command(&binary, &paths)
        .output()
        .expect("run exporter");
    assert!(
        export.status.success(),
        "export failed: {}",
        String::from_utf8_lossy(&export.stderr)
    );
    let export_stdout = String::from_utf8_lossy(&export.stdout);
    assert!(export_stdout.contains("2 addition tables"));
    assert!(export_stdout.contains("2 persistent CAS tables"));
    assert!(export_stdout.contains("1 byte-length relations"));
    assert_eq!(
        fs::read(&paths.public).expect("read generated public key"),
        SigningKey::from_bytes(&[23; 32]).verifying_key().to_bytes()
    );

    let import = import_command(&binary, &paths)
        .output()
        .expect("run importer");
    assert!(
        import.status.success(),
        "import failed: {}",
        String::from_utf8_lossy(&import.stderr)
    );
    let stdout = String::from_utf8_lossy(&import.stdout);
    assert!(stdout.contains("integers: 2 facts"));
    assert!(stdout.contains("-42 = -20 + -22"));
    assert!(stdout.contains("-9223372036854775807 = -9223372036854775808 + 1"));
    assert!(stdout.contains("naturals: 2 facts"));
    assert!(stdout.contains("2 = 1 + 1"));
    assert!(stdout.contains("42 = 20 + 22"));
    assert!(stdout.contains("persistent CAS tables: 2"));
    assert!(stdout.contains("  binary_cas"));
    assert!(stdout.contains("  text_cas"));
    assert!(stdout.contains("byte_lengths: 4 byte-length facts"));
    assert!(stdout.contains("binary_cas/"));
    assert!(stdout.contains("text_cas/"));
    assert!(stdout.contains(": 4 bytes"));
    assert!(stdout.contains(": 6 bytes"));
    assert!(stdout.contains(": 14 bytes"));
    assert!(stdout.contains("snapshot image resident in CAS: true"));
}

#[test]
fn import_rejects_modified_images_and_wrong_keys() {
    let Some(binary) = nucleus_binary() else {
        return;
    };
    let paths = FixturePaths::new();
    fs::write(&paths.secret, [29; 32]).expect("write secret key");
    assert!(
        export_command(&binary, &paths)
            .status()
            .expect("run exporter")
            .success()
    );

    let mut envelope = fs::read(&paths.envelope).expect("read envelope");
    envelope[100] ^= 1;
    fs::write(&paths.envelope, &envelope).expect("modify envelope");
    let modified = import_command(&binary, &paths)
        .output()
        .expect("import modified");
    assert!(!modified.status.success());
    assert!(String::from_utf8_lossy(&modified.stderr).contains("signature was not accepted"));

    envelope[100] ^= 1;
    fs::write(&paths.envelope, envelope).expect("restore envelope");
    fs::write(
        &paths.public,
        SigningKey::from_bytes(&[30; 32]).verifying_key().to_bytes(),
    )
    .expect("replace public key");
    let wrong_key = import_command(&binary, &paths)
        .output()
        .expect("import wrong key");
    assert!(!wrong_key.status.success());
    assert!(String::from_utf8_lossy(&wrong_key.stderr).contains("signature was not accepted"));
}

#[test]
fn export_rejects_a_malformed_secret_key_file() {
    let Some(binary) = nucleus_binary() else {
        return;
    };
    let paths = FixturePaths::new();
    fs::write(&paths.secret, [7; 31]).expect("write short secret key");
    let export = export_command(&binary, &paths)
        .output()
        .expect("run exporter");
    assert!(!export.status.success());
    assert!(String::from_utf8_lossy(&export.stderr).contains("must contain 32 bytes"));
    assert!(!paths.envelope.exists());
    assert!(!paths.public.exists());
}

fn nucleus_binary() -> Option<PathBuf> {
    std::env::var_os("CARGO_BIN_EXE_nucleus").map(PathBuf::from)
}

fn export_command(binary: &Path, paths: &FixturePaths) -> Command {
    let mut command = Command::new(binary);
    command
        .args(["snapshot", "export"])
        .arg(&paths.envelope)
        .arg(&paths.secret)
        .arg(&paths.public);
    command
}

fn import_command(binary: &Path, paths: &FixturePaths) -> Command {
    let mut command = Command::new(binary);
    command
        .args(["snapshot", "import"])
        .arg(&paths.envelope)
        .arg(&paths.public);
    command
}

struct FixturePaths {
    directory: PathBuf,
    envelope: PathBuf,
    secret: PathBuf,
    public: PathBuf,
}

impl FixturePaths {
    fn new() -> Self {
        let id = FIXTURE_ID.fetch_add(1, Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("nucleus-snapshot-cli-{}-{id}", std::process::id()));
        fs::create_dir(&directory).expect("create fixture directory");
        Self {
            envelope: directory.join("snapshot.nucleus"),
            secret: directory.join("secret.key"),
            public: directory.join("public.key"),
            directory,
        }
    }
}

impl Drop for FixturePaths {
    fn drop(&mut self) {
        remove_if_present(&self.envelope);
        remove_if_present(&self.secret);
        remove_if_present(&self.public);
        let _ = fs::remove_dir(&self.directory);
    }
}

fn remove_if_present(path: &Path) {
    if let Err(error) = fs::remove_file(path) {
        assert_eq!(error.kind(), std::io::ErrorKind::NotFound);
    }
}
