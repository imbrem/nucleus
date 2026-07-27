use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use covalence_lib_crypto::ed25519::SigningKey;

#[test]
fn exports_then_imports_in_a_fresh_process() {
    let paths = FixturePaths::new();
    let signing_key = SigningKey::from_bytes(&[23; 32]);
    fs::write(&paths.secret, signing_key.to_bytes()).expect("write secret key");
    fs::write(&paths.public, signing_key.verifying_key().to_bytes()).expect("write public key");

    let export = command()
        .args(["snapshot", "export"])
        .arg(&paths.envelope)
        .arg(&paths.secret)
        .output()
        .expect("run exporter");
    assert!(
        export.status.success(),
        "export failed: {}",
        String::from_utf8_lossy(&export.stderr)
    );
    assert!(String::from_utf8_lossy(&export.stdout).contains("exported 2 addition tables"));

    let import = command()
        .args(["snapshot", "import"])
        .arg(&paths.envelope)
        .arg(&paths.public)
        .output()
        .expect("run importer");
    assert!(
        import.status.success(),
        "import failed: {}",
        String::from_utf8_lossy(&import.stderr)
    );
    let stdout = String::from_utf8_lossy(&import.stdout);
    assert!(stdout.contains("naturals RowId: 2 facts"));
    assert!(stdout.contains("integers WithoutRowId: 2 facts"));
    assert!(stdout.contains("snapshot image resident in CAS: true"));
}

#[test]
fn import_rejects_a_modified_envelope() {
    let paths = FixturePaths::new();
    let signing_key = SigningKey::from_bytes(&[29; 32]);
    fs::write(&paths.secret, signing_key.to_bytes()).expect("write secret key");
    fs::write(&paths.public, signing_key.verifying_key().to_bytes()).expect("write public key");
    assert!(
        command()
            .args(["snapshot", "export"])
            .arg(&paths.envelope)
            .arg(&paths.secret)
            .status()
            .expect("run exporter")
            .success()
    );

    let mut envelope = fs::read(&paths.envelope).expect("read envelope");
    envelope[100] ^= 1;
    fs::write(&paths.envelope, envelope).expect("modify envelope");
    assert!(
        !command()
            .args(["snapshot", "import"])
            .arg(&paths.envelope)
            .arg(&paths.public)
            .status()
            .expect("run importer")
            .success()
    );
}

fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_nucleus"))
}

struct FixturePaths {
    directory: PathBuf,
    envelope: PathBuf,
    secret: PathBuf,
    public: PathBuf,
}

impl FixturePaths {
    fn new() -> Self {
        let directory = std::env::temp_dir().join(format!(
            "nucleus-snapshot-cli-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).expect("create fixture directory");
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
