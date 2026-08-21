use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_REPOSITORY: AtomicU64 = AtomicU64::new(0);

struct TestRepository(PathBuf);

impl TestRepository {
    fn new() -> Self {
        let sequence = NEXT_REPOSITORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "glu-lean-audit-cli-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(path.join("tools/glu")).expect("create repository layout");
        fs::write(path.join("Cargo.toml"), "[workspace]\n").expect("write root manifest");
        fs::write(
            path.join("tools/glu/Cargo.toml"),
            "[package]\nname = \"fixture\"\nversion = \"0.0.0\"\n",
        )
        .expect("write tool manifest");
        let status = Command::new("git")
            .args(["init", "--quiet"])
            .current_dir(&path)
            .status()
            .expect("run git init");
        assert!(status.success());
        Self(path)
    }

    fn track(&self, relative: &str, source: &str) {
        let path = self.0.join(relative);
        fs::create_dir_all(path.parent().expect("fixture has a parent"))
            .expect("create fixture directory");
        fs::write(path, source).expect("write fixture");
        let status = Command::new("git")
            .args(["add", "--", relative])
            .current_dir(&self.0)
            .status()
            .expect("run git add");
        assert!(status.success());
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_glu"))
            .args(args)
            .current_dir(self.0.join("tools"))
            .output()
            .expect("run glu")
    }
}

impl AsRef<Path> for TestRepository {
    fn as_ref(&self) -> &Path {
        &self.0
    }
}

impl Drop for TestRepository {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).expect("remove test repository");
    }
}

#[test]
fn command_exit_status_reflects_audit_result() {
    let clean = TestRepository::new();
    clean.track("lean/Clean.lean", "def clean := True\n");
    let clean_output = clean.run(&["lean", "audit"]);
    assert!(clean_output.status.success());
    assert!(String::from_utf8_lossy(&clean_output.stderr).contains("1 tracked files clean"));

    let bad = TestRepository::new();
    bad.track("lean/Bad.lean", "theorem bad : True := by sorry\n");
    let bad_output = bad.run(&["lean", "audit"]);
    assert!(!bad_output.status.success());
    let stderr = String::from_utf8_lossy(&bad_output.stderr);
    assert!(stderr.contains("lean/Bad.lean:1:26: forbidden Lean marker `sorry`"));
    assert!(stderr.contains("Lean source audit found 1 forbidden marker"));
}

#[test]
fn lean_check_audits_before_building() {
    let repository = TestRepository::new();
    repository.track("lean/Fixture/Bad.lean", "theorem bad : True := by sorry\n");
    repository.track("lean/Fixture/lakefile.toml", "name = \"Fixture\"\n");

    let output = repository.run(&["lean", "check"]);

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("forbidden Lean marker `sorry`"));
    assert!(!stderr.contains("build lean/Fixture"));
}

#[test]
fn lean_help_lists_the_nested_commands() {
    let output = Command::new(env!("CARGO_BIN_EXE_glu"))
        .args(["lean", "--help"])
        .output()
        .expect("run glu lean --help");

    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    for command in ["audit", "build", "check", "doc", "list"] {
        assert!(stdout.contains(command), "help omits {command}");
    }
}
