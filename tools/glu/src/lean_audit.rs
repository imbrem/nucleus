use std::{
    ffi::OsStr,
    fmt, fs,
    path::{Component, Path, PathBuf},
    process::Command,
};

use color_eyre::eyre::{Result, WrapErr, bail};

const IGNORED_DIRECTORIES: &[&str] = &[".lake", "build", "generated", "vendor"];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Marker {
    Sorry,
    Admit,
    Todo,
}

impl Marker {
    const ALL: [Self; 3] = [Self::Sorry, Self::Admit, Self::Todo];

    const fn text(self) -> &'static str {
        match self {
            Self::Sorry => "sorry",
            Self::Admit => "admit",
            Self::Todo => "TODO",
        }
    }
}

impl fmt::Display for Marker {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.text())
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Finding {
    path: PathBuf,
    line: usize,
    column: usize,
    marker: Marker,
}

#[derive(Debug, Eq, PartialEq)]
struct Audit {
    files: usize,
    findings: Vec<Finding>,
}

/// Audits tracked Lean sources without interpreting Lean syntax. Markers in
/// comments and strings are intentional findings; identifier substrings are
/// not. This keeps `TODO` useful while making the policy easy to reproduce.
pub(crate) fn check(root: &Path) -> Result<()> {
    let audit = audit(root)?;
    if audit.findings.is_empty() {
        eprintln!("Lean source audit: {} tracked files clean", audit.files);
        return Ok(());
    }

    for finding in &audit.findings {
        eprintln!(
            "{}:{}:{}: forbidden Lean marker `{}`",
            finding.path.display(),
            finding.line,
            finding.column,
            finding.marker
        );
    }
    bail!(
        "Lean source audit found {} forbidden marker(s)",
        audit.findings.len()
    )
}

fn audit(root: &Path) -> Result<Audit> {
    let paths = tracked_lean_sources(root)?;
    let mut findings = Vec::new();
    for path in &paths {
        let source = fs::read_to_string(root.join(path))
            .wrap_err_with(|| format!("could not read {}", path.display()))?;
        findings.extend(find_markers(path, &source));
    }
    Ok(Audit {
        files: paths.len(),
        findings,
    })
}

fn tracked_lean_sources(root: &Path) -> Result<Vec<PathBuf>> {
    let output = Command::new("git")
        .args(["ls-files", "-z", "--", "lean"])
        .current_dir(root)
        .output()
        .wrap_err("could not list tracked Lean sources with git")?;
    if !output.status.success() {
        bail!(
            "git ls-files failed with {}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|bytes| !bytes.is_empty())
        .map(|bytes| {
            let path =
                std::str::from_utf8(bytes).wrap_err("tracked repository path is not UTF-8")?;
            Ok(PathBuf::from(path))
        })
        .filter_map(|path: Result<PathBuf>| match path {
            Ok(path) if is_lean_source(&path) => Some(Ok(path)),
            Ok(_) => None,
            Err(error) => Some(Err(error)),
        })
        .collect()
}

fn is_lean_source(path: &Path) -> bool {
    path.extension() == Some(OsStr::new("lean"))
        && path.starts_with("lean")
        && !path.components().any(|component| {
            let Component::Normal(name) = component else {
                return false;
            };
            IGNORED_DIRECTORIES
                .iter()
                .any(|ignored| name == OsStr::new(ignored))
        })
}

fn find_markers(path: &Path, source: &str) -> Vec<Finding> {
    let mut findings = Vec::new();
    for (line_index, line) in source.lines().enumerate() {
        for (column_index, (offset, _)) in line.char_indices().enumerate() {
            for marker in Marker::ALL {
                if has_marker_at(line, offset, marker) {
                    findings.push(Finding {
                        path: path.to_owned(),
                        line: line_index + 1,
                        column: column_index + 1,
                        marker,
                    });
                }
            }
        }
    }
    findings
}

fn has_marker_at(line: &str, offset: usize, marker: Marker) -> bool {
    let text = marker.text();
    line[offset..].starts_with(text)
        && line[..offset]
            .chars()
            .next_back()
            .is_none_or(|character| !is_identifier_character(character))
        && line[offset + text.len()..]
            .chars()
            .next()
            .is_none_or(|character| !is_identifier_continuation(marker, character))
}

fn is_identifier_character(character: char) -> bool {
    character.is_alphanumeric() || character == '_' || character == '\''
}

fn is_identifier_continuation(marker: Marker, character: char) -> bool {
    is_identifier_character(character) || (marker != Marker::Todo && matches!(character, '!' | '?'))
}

#[cfg(test)]
mod tests {
    use std::{
        process::Command,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;

    static NEXT_REPOSITORY: AtomicU64 = AtomicU64::new(0);

    struct TestRepository(PathBuf);

    impl TestRepository {
        fn new() -> Self {
            let sequence = NEXT_REPOSITORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("glu-lean-audit-{}-{sequence}", std::process::id()));
            fs::create_dir_all(&path).expect("create test repository");
            let status = Command::new("git")
                .args(["init", "--quiet"])
                .current_dir(&path)
                .status()
                .expect("run git init");
            assert!(status.success());
            Self(path)
        }

        fn write(&self, relative: &str, source: &str) {
            let path = self.0.join(relative);
            fs::create_dir_all(path.parent().expect("fixture has a parent"))
                .expect("create fixture directory");
            fs::write(path, source).expect("write fixture");
        }

        fn track(&self, relative: &str, source: &str) {
            self.write(relative, source);
            let status = Command::new("git")
                .args(["add", "-f", "--", relative])
                .current_dir(&self.0)
                .status()
                .expect("run git add");
            assert!(status.success());
        }
    }

    impl Drop for TestRepository {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).expect("remove test repository");
        }
    }

    #[test]
    fn accepts_clean_tracked_sources() {
        let repository = TestRepository::new();
        repository.track(
            "lean/Example.lean",
            "theorem example : True := by trivial\n",
        );

        assert_eq!(
            audit(&repository.0).expect("audit succeeds"),
            Audit {
                files: 1,
                findings: Vec::new(),
            }
        );
    }

    #[test]
    fn finds_each_forbidden_marker() {
        let findings = find_markers(
            Path::new("lean/Example.lean"),
            "theorem one : True := by sorry\n\
             theorem two : True := by admit\n\
             -- TODO: prove these\n",
        );

        assert_eq!(
            findings
                .iter()
                .map(|finding| finding.marker)
                .collect::<Vec<_>>(),
            vec![Marker::Sorry, Marker::Admit, Marker::Todo]
        );
        assert_eq!(
            findings
                .iter()
                .map(|finding| finding.line)
                .collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
    }

    #[test]
    fn uses_case_sensitive_identifier_boundaries() {
        let findings = find_markers(
            Path::new("lean/Example.lean"),
            "sorryAx admitFoo TODOING Sorry Admit todo αsorry sorry' sorry! admit?\n",
        );

        assert!(findings.is_empty());
    }

    #[test]
    fn scans_comments_and_strings_textually() {
        let findings = find_markers(
            Path::new("lean/Example.lean"),
            "-- TODO\ndef message := \"sorry and admit\"\n",
        );

        assert_eq!(
            findings
                .iter()
                .map(|finding| finding.marker)
                .collect::<Vec<_>>(),
            vec![Marker::Todo, Marker::Sorry, Marker::Admit]
        );
    }

    #[test]
    fn reports_multiple_locations_in_source_order() {
        let findings = find_markers(Path::new("lean/Example.lean"), "sorry\n  admit; sorry\n");

        assert_eq!(
            findings
                .iter()
                .map(|finding| (finding.line, finding.column, finding.marker))
                .collect::<Vec<_>>(),
            vec![
                (1, 1, Marker::Sorry),
                (2, 3, Marker::Admit),
                (2, 10, Marker::Sorry),
            ]
        );
    }

    #[test]
    fn ignores_untracked_outside_and_generated_sources() {
        let repository = TestRepository::new();
        repository.track("lean/Good.lean", "def good := True\n");
        repository.write("lean/Untracked.lean", "sorry\n");
        repository.track("other/Outside.lean", "sorry\n");
        for directory in IGNORED_DIRECTORIES {
            repository.track(&format!("lean/{directory}/Ignored.lean"), "sorry\n");
        }

        assert_eq!(
            audit(&repository.0).expect("audit succeeds"),
            Audit {
                files: 1,
                findings: Vec::new(),
            }
        );
    }

    #[test]
    fn check_fails_when_a_marker_is_found() {
        let repository = TestRepository::new();
        repository.track("lean/Bad.lean", "theorem bad : True := by sorry\n");

        let error = check(&repository.0).expect_err("marker must fail the check");
        assert!(error.to_string().contains("1 forbidden marker"));
    }
}
