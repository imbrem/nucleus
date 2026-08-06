//! End-to-end proof-module runs against real guest builds.
//!
//! Guest fixtures are ordinary workspace crates compiled to Wasm on
//! demand with the toolchain's own `cargo`; tests that need a Wasm
//! target skip cleanly (with a message) when the standard library for
//! that target is not installed.

use std::path::PathBuf;
use std::process::Command;
use std::sync::{Mutex, OnceLock, PoisonError};

use covalence_hol_wasm::{GuestAbi, GuestModule, RunError, Runner};
use covalence_nucleus::hol::Tm;

/// Serializes nested `cargo build` invocations across test threads.
static BUILD_LOCK: Mutex<()> = Mutex::new(());

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .expect("workspace root exists")
        .to_path_buf()
}

fn target_directory() -> PathBuf {
    std::env::var_os("CARGO_TARGET_DIR")
        .map_or_else(|| workspace_root().join("target"), PathBuf::from)
}

/// Returns whether the standard library for `target` is installed.
fn target_installed(target: &str) -> bool {
    static INSTALLED: OnceLock<Mutex<Vec<(String, bool)>>> = OnceLock::new();
    let cache = INSTALLED.get_or_init(|| Mutex::new(Vec::new()));
    let mut cache = cache.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some((_, installed)) = cache.iter().find(|(name, _)| name == target) {
        return *installed;
    }
    let installed = Command::new("rustc")
        .args(["--print", "target-libdir", "--target", target])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .is_some_and(|libdir| PathBuf::from(libdir).exists());
    cache.push((target.to_owned(), installed));
    installed
}

/// Builds a guest fixture for `target`, or skips when unsupported.
fn build_guest(package: &str, target: &str, artifact: &str) -> Option<Vec<u8>> {
    if !target_installed(target) {
        eprintln!("skipping: the {target} standard library is not installed");
        return None;
    }
    let guard = BUILD_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let status = Command::new(cargo)
        .current_dir(workspace_root())
        .args([
            "build",
            "--release",
            "--package",
            package,
            "--target",
            target,
        ])
        .status()
        .expect("run cargo build for the guest fixture");
    drop(guard);
    assert!(status.success(), "guest fixture build failed");
    let artifact = target_directory()
        .join(target)
        .join("release")
        .join(format!("{artifact}.wasm"));
    Some(std::fs::read(artifact).expect("read the built guest module"))
}

fn init_image() -> covalence_neutron::Bytes {
    covalence_hol_init::init_image().expect("generate the init image")
}

#[test]
fn core_wasm_guest_proves_and_commutativity() {
    let Some(bytes) = build_guest(
        "covalence-hol-guest-prop",
        "wasm32-unknown-unknown",
        "covalence_hol_guest_prop",
    ) else {
        return;
    };
    let runner = Runner::new().expect("create runner");
    let outcome = runner
        .run(
            &init_image(),
            GuestModule {
                bytes: &bytes,
                abi: GuestAbi::Core,
            },
        )
        .expect("run the guest");
    assert_eq!(outcome.status, 0, "guest failed: {:?}", outcome.guest_error);
    assert_eq!(outcome.proved.len(), 1);

    // Revalidate the recorded handle and check the judgement is the
    // commuted conjunction under the original hypothesis.
    let hol = outcome.connection.view();
    let logic = covalence_hol_logic::Logic::new(&hol).expect("resolve init exports");
    let theorem = hol
        .theorem_from_raw(outcome.proved[0])
        .expect("revalidate the finished theorem");
    let (_, vars, hyps, concl) = hol.theorem(theorem).expect("read the judgement");
    let p = hol.tm(Tm::Bv(0)).expect("p");
    let q = hol.tm(Tm::Bv(1)).expect("q");
    assert_eq!(hol.vars_entries(vars).expect("vars").len(), 2);
    assert_eq!(
        hol.hyps_entries(hyps).expect("hyps"),
        vec![logic.and_term(p, q).expect("and p q")]
    );
    assert_eq!(concl, logic.and_term(q, p).expect("and q p"));
}

#[test]
fn wasi_guest_runs_only_when_declared() {
    let Some(bytes) = build_guest(
        "covalence-hol-guest-prop-wasi",
        "wasm32-wasip1",
        "covalence_hol_guest_prop_wasi",
    ) else {
        return;
    };
    let runner = Runner::new().expect("create runner");

    // Without a declared WASI ABI the imports are simply absent: a
    // clean reported failure, not a soundness event.
    let refused = runner.run(
        &init_image(),
        GuestModule {
            bytes: &bytes,
            abi: GuestAbi::Core,
        },
    );
    assert!(matches!(refused, Err(RunError::Instantiate { .. })));

    let outcome = runner
        .run(
            &init_image(),
            GuestModule {
                bytes: &bytes,
                abi: GuestAbi::WasiP1,
            },
        )
        .expect("run the WASI guest");
    assert_eq!(outcome.status, 0, "guest failed: {:?}", outcome.guest_error);
    assert_eq!(outcome.proved.len(), 1);
    let hol = outcome.connection.view();
    let theorem = hol
        .theorem_from_raw(outcome.proved[0])
        .expect("revalidate the finished theorem");
    let (_, _, hyps, concl) = hol.theorem(theorem).expect("read the judgement");
    assert_eq!(hyps, hol.empty_hyps());
    assert_eq!(hol.tm_node(concl).expect("node"), Tm::Bool(true));
}

#[test]
fn broken_modules_fail_cleanly() {
    let runner = Runner::new().expect("create runner");
    let image = init_image();

    // Not a Wasm module at all.
    let garbage = runner.run(
        &image,
        GuestModule {
            bytes: b"not wasm",
            abi: GuestAbi::Core,
        },
    );
    assert!(matches!(garbage, Err(RunError::Compile { .. })));

    // A valid module with no `prove` entry point.
    let empty_module = b"\0asm\x01\0\0\0";
    let missing = runner.run(
        &image,
        GuestModule {
            bytes: empty_module,
            abi: GuestAbi::Core,
        },
    );
    assert!(matches!(missing, Err(RunError::MissingEntry { .. })));

    // An image without the init database is refused before any guest
    // runs.
    let unseeded = covalence_nucleus::Connection::<
        covalence_nucleus::Hol<covalence_nucleus::hol::AllowAll>,
    >::open_hol_in_memory(covalence_nucleus::hol::AllowAll)
    .expect("open unseeded")
    .serialize_image()
    .expect("serialize unseeded");
    let refused = runner.run(
        &unseeded,
        GuestModule {
            bytes: empty_module,
            abi: GuestAbi::Core,
        },
    );
    assert!(matches!(refused, Err(RunError::Resolve { .. })));
}
