use covalence_exec_wasm::{ExecError, Outcome, run, run_bytes};
use covalence_lang_wasm::{Limits, Profile, Value, load};
use covalence_lib_hash::{Blake3, HashNamespace, Sha256};

const ADD: &[u8] = include_bytes!("fixtures/add.wasm");

const RETURN_UNWINDS: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // header
    0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type
    0x03, 0x02, 0x01, 0x00, // function
    0x07, 0x07, 0x01, 0x03, b'r', b'e', b't', 0x00, 0x00, // export
    0x0a, 0x09, 0x01, 0x07, 0x00, 0x41, 0x07, 0x41, 0x08, 0x0f, 0x0b, // code
];

const LOCAL_ZERO: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // header
    0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type
    0x03, 0x02, 0x01, 0x00, // function
    0x07, 0x08, 0x01, 0x04, b'z', b'e', b'r', b'o', 0x00, 0x00, // export
    0x0a, 0x08, 0x01, 0x06, 0x01, 0x01, 0x7f, 0x20, 0x00, 0x0b, // code
];

#[test]
fn exact_add_fixture_returns_42() {
    let result = run_bytes(
        ADD,
        Profile::TinyCoreV0,
        Limits::default(),
        "add",
        &[Value::I32(20), Value::I32(22)],
        3,
    )
    .unwrap();

    assert_eq!(result.trace, []);
    assert_eq!(result.outcome, Outcome::Returned(vec![Value::I32(42)]));
    assert_eq!(result.fuel_consumed, 3);
}

#[test]
fn i32_add_wraps_as_word_arithmetic() {
    let loaded = load(ADD, Profile::TinyCoreV0, Limits::default()).unwrap();
    let result = run(
        loaded.module(),
        "add",
        &[Value::I32(u32::MAX), Value::I32(2)],
        3,
    )
    .unwrap();
    assert_eq!(result.outcome, Outcome::Returned(vec![Value::I32(1)]));
}

#[test]
fn fuel_exhaustion_is_not_a_return() {
    let loaded = load(ADD, Profile::TinyCoreV0, Limits::default()).unwrap();
    let result = run(loaded.module(), "add", &[Value::I32(20), Value::I32(22)], 2).unwrap();
    assert_eq!(result.outcome, Outcome::FuelExhausted);
    assert_eq!(result.fuel_consumed, 2);
}

#[test]
fn explicit_return_discards_lower_frame_values() {
    let result = run_bytes(
        RETURN_UNWINDS,
        Profile::TinyCoreV0,
        Limits::default(),
        "ret",
        &[],
        3,
    )
    .unwrap();
    assert_eq!(result.outcome, Outcome::Returned(vec![Value::I32(8)]));
    assert_eq!(result.fuel_consumed, 3);
}

#[test]
fn locals_are_zero_initialized() {
    let result = run_bytes(
        LOCAL_ZERO,
        Profile::TinyCoreV0,
        Limits::default(),
        "zero",
        &[],
        1,
    )
    .unwrap();
    assert_eq!(result.outcome, Outcome::Returned(vec![Value::I32(0)]));
    assert_eq!(result.fuel_consumed, 1);
}

#[test]
fn request_shape_is_checked_before_execution() {
    let loaded = load(ADD, Profile::TinyCoreV0, Limits::default()).unwrap();
    assert!(matches!(
        run(
            loaded.module(),
            "missing",
            &[Value::I32(20), Value::I32(22)],
            3,
        ),
        Err(ExecError::UnknownEntry { .. })
    ));
    assert!(matches!(
        run(loaded.module(), "add", &[Value::I32(20)], 3),
        Err(ExecError::ArgumentCount {
            expected: 2,
            actual: 1,
        })
    ));
}

#[test]
fn fixture_hashes_are_frozen() {
    assert_eq!(
        Sha256::hash(ADD).to_string(),
        "f61fd62f57c41269c3c23f360eeaf1090b1db9c38651106674d48bc65dba88ba"
    );
    assert_eq!(
        Blake3::hash(ADD).to_string(),
        "801ae5deb92905065f7f0baedcbec41ebf1c4f2206904f7da319a7e5f24e29a4"
    );
}
