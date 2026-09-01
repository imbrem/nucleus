#![cfg(not(target_arch = "wasm32"))]

use covalence_exec_wasm::{Outcome, run_bytes};
use covalence_lang_wasm::{Limits, Profile, Value};
use covalence_lib_wasm::wasmtime::{Engine, Instance, Module, Store};

const ADD: &[u8] = include_bytes!("fixtures/add.wasm");

fn run_add(left: u32, right: u32) -> u32 {
    let engine = Engine::default();
    let module = Module::from_binary(&engine, ADD).expect("compile add.wasm");
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).expect("instantiate add.wasm");
    let add = instance
        .get_typed_func::<(i32, i32), i32>(&mut store, "add")
        .expect("select add export");

    add.call(&mut store, (left.cast_signed(), right.cast_signed()))
        .expect("execute add export")
        .cast_unsigned()
}

#[test]
fn wasmtime_agrees_on_addition_and_wraparound() {
    for (left, right) in [
        (0, 0),
        (1, 1),
        (20, 22),
        (u32::MAX, 2),
        (u32::MAX, u32::MAX),
    ] {
        let reference = run_bytes(
            ADD,
            Profile::TinyCoreV0,
            Limits::default(),
            "add",
            &[Value::I32(left), Value::I32(right)],
            3,
        )
        .unwrap();
        let expected = left.wrapping_add(right);
        assert_eq!(
            reference.outcome,
            Outcome::Returned(vec![Value::I32(expected)])
        );
        assert_eq!(run_add(left, right), expected);
    }
}
