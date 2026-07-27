//! WebAssembly runtimes used by Nucleus.
//!
//! This crate is the dependency-policy boundary for executing WebAssembly.
//! Portable code can use [`wasmi`]; target-specific runtimes can be added
//! behind separate features without exposing them throughout the workspace.

#[cfg(feature = "wasmi")]
pub use wasmi;

#[cfg(all(test, feature = "wasmi"))]
mod tests {
    use wasmi::{Engine, Linker, Module, Store};

    #[test]
    fn executes_a_portable_module() {
        const MODULE: &[u8] = b"\0asm\x01\0\0\0\
            \x01\x05\x01\x60\x00\x01\x7f\
            \x03\x02\x01\x00\
            \x07\x0a\x01\x06answer\x00\x00\
            \x0a\x06\x01\x04\x00\x41\x2a\x0b";

        let engine = Engine::default();
        let module = Module::new(&engine, MODULE).expect("the test module should compile");
        let mut store = Store::new(&engine, ());
        let instance = Linker::new(&engine)
            .instantiate_and_start(&mut store, &module)
            .expect("the test module should instantiate and start");
        let answer = instance
            .get_typed_func::<(), i32>(&store, "answer")
            .expect("the exported function should have the expected type");

        assert_eq!(
            answer
                .call(&mut store, ())
                .expect("the exported function should run"),
            42
        );
    }
}
