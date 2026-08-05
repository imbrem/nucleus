//! Runtime-mechanical execution instances used by Nucleus applications.

#[cfg(not(target_arch = "wasm32"))]
mod wasmtime_native {
    use std::error::Error as StdError;
    use std::fmt;

    use wasmtime::{Config, Engine, Store, StoreLimits, StoreLimitsBuilder, component::Component};

    /// Wasmtime types needed by protocol-owned generated component bindings.
    pub use wasmtime;

    /// Resource limits applied to one untrusted Wasmtime component invocation.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct WasmtimeComponentLimits {
        /// Maximum encoded component bytes accepted for compilation.
        pub component_bytes: usize,
        /// Maximum WebAssembly instructions, measured by Wasmtime fuel.
        pub fuel: u64,
        /// Maximum bytes in each linear memory.
        pub memory_bytes: usize,
        /// Maximum number of module instances in one store.
        pub instances: usize,
        /// Maximum number of core WebAssembly memories in one store.
        pub memories: usize,
        /// Maximum number of core WebAssembly tables in one store.
        pub tables: usize,
        /// Maximum elements in each core WebAssembly table.
        pub table_elements: usize,
    }

    impl Default for WasmtimeComponentLimits {
        fn default() -> Self {
            Self {
                component_bytes: 4 * 1024 * 1024,
                fuel: 10_000_000,
                memory_bytes: 16 * 1024 * 1024,
                instances: 16,
                memories: 8,
                tables: 8,
                table_elements: 65_536,
            }
        }
    }

    /// Generic native Wasmtime component runtime.
    ///
    /// This layer knows nothing about a Nucleus protocol, database, key, or signer. Protocol
    /// owners construct their linker and keep all semantic capabilities in `data`.
    #[derive(Clone)]
    pub struct WasmtimeComponentRuntime {
        engine: Engine,
        limits: WasmtimeComponentLimits,
    }

    impl WasmtimeComponentRuntime {
        /// Constructs a deterministic, fuel-metered component engine.
        ///
        /// # Errors
        ///
        /// Returns an error if Wasmtime rejects the engine configuration.
        pub fn new(limits: WasmtimeComponentLimits) -> Result<Self, WasmtimeRuntimeError> {
            let mut config = Config::new();
            config.wasm_component_model(true);
            config.consume_fuel(true);
            let engine = Engine::new(&config).map_err(WasmtimeRuntimeError::Engine)?;
            Ok(Self { engine, limits })
        }

        /// Returns the engine used for compilation, linking, and stores.
        #[must_use]
        pub const fn engine(&self) -> &Engine {
            &self.engine
        }

        /// Compiles one bounded component from its exact encoded bytes.
        ///
        /// # Errors
        ///
        /// Returns an error if the byte bound is exceeded or Wasmtime rejects the component.
        pub fn component(&self, bytes: &[u8]) -> Result<Component, WasmtimeRuntimeError> {
            if bytes.len() > self.limits.component_bytes {
                return Err(WasmtimeRuntimeError::ComponentTooLarge {
                    size: bytes.len(),
                    maximum: self.limits.component_bytes,
                });
            }
            Component::from_binary(&self.engine, bytes).map_err(WasmtimeRuntimeError::Component)
        }

        /// Creates one isolated store with hard limits and a fuel budget.
        ///
        /// # Errors
        ///
        /// Returns an error if Wasmtime rejects the fuel budget.
        pub fn store<T>(&self, data: T) -> Result<Store<WasmtimeStore<T>>, WasmtimeRuntimeError> {
            let limits = StoreLimitsBuilder::new()
                .memory_size(self.limits.memory_bytes)
                .instances(self.limits.instances)
                .memories(self.limits.memories)
                .tables(self.limits.tables)
                .table_elements(self.limits.table_elements)
                .build();
            let mut store = Store::new(&self.engine, WasmtimeStore { data, limits });
            store.limiter(|state| &mut state.limits);
            store
                .set_fuel(self.limits.fuel)
                .map_err(WasmtimeRuntimeError::Fuel)?;
            Ok(store)
        }
    }

    /// Store state separating protocol data from mechanical limits.
    pub struct WasmtimeStore<T> {
        /// Protocol-owned host state.
        pub data: T,
        limits: StoreLimits,
    }

    /// Failure to configure or compile with the native Wasmtime runtime.
    #[derive(Debug)]
    pub enum WasmtimeRuntimeError {
        /// Component bytes exceed the pre-compilation limit.
        ComponentTooLarge { size: usize, maximum: usize },
        /// Wasmtime rejected component bytes.
        Component(wasmtime::Error),
        /// Wasmtime engine configuration failed.
        Engine(wasmtime::Error),
        /// Wasmtime rejected the fuel budget.
        Fuel(wasmtime::Error),
    }

    impl fmt::Display for WasmtimeRuntimeError {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::ComponentTooLarge { size, maximum } => {
                    write!(formatter, "component is {size} bytes; maximum is {maximum}")
                }
                Self::Component(error) => write!(formatter, "could not compile component: {error}"),
                Self::Engine(error) => write!(formatter, "could not configure Wasmtime: {error}"),
                Self::Fuel(error) => write!(formatter, "could not set Wasmtime fuel: {error}"),
            }
        }
    }

    impl StdError for WasmtimeRuntimeError {}
}

#[cfg(not(target_arch = "wasm32"))]
pub use wasmtime_native::{
    WasmtimeComponentLimits, WasmtimeComponentRuntime, WasmtimeRuntimeError, WasmtimeStore,
    wasmtime,
};

#[cfg(not(target_arch = "wasm32"))]
mod core_wasm_owned_bytes {
    use std::error::Error as StdError;
    use std::fmt;

    use wasmtime::{
        Config, Engine, Linker, Module, Store, StoreLimits, StoreLimitsBuilder, WasmFeatures,
    };

    /// Fixed export names for the capability-free owned-bytes ABI.
    pub const CORE_WASM_MEMORY_EXPORT: &str = "memory";
    /// Function returning `(length << 32) | pointer` as one `i64`.
    pub const CORE_WASM_OWNED_BYTES_EXPORT: &str = "covalence_owned_bytes";
    /// Hard ceiling for bytes copied from any core-Wasm producer.
    pub const MAX_CORE_WASM_OWNED_BYTES: usize = 64 * 1024;

    /// Mechanical limits for one untrusted core-Wasm byte producer.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct CoreWasmOwnedBytesLimits {
        /// Maximum encoded module bytes accepted before compilation.
        pub module_bytes: usize,
        /// Wasmtime fuel available to compilation-independent guest execution.
        pub fuel: u64,
        /// Maximum size of the module's sole linear memory.
        pub memory_bytes: usize,
        /// Maximum copied output bytes.
        pub output_bytes: usize,
    }

    impl Default for CoreWasmOwnedBytesLimits {
        fn default() -> Self {
            Self {
                module_bytes: 4 * 1024 * 1024,
                fuel: 1_000_000,
                memory_bytes: 2 * 1024 * 1024,
                output_bytes: MAX_CORE_WASM_OWNED_BYTES,
            }
        }
    }

    /// Generic native Wasmtime wrapper for a no-import module returning owned bytes.
    ///
    /// This type cannot receive host data or capabilities and has no dependency on Nucleus,
    /// a database connection, a kernel, or key material. Its only successful result is copied
    /// untrusted bytes. `module_bytes` bounds input size, but compilation happens before the
    /// fuel-metered store exists: it is not a strict compilation CPU or memory bound. Callers
    /// which accept arbitrary modules should compile in a disposable worker/process with its own
    /// external resource limits.
    ///
    /// Each call creates a fresh store and performs exactly one direct instantiation. Imports are
    /// forbidden, so the configured one-instance limit cannot be consumed by host-mediated
    /// nested instantiation. Store growth failures are not configured to trap: WebAssembly
    /// `memory.grow`/`table.grow` can observe their normal failure sentinel and continue. Initial
    /// resources and successful growth remain bounded, and the copied range is checked against
    /// post-call memory.
    #[derive(Clone)]
    pub struct CoreWasmOwnedBytesRuntime {
        engine: Engine,
        limits: CoreWasmOwnedBytesLimits,
    }

    struct State {
        limits: StoreLimits,
    }

    impl CoreWasmOwnedBytesRuntime {
        /// Constructs a fuel-metered core-Wasm runtime.
        ///
        /// # Errors
        ///
        /// Returns an error if Wasmtime rejects the deterministic engine configuration.
        pub fn new(limits: CoreWasmOwnedBytesLimits) -> Result<Self, CoreWasmOwnedBytesError> {
            if limits.output_bytes > MAX_CORE_WASM_OWNED_BYTES {
                return Err(CoreWasmOwnedBytesError::OutputLimitTooLarge {
                    requested: limits.output_bytes,
                    maximum: MAX_CORE_WASM_OWNED_BYTES,
                });
            }
            let mut config = Config::new();
            config.consume_fuel(true);
            // Wasmtime's `ResourceLimiter` is not consulted for shared memories. Keep threads
            // disabled so every accepted memory is governed by the store's byte limit.
            config.wasm_features(WasmFeatures::THREADS, false);
            let engine = Engine::new(&config).map_err(CoreWasmOwnedBytesError::Engine)?;
            Ok(Self { engine, limits })
        }

        /// Executes one no-import module and copies its described memory range.
        ///
        /// Pointer and length are unsigned 32-bit fields in the returned `i64`. This method
        /// bounds the length, checks addition, checks the post-call memory range, and returns a
        /// fresh `Vec`; no guest memory or runtime authority escapes.
        ///
        /// # Errors
        ///
        /// Returns an error for an oversized/malformed module, any import, resource exhaustion,
        /// a trap, a missing or wrongly typed ABI export, or an invalid output range.
        pub fn execute(&self, module_bytes: &[u8]) -> Result<Vec<u8>, CoreWasmOwnedBytesError> {
            if module_bytes.len() > self.limits.module_bytes {
                return Err(CoreWasmOwnedBytesError::ModuleTooLarge {
                    size: module_bytes.len(),
                    maximum: self.limits.module_bytes,
                });
            }
            let module = Module::from_binary(&self.engine, module_bytes)
                .map_err(CoreWasmOwnedBytesError::Module)?;
            if let Some(import) = module.imports().next() {
                return Err(CoreWasmOwnedBytesError::ImportNotAllowed {
                    module: import.module().to_owned(),
                    name: import.name().to_owned(),
                });
            }

            let limits = StoreLimitsBuilder::new()
                .memory_size(self.limits.memory_bytes)
                .instances(1)
                .memories(1)
                .tables(1)
                .table_elements(1)
                .build();
            let mut store = Store::new(&self.engine, State { limits });
            store.limiter(|state| &mut state.limits);
            store
                .set_fuel(self.limits.fuel)
                .map_err(CoreWasmOwnedBytesError::Fuel)?;
            let linker = Linker::new(&self.engine);
            let instance = linker
                .instantiate(&mut store, &module)
                .map_err(CoreWasmOwnedBytesError::Instantiate)?;
            let memory = instance
                .get_memory(&mut store, CORE_WASM_MEMORY_EXPORT)
                .ok_or(CoreWasmOwnedBytesError::MissingMemory)?;
            let recipe = instance
                .get_typed_func::<(), i64>(&mut store, CORE_WASM_OWNED_BYTES_EXPORT)
                .map_err(CoreWasmOwnedBytesError::OwnedBytesExport)?;
            let descriptor = recipe
                .call(&mut store, ())
                .map_err(CoreWasmOwnedBytesError::Guest)?
                .cast_unsigned();
            let descriptor_bytes = descriptor.to_le_bytes();
            let pointer_u32 = u32::from_le_bytes([
                descriptor_bytes[0],
                descriptor_bytes[1],
                descriptor_bytes[2],
                descriptor_bytes[3],
            ]);
            let length_u32 = u32::from_le_bytes([
                descriptor_bytes[4],
                descriptor_bytes[5],
                descriptor_bytes[6],
                descriptor_bytes[7],
            ]);
            let pointer = usize::try_from(pointer_u32)
                .map_err(|_| CoreWasmOwnedBytesError::PointerNotRepresentable(pointer_u32))?;
            let length = usize::try_from(length_u32)
                .map_err(|_| CoreWasmOwnedBytesError::LengthNotRepresentable(length_u32))?;
            if length > self.limits.output_bytes {
                return Err(CoreWasmOwnedBytesError::OutputTooLarge {
                    size: length,
                    maximum: self.limits.output_bytes,
                });
            }
            let end = pointer
                .checked_add(length)
                .ok_or(CoreWasmOwnedBytesError::OutputRangeOverflow { pointer, length })?;
            let data = memory.data(&store);
            let bytes =
                data.get(pointer..end)
                    .ok_or(CoreWasmOwnedBytesError::OutputOutOfBounds {
                        pointer,
                        length,
                        memory_size: data.len(),
                    })?;
            Ok(bytes.to_vec())
        }
    }

    /// Rejection from the generic no-import core-Wasm byte runtime.
    #[derive(Debug)]
    pub enum CoreWasmOwnedBytesError {
        /// Engine configuration failed.
        Engine(wasmtime::Error),
        /// Encoded module exceeds the pre-compilation bound.
        ModuleTooLarge { size: usize, maximum: usize },
        /// Core-Wasm compilation failed.
        Module(wasmtime::Error),
        /// Configuration attempted to weaken the fixed output ceiling.
        OutputLimitTooLarge { requested: usize, maximum: usize },
        /// The module requested a host import and therefore a capability.
        ImportNotAllowed { module: String, name: String },
        /// Fuel configuration failed.
        Fuel(wasmtime::Error),
        /// Instantiation or the start function failed.
        Instantiate(wasmtime::Error),
        /// The required exported memory is absent or not a memory.
        MissingMemory,
        /// The owned-bytes descriptor export is absent or has the wrong type.
        OwnedBytesExport(wasmtime::Error),
        /// The descriptor function trapped or exhausted resources.
        Guest(wasmtime::Error),
        /// The claimed output exceeds the independent host output bound.
        OutputTooLarge { size: usize, maximum: usize },
        /// The 32-bit guest pointer cannot be represented by this host.
        PointerNotRepresentable(u32),
        /// The 32-bit guest length cannot be represented by this host.
        LengthNotRepresentable(u32),
        /// Pointer-plus-length overflowed the host address representation.
        OutputRangeOverflow { pointer: usize, length: usize },
        /// The claimed range does not lie in post-call guest memory.
        OutputOutOfBounds {
            pointer: usize,
            length: usize,
            memory_size: usize,
        },
    }

    impl fmt::Display for CoreWasmOwnedBytesError {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::Engine(error) => write!(formatter, "could not configure Wasmtime: {error}"),
                Self::ModuleTooLarge { size, maximum } => {
                    write!(formatter, "module is {size} bytes; maximum is {maximum}")
                }
                Self::Module(error) => write!(formatter, "could not compile core Wasm: {error}"),
                Self::OutputLimitTooLarge { requested, maximum } => write!(
                    formatter,
                    "requested output limit is {requested} bytes; hard maximum is {maximum}"
                ),
                Self::ImportNotAllowed { module, name } => {
                    write!(formatter, "core-Wasm byte guest imports {module}.{name}")
                }
                Self::Fuel(error) => write!(formatter, "could not set Wasmtime fuel: {error}"),
                Self::Instantiate(error) => {
                    write!(formatter, "could not instantiate guest: {error}")
                }
                Self::MissingMemory => {
                    write!(formatter, "guest does not export memory as `memory`")
                }
                Self::OwnedBytesExport(error) => {
                    write!(
                        formatter,
                        "guest has no `covalence_owned_bytes: () -> i64`: {error}"
                    )
                }
                Self::Guest(error) => write!(formatter, "guest descriptor call failed: {error}"),
                Self::OutputTooLarge { size, maximum } => {
                    write!(
                        formatter,
                        "guest output is {size} bytes; maximum is {maximum}"
                    )
                }
                Self::PointerNotRepresentable(pointer) => {
                    write!(formatter, "guest pointer {pointer} does not fit this host")
                }
                Self::LengthNotRepresentable(length) => {
                    write!(formatter, "guest length {length} does not fit this host")
                }
                Self::OutputRangeOverflow { pointer, length } => {
                    write!(
                        formatter,
                        "guest output range {pointer} + {length} overflows"
                    )
                }
                Self::OutputOutOfBounds {
                    pointer,
                    length,
                    memory_size,
                } => write!(
                    formatter,
                    "guest output range {pointer} + {length} exceeds {memory_size}-byte memory"
                ),
            }
        }
    }

    impl StdError for CoreWasmOwnedBytesError {}
}

#[cfg(not(target_arch = "wasm32"))]
pub use core_wasm_owned_bytes::{
    CORE_WASM_MEMORY_EXPORT, CORE_WASM_OWNED_BYTES_EXPORT, CoreWasmOwnedBytesError,
    CoreWasmOwnedBytesLimits, CoreWasmOwnedBytesRuntime, MAX_CORE_WASM_OWNED_BYTES,
};

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    enum Descriptor {
        Value(u64),
        Trap,
    }

    fn unsigned_leb(mut value: u64, bytes: &mut Vec<u8>) {
        loop {
            let byte = u8::try_from(value & 0x7f).expect("seven bits fit u8");
            value >>= 7;
            bytes.push(if value == 0 { byte } else { byte | 0x80 });
            if value == 0 {
                return;
            }
        }
    }

    fn signed_leb(mut value: i64, bytes: &mut Vec<u8>) {
        loop {
            let byte = u8::try_from(value & 0x7f).expect("seven bits fit u8");
            value >>= 7;
            let done = (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0);
            bytes.push(if done { byte } else { byte | 0x80 });
            if done {
                return;
            }
        }
    }

    fn name(value: &str, bytes: &mut Vec<u8>) {
        unsigned_leb(
            u64::try_from(value.len()).expect("Wasm name length fits u64"),
            bytes,
        );
        bytes.extend_from_slice(value.as_bytes());
    }

    fn section(id: u8, payload: &[u8], module: &mut Vec<u8>) {
        module.push(id);
        unsigned_leb(
            u64::try_from(payload.len()).expect("Wasm section length fits u64"),
            module,
        );
        module.extend_from_slice(payload);
    }

    fn byte_module_with_memories(
        data: &[u8],
        descriptor: Descriptor,
        import: bool,
        minimum_pages: u32,
        memory_count: usize,
    ) -> Vec<u8> {
        byte_module_with_resources(data, descriptor, import, minimum_pages, memory_count, 0, 0)
    }

    #[allow(clippy::too_many_arguments)]
    fn byte_module_with_resources(
        data: &[u8],
        descriptor: Descriptor,
        import: bool,
        minimum_pages: u32,
        memory_count: usize,
        table_count: usize,
        table_elements: u32,
    ) -> Vec<u8> {
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        // One `() -> i64` type.
        section(1, &[1, 0x60, 0, 1, 0x7e], &mut module);
        if import {
            let mut imports = vec![1];
            name("forbidden", &mut imports);
            name("capability", &mut imports);
            imports.extend_from_slice(&[0, 0]);
            section(2, &imports, &mut module);
        }
        section(3, &[1, 0], &mut module);
        if table_count != 0 {
            let mut tables = Vec::new();
            unsigned_leb(
                u64::try_from(table_count).expect("test table count fits u64"),
                &mut tables,
            );
            for _ in 0..table_count {
                tables.extend_from_slice(&[0x70, 1]); // funcref, min and max present
                unsigned_leb(u64::from(table_elements), &mut tables);
                unsigned_leb(u64::from(table_elements), &mut tables);
            }
            section(4, &tables, &mut module);
        }
        let mut memories = Vec::new();
        unsigned_leb(
            u64::try_from(memory_count).expect("test memory count fits u64"),
            &mut memories,
        );
        for _ in 0..memory_count {
            memories.push(1); // min and max present
            unsigned_leb(u64::from(minimum_pages), &mut memories);
            unsigned_leb(u64::from(minimum_pages), &mut memories);
        }
        section(5, &memories, &mut module);
        let mut exports = vec![2];
        name(CORE_WASM_MEMORY_EXPORT, &mut exports);
        exports.extend_from_slice(&[2, 0]);
        name(CORE_WASM_OWNED_BYTES_EXPORT, &mut exports);
        exports.extend_from_slice(&[0, u8::from(import)]);
        section(7, &exports, &mut module);
        let mut instructions = vec![0]; // no locals
        match descriptor {
            Descriptor::Value(value) => {
                instructions.push(0x42);
                signed_leb(value.cast_signed(), &mut instructions);
            }
            Descriptor::Trap => instructions.push(0),
        }
        instructions.push(0x0b);
        let mut code = vec![1];
        unsigned_leb(
            u64::try_from(instructions.len()).expect("test function length fits u64"),
            &mut code,
        );
        code.extend_from_slice(&instructions);
        section(10, &code, &mut module);
        if !data.is_empty() {
            let mut data_section = vec![1, 0, 0x41, 32, 0x0b];
            unsigned_leb(
                u64::try_from(data.len()).expect("test data length fits u64"),
                &mut data_section,
            );
            data_section.extend_from_slice(data);
            section(11, &data_section, &mut module);
        }
        module
    }

    fn memory_grow_denial_module() -> Vec<u8> {
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        section(1, &[1, 0x60, 0, 1, 0x7e], &mut module);
        section(3, &[1, 0], &mut module);
        section(5, &[1, 1, 1, 2], &mut module); // one memory, min 1, max 2 pages
        let mut exports = vec![2];
        name(CORE_WASM_MEMORY_EXPORT, &mut exports);
        exports.extend_from_slice(&[2, 0]);
        name(CORE_WASM_OWNED_BYTES_EXPORT, &mut exports);
        exports.extend_from_slice(&[0, 0]);
        section(7, &exports, &mut module);
        // Require `memory.grow(1) == -1`; trap if the configured one-page limit failed to deny it,
        // then return an empty owned byte range.
        let function = [
            0, // no locals
            0x41, 1, // i32.const 1
            0x40, 0, // memory.grow 0
            0x41, 0x7f, // i32.const -1
            0x47, // i32.ne
            0x04, 0x40, // if void
            0,    // unreachable
            0x0b, // end if
            0x42, 0,    // i64.const 0
            0x0b, // end function
        ];
        let mut code = vec![1];
        unsigned_leb(
            u64::try_from(function.len()).expect("test function length fits u64"),
            &mut code,
        );
        code.extend_from_slice(&function);
        section(10, &code, &mut module);
        module
    }

    fn shared_memory_module() -> Vec<u8> {
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        section(1, &[1, 0x60, 0, 1, 0x7e], &mut module);
        section(3, &[1, 0], &mut module);
        // One 33-page shared memory with min=max. Shared memories require a maximum.
        section(5, &[1, 3, 33, 33], &mut module);
        let mut exports = vec![2];
        name(CORE_WASM_MEMORY_EXPORT, &mut exports);
        exports.extend_from_slice(&[2, 0]);
        name(CORE_WASM_OWNED_BYTES_EXPORT, &mut exports);
        exports.extend_from_slice(&[0, 0]);
        section(7, &exports, &mut module);
        section(10, &[1, 4, 0, 0x42, 0, 0x0b], &mut module);
        module
    }

    fn byte_module(data: &[u8], descriptor: Descriptor, import: bool) -> Vec<u8> {
        byte_module_with_memories(data, descriptor, import, 1, 1)
    }

    fn wrong_export_module(memory_as_function: bool) -> Vec<u8> {
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        let result_type = if memory_as_function { 0x7e } else { 0x7f };
        section(1, &[1, 0x60, 0, 1, result_type], &mut module);
        section(3, &[1, 0], &mut module);
        if !memory_as_function {
            section(5, &[1, 1, 1, 1], &mut module);
        }
        let mut exports = vec![2];
        name(CORE_WASM_MEMORY_EXPORT, &mut exports);
        exports.extend_from_slice(&[if memory_as_function { 0 } else { 2 }, 0]);
        name(CORE_WASM_OWNED_BYTES_EXPORT, &mut exports);
        exports.extend_from_slice(&[0, 0]);
        section(7, &exports, &mut module);
        let opcode = if memory_as_function { 0x42 } else { 0x41 };
        section(10, &[1, 4, 0, opcode, 0, 0x0b], &mut module);
        module
    }

    fn infinite_loop_module() -> Vec<u8> {
        let mut module = b"\0asm\x01\0\0\0".to_vec();
        section(1, &[1, 0x60, 0, 1, 0x7e], &mut module);
        section(3, &[1, 0], &mut module);
        section(5, &[1, 1, 1, 1], &mut module);
        let mut exports = vec![2];
        name(CORE_WASM_MEMORY_EXPORT, &mut exports);
        exports.extend_from_slice(&[2, 0]);
        name(CORE_WASM_OWNED_BYTES_EXPORT, &mut exports);
        exports.extend_from_slice(&[0, 0]);
        section(7, &exports, &mut module);
        // locals=0; loop {}; br 0; end; i64.const 0; end
        section(
            10,
            &[1, 9, 0, 0x03, 0x40, 0x0c, 0, 0x0b, 0x42, 0, 0x0b],
            &mut module,
        );
        module
    }

    fn descriptor(pointer: u32, length: u32) -> Descriptor {
        Descriptor::Value((u64::from(length) << 32) | u64::from(pointer))
    }

    #[test]
    fn rejects_oversized_component_before_compilation() {
        let limits = WasmtimeComponentLimits {
            component_bytes: 8,
            ..WasmtimeComponentLimits::default()
        };
        let runtime = WasmtimeComponentRuntime::new(limits).expect("configure Wasmtime");
        assert!(matches!(
            runtime.component(&[0; 9]),
            Err(WasmtimeRuntimeError::ComponentTooLarge {
                size: 9,
                maximum: 8
            })
        ));
    }

    #[test]
    fn core_wasm_returns_only_a_copied_checked_range() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        let bytes = b"untrusted recipe";
        let length = u32::try_from(bytes.len()).expect("small test byte string");
        let module = byte_module(bytes, descriptor(32, length), false);
        assert_eq!(runtime.execute(&module).unwrap(), bytes);
    }

    #[test]
    fn core_wasm_rejects_oversized_module_before_compilation() {
        let module = byte_module(&[], descriptor(0, 0), false);
        let limits = CoreWasmOwnedBytesLimits {
            module_bytes: module.len() - 1,
            ..CoreWasmOwnedBytesLimits::default()
        };
        let runtime = CoreWasmOwnedBytesRuntime::new(limits).unwrap();
        assert!(matches!(
            runtime.execute(&module),
            Err(CoreWasmOwnedBytesError::ModuleTooLarge {
                size,
                maximum
            }) if size == module.len() && maximum == module.len() - 1
        ));
    }

    #[test]
    fn core_wasm_rejects_imports_before_instantiation() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        let module = byte_module(&[], descriptor(0, 0), true);
        assert!(matches!(
            runtime.execute(&module),
            Err(CoreWasmOwnedBytesError::ImportNotAllowed { .. })
        ));
    }

    #[test]
    fn core_wasm_reports_traps() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        let module = byte_module(&[], Descriptor::Trap, false);
        assert!(matches!(
            runtime.execute(&module),
            Err(CoreWasmOwnedBytesError::Guest(_))
        ));
    }

    #[test]
    fn core_wasm_rejects_bad_pointer_and_length() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        for module in [
            byte_module(&[], descriptor(u32::MAX, 1), false),
            byte_module(&[], descriptor(65_535, 2), false),
        ] {
            assert!(matches!(
                runtime.execute(&module),
                Err(CoreWasmOwnedBytesError::OutputOutOfBounds { .. })
            ));
        }
    }

    #[test]
    fn core_wasm_rejects_oversized_claim_before_memory_access() {
        let limits = CoreWasmOwnedBytesLimits {
            output_bytes: 8,
            ..CoreWasmOwnedBytesLimits::default()
        };
        let runtime = CoreWasmOwnedBytesRuntime::new(limits).unwrap();
        let module = byte_module(&[], descriptor(u32::MAX, 9), false);
        assert!(matches!(
            runtime.execute(&module),
            Err(CoreWasmOwnedBytesError::OutputTooLarge {
                size: 9,
                maximum: 8
            })
        ));
    }

    #[test]
    fn core_wasm_hard_output_ceiling_cannot_be_configured_away() {
        let limits = CoreWasmOwnedBytesLimits {
            output_bytes: MAX_CORE_WASM_OWNED_BYTES + 1,
            ..CoreWasmOwnedBytesLimits::default()
        };
        assert!(matches!(
            CoreWasmOwnedBytesRuntime::new(limits),
            Err(CoreWasmOwnedBytesError::OutputLimitTooLarge { .. })
        ));
    }

    #[test]
    fn core_wasm_limiter_rejects_oversized_initial_memory_and_extra_memories() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        let too_large_initial = byte_module_with_memories(&[], descriptor(0, 0), false, 33, 1);
        let two_memories = byte_module_with_memories(&[], descriptor(0, 0), false, 1, 2);
        for module in [too_large_initial, two_memories] {
            assert!(matches!(
                runtime.execute(&module),
                Err(CoreWasmOwnedBytesError::Instantiate(_))
            ));
        }
    }

    #[test]
    fn core_wasm_rejects_shared_memory_before_instantiation() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        assert!(matches!(
            runtime.execute(&shared_memory_module()),
            Err(CoreWasmOwnedBytesError::Module(_))
        ));
    }

    #[test]
    fn core_wasm_memory_grow_denial_returns_minus_one_and_guest_can_continue() {
        let limits = CoreWasmOwnedBytesLimits {
            memory_bytes: 64 * 1024,
            ..CoreWasmOwnedBytesLimits::default()
        };
        let runtime = CoreWasmOwnedBytesRuntime::new(limits).unwrap();
        assert_eq!(runtime.execute(&memory_grow_denial_module()).unwrap(), []);
    }

    #[test]
    fn core_wasm_limiter_rejects_extra_tables_and_table_elements() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        let two_tables = byte_module_with_resources(&[], descriptor(0, 0), false, 1, 1, 2, 1);
        let oversized_table = byte_module_with_resources(&[], descriptor(0, 0), false, 1, 1, 1, 2);
        for module in [two_tables, oversized_table] {
            assert!(matches!(
                runtime.execute(&module),
                Err(CoreWasmOwnedBytesError::Instantiate(_))
            ));
        }
    }

    #[test]
    fn core_wasm_rejects_wrong_memory_and_descriptor_export_types() {
        let runtime = CoreWasmOwnedBytesRuntime::new(CoreWasmOwnedBytesLimits::default()).unwrap();
        assert!(matches!(
            runtime.execute(&wrong_export_module(true)),
            Err(CoreWasmOwnedBytesError::MissingMemory)
        ));
        assert!(matches!(
            runtime.execute(&wrong_export_module(false)),
            Err(CoreWasmOwnedBytesError::OwnedBytesExport(_))
        ));
    }

    #[test]
    fn core_wasm_positive_fuel_stops_an_infinite_loop() {
        let limits = CoreWasmOwnedBytesLimits {
            fuel: 100,
            ..CoreWasmOwnedBytesLimits::default()
        };
        let runtime = CoreWasmOwnedBytesRuntime::new(limits).unwrap();
        assert!(matches!(
            runtime.execute(&infinite_loop_module()),
            Err(CoreWasmOwnedBytesError::Guest(_))
        ));
    }
}
