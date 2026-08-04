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
        /// Maximum number of elements in each core WebAssembly table.
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
    /// This layer deliberately knows nothing about any Nucleus protocol, WIT world,
    /// database, key, or signer. Protocol owners construct their linker and keep all
    /// semantic capabilities in `data`. The byte, fuel, and store limits do not bound native
    /// compilation CPU or memory: callers accepting hostile component bytes should pre-vet and
    /// cache them, or isolate compilation behind a separate process boundary.
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
        /// Returns an error if the byte bound is exceeded or compilation fails.
        pub fn component(&self, bytes: &[u8]) -> Result<Component, WasmtimeRuntimeError> {
            if bytes.len() > self.limits.component_bytes {
                return Err(WasmtimeRuntimeError::ComponentTooLarge {
                    size: bytes.len(),
                    maximum: self.limits.component_bytes,
                });
            }
            Component::from_binary(&self.engine, bytes).map_err(WasmtimeRuntimeError::Component)
        }

        /// Creates one isolated store with the configured hard limits and fuel.
        ///
        /// # Errors
        ///
        /// Returns an error if Wasmtime rejects the initial fuel budget.
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

    /// Store state separating protocol-owned data from runtime-mechanical limits.
    pub struct WasmtimeStore<T> {
        /// Protocol-owned host state.
        pub data: T,
        limits: StoreLimits,
    }

    /// Failure to configure a native Wasmtime component runtime.
    #[derive(Debug)]
    pub enum WasmtimeRuntimeError {
        /// Encoded component exceeds the configured pre-compilation bound.
        ComponentTooLarge {
            /// Supplied byte length.
            size: usize,
            /// Configured byte-length maximum.
            maximum: usize,
        },
        /// Wasmtime rejected the encoded component.
        Component(wasmtime::Error),
        /// Wasmtime rejected the engine configuration.
        Engine(wasmtime::Error),
        /// Wasmtime rejected the initial fuel budget.
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

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

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
}
