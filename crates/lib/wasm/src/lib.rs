//! Shared WebAssembly language and runtime dependencies.
//!
//! Covalence crates select the runtime appropriate to their boundary rather
//! than pinning versions independently:
//!
//! - `parser` exposes `wasmparser` for untrusted binary parsing and validation;
//! - `engine` exposes the core Wasmtime engine without selecting a WASI host;
//! - `component-host` exposes Wasmtime with native Component Model async and
//!   the WASI Preview 3 host;
//! - `component-guest` exposes the canonical-ABI runtime used by generated WIT
//!   bindings;
//! - `browser` exposes `wasm-bindgen` on `wasm32-unknown-unknown`.
//!
//! This crate supplies versions and dependency paths, not a common abstraction
//! over them. They implement different sides of the WebAssembly boundary.
//! Selecting a feature is also not a trust decision: checked logic decides
//! whether an executor's result is merely proposed evidence or is admitted by
//! an explicit acceleration capability.

#[cfg(all(feature = "browser", target_arch = "wasm32", target_os = "unknown"))]
pub use wasm_bindgen;

#[cfg(feature = "component-guest")]
pub use wit_bindgen_rt;

#[cfg(all(feature = "engine", not(target_arch = "wasm32")))]
pub use wasmtime;

#[cfg(all(feature = "component-host", not(target_arch = "wasm32")))]
pub use wasmtime_wasi;

#[cfg(feature = "parser")]
pub use wasmparser;
