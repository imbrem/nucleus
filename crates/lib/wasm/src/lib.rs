//! Shared WebAssembly runtime dependencies.
//!
//! Covalence crates select the runtime appropriate to their boundary rather
//! than pinning versions independently:
//!
//! - `component-host` exposes Wasmtime and its minimal WASI Preview 2 host;
//! - `component-guest` exposes the canonical-ABI runtime used by generated WIT
//!   bindings;
//! - `browser` exposes `wasm-bindgen` on `wasm32-unknown-unknown`.
//!
//! This crate supplies versions and paths, not a common abstraction over the
//! three runtimes. They implement different sides of the WebAssembly boundary.

#[cfg(all(feature = "browser", target_arch = "wasm32", target_os = "unknown"))]
pub use wasm_bindgen;

#[cfg(feature = "component-guest")]
pub use wit_bindgen_rt;

#[cfg(all(feature = "component-host", not(target_arch = "wasm32")))]
pub use wasmtime;

#[cfg(all(feature = "component-host", not(target_arch = "wasm32")))]
pub use wasmtime_wasi;
