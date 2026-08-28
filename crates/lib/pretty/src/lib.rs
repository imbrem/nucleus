//! Width-aware document layout for Nucleus user surfaces.
//!
//! Reach for [`pretty`] when a userspace textual format needs stable grouping,
//! indentation, and width-sensitive line breaking. Semantic encoders and wire
//! formats should remain independent of presentation width.

pub use pretty;
pub use pretty::*;
