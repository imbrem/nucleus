use covalence_lib_hash::O256;

/// Exact prefix reserved for Covalence metatables.
pub const META_PREFIX: &str = "covalence_meta_";

/// The permanent bootstrap-catalog metatable kind.
///
/// BLAKE3 of `covalence.meta/bootstrap-catalog`.
///
/// This O256 and its physical table format are the bootstrap ABI. They are
/// intentionally unversioned: future metadata is introduced through tables
/// typed by this catalog, not by replacing the bootstrap.
pub const BOOTSTRAP_CATALOG: O256 = O256::from_bytes([
    0x56, 0x20, 0x3f, 0x30, 0x1f, 0x01, 0xd2, 0xc5, 0x25, 0xcc, 0xfa, 0x9b, 0x47, 0xd3, 0x64, 0x95,
    0x96, 0x5d, 0xda, 0x82, 0xf2, 0x86, 0x92, 0xa0, 0xea, 0x5b, 0x3e, 0xb1, 0x39, 0x37, 0xf3, 0x01,
]);

/// The v0 `Bool` substrate sort.
///
/// BLAKE3 of `covalence.sort/bool/v0`.
pub const BOOL_SORT_V0: O256 = O256::from_bytes([
    0x84, 0xfd, 0xdb, 0x85, 0xd8, 0x32, 0x37, 0x2a, 0x4a, 0x4a, 0xa7, 0x22, 0xec, 0x8c, 0x80, 0xdd,
    0x07, 0x25, 0x06, 0x63, 0x9c, 0x8f, 0x45, 0x72, 0x73, 0x73, 0xa6, 0x37, 0x0e, 0xbe, 0x53, 0x54,
]);

/// The first extension metatable: process-local Rust type names and IDs.
///
/// BLAKE3 of `covalence.meta/rust-types/v0`.
pub const RUST_TYPES_METATABLE_V0: O256 = O256::from_bytes([
    0x55, 0x21, 0xf3, 0xc7, 0xda, 0x37, 0x98, 0x60, 0xd7, 0xca, 0xb8, 0xc5, 0x1e, 0x99, 0x14, 0x49,
    0x4d, 0xd7, 0x3f, 0xc8, 0xdc, 0x26, 0xf4, 0xab, 0x3e, 0xfc, 0x80, 0x3b, 0x14, 0xaa, 0x9c, 0x2f,
]);

/// Text stored in the bootstrap catalog for the Rust-type registry.
pub const RUST_TYPES_INTERPRETATION_V0: &str = "covalence.meta.rust-types/v0";

/// Expressions stored as checked textual S-expressions.
pub const EXPRESSIONS_METATABLE_V0: O256 = O256::from_bytes([
    0x27, 0x57, 0x73, 0xd8, 0x93, 0x96, 0x5c, 0x30, 0x5c, 0x29, 0xef, 0x6d, 0x50, 0xf8, 0x1d, 0x5e,
    0x3c, 0xb6, 0x22, 0x90, 0x94, 0xf1, 0xee, 0x69, 0xbf, 0x45, 0x72, 0xf2, 0xf2, 0x2a, 0x41, 0x9d,
]);

/// Compiled interpretation selected for the expression registry.
pub const EXPRESSIONS_INTERPRETATION_V0: &str = "covalence.meta.expressions/v0";

/// Executors registered for connection-local execution.
pub const EXECUTORS_METATABLE_V0: O256 = O256::from_bytes([
    0x93, 0x9f, 0x9d, 0x4c, 0x64, 0xa2, 0xab, 0x27, 0x85, 0xbc, 0xaa, 0xf1, 0xf3, 0x9f, 0x87, 0x4e,
    0xb7, 0xa6, 0x99, 0x5a, 0x8e, 0x5e, 0x06, 0xed, 0xba, 0x9b, 0x34, 0xd4, 0x6b, 0xaf, 0xf9, 0x07,
]);

/// Compiled interpretation selected for the executor registry.
pub const EXECUTORS_INTERPRETATION_V0: &str = "covalence.meta.executors/v0";

/// Expressions which interpret ordinary tables.
pub const TABLE_INTERPRETATIONS_METATABLE_V0: O256 = O256::from_bytes([
    0xe5, 0x98, 0x4f, 0x43, 0x09, 0xcf, 0x2f, 0x11, 0x3f, 0x68, 0x45, 0xed, 0x83, 0xad, 0x6f, 0xe9,
    0xcf, 0x86, 0xad, 0x8f, 0x86, 0x5c, 0xc3, 0xa6, 0x20, 0x4d, 0x67, 0xd6, 0x68, 0x60, 0x44, 0x41,
]);

/// Compiled interpretation selected for table interpretations.
pub const TABLE_INTERPRETATIONS_INTERPRETATION_V0: &str = "covalence.meta.table-interpretations/v0";

/// Connection-local execution trace records.
pub const EXECUTION_TRACES_METATABLE_V0: O256 = O256::from_bytes([
    0xc9, 0xe1, 0x97, 0x68, 0x12, 0x6c, 0x1c, 0xee, 0xcd, 0x81, 0x80, 0x3c, 0x8b, 0x83, 0x68, 0x06,
    0xd6, 0xde, 0xb3, 0xe8, 0x30, 0x35, 0x57, 0x32, 0x9f, 0x95, 0x80, 0xfe, 0xa2, 0x7c, 0xeb, 0xb3,
]);

/// Compiled interpretation selected for execution traces.
pub const EXECUTION_TRACES_INTERPRETATION_V0: &str = "covalence.meta.execution-traces/v0";

/// A stable identifier for one metatable format and version.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MetatableKind(O256);

impl MetatableKind {
    /// Constructs a kind from its stable identifier.
    #[must_use]
    pub const fn new(id: O256) -> Self {
        Self(id)
    }

    /// Returns the stable identifier.
    #[must_use]
    pub const fn id(self) -> O256 {
        self.0
    }
}

/// Formats the physical `SQLite` identifier for a metatable kind.
#[must_use]
pub fn metatable_name(kind: MetatableKind) -> String {
    format!("{META_PREFIX}{}", kind.id())
}

/// Parses a well-formed reserved metatable name.
///
/// Returns `None` for names outside the reserved namespace or for malformed
/// names inside it. Callers that need to distinguish those cases should first
/// check [`META_PREFIX`].
#[must_use]
pub fn parse_metatable_name(name: &str) -> Option<MetatableKind> {
    let suffix = name.strip_prefix(META_PREFIX)?;
    if suffix.len() != 64
        || !suffix
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    O256::from_hex(suffix).ok().map(MetatableKind)
}

#[cfg(test)]
mod tests {
    use super::{
        BOOTSTRAP_CATALOG, META_PREFIX, MetatableKind, metatable_name, parse_metatable_name,
    };

    #[test]
    fn physical_name_round_trips() {
        let kind = MetatableKind::new(BOOTSTRAP_CATALOG);
        let name = metatable_name(kind);
        assert!(name.starts_with("covalence_meta_"));
        assert!(!name.contains('.'));
        assert_eq!(parse_metatable_name(&name), Some(kind));
    }

    #[test]
    fn parser_is_exact_and_lowercase() {
        let name = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        assert_eq!(parse_metatable_name(&name.to_uppercase()), None);
        assert_eq!(parse_metatable_name(&format!("{name}0")), None);
        assert_eq!(parse_metatable_name(&name[..name.len() - 1]), None);
        assert_eq!(
            parse_metatable_name(&format!("{META_PREFIX}{}", "g".repeat(64))),
            None
        );
        assert_eq!(parse_metatable_name("ordinary"), None);
    }
}
