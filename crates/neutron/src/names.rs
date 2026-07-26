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

/// The first hardcoded BLAKE3 content-addressed relation.
///
/// BLAKE3 of `covalence.meta/blake3-cas/v0`.
pub const BLAKE3_CAS_METATABLE_V0: O256 = O256::from_bytes([
    0x2a, 0x77, 0x45, 0xad, 0xb4, 0x82, 0xbf, 0x83, 0x93, 0xb6, 0x62, 0xfa, 0xcd, 0x5b, 0xd5, 0xd7,
    0x8c, 0xce, 0x28, 0x56, 0x1f, 0xcb, 0xc3, 0x49, 0xdc, 0x68, 0xf6, 0x67, 0xe5, 0xbe, 0x12, 0x43,
]);

/// Text stored in the bootstrap catalog for the hardcoded BLAKE3 CAS.
pub const BLAKE3_CAS_INTERPRETATION_V0: &str = "covalence.meta.blake3-cas/v0";

/// An indexed mutable key/value relation with a connection-local DEF identity.
///
/// BLAKE3 of `covalence.meta/indexed-kv/v0`.
pub const INDEXED_KV_METATABLE_V0: O256 = O256::from_bytes([
    0x2d, 0xb8, 0xd1, 0xf4, 0xdd, 0x61, 0x71, 0xee, 0x67, 0x37, 0x09, 0x39, 0x3c, 0x1d, 0x67, 0x92,
    0x04, 0x6b, 0xdf, 0xfe, 0xab, 0x5d, 0xd7, 0x42, 0x12, 0xb9, 0xaa, 0x0a, 0x84, 0x0e, 0x9e, 0x58,
]);

/// Text stored in the bootstrap catalog for indexed KV v0.
pub const INDEXED_KV_INTERPRETATION_V0: &str = "covalence.meta.indexed-kv/v0";

/// A direct mutable key/value relation stored without a separate row ID.
///
/// BLAKE3 of `covalence.meta/direct-kv/v0`.
pub const DIRECT_KV_METATABLE_V0: O256 = O256::from_bytes([
    0x71, 0xfc, 0x47, 0xae, 0x9b, 0x5b, 0x6e, 0x44, 0x23, 0x49, 0x37, 0x32, 0x8c, 0x30, 0x4b, 0x30,
    0x47, 0xc1, 0xcd, 0xac, 0x5b, 0x93, 0x24, 0x99, 0x5d, 0x37, 0xc3, 0xfa, 0x79, 0xb5, 0x6c, 0xae,
]);

/// Text stored in the bootstrap catalog for direct KV v0.
pub const DIRECT_KV_INTERPRETATION_V0: &str = "covalence.meta.direct-kv/v0";

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
