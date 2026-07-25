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

/// The v0 `SQLite` `INTEGER` 0/1 representation of `Bool`.
///
/// BLAKE3 of `covalence.representation/sqlite-integer-bool-01/v0`.
pub const INTEGER_BOOL_01_REPR_V0: O256 = O256::from_bytes([
    0x81, 0xe1, 0xc9, 0xb6, 0x79, 0xed, 0xd3, 0x1e, 0xae, 0xe3, 0x8e, 0xb4, 0x6b, 0x37, 0xad, 0xab,
    0x68, 0x8f, 0xc0, 0xb7, 0x14, 0xbd, 0x91, 0x23, 0x29, 0x32, 0xc2, 0x2a, 0x27, 0x21, 0x51, 0xe3,
]);

/// The v0 logical relation containing `Bool` values.
///
/// BLAKE3 of `covalence.relation/bool-values/v0`.
pub const BOOL_VALUES_RELATION_V0: O256 = O256::from_bytes([
    0x57, 0xfc, 0xea, 0xf1, 0x28, 0xfa, 0x5f, 0xae, 0xf0, 0x8e, 0xe0, 0xa8, 0x54, 0x5c, 0xba, 0x46,
    0x6e, 0x2e, 0x48, 0xe1, 0x47, 0xa4, 0x3c, 0xe6, 0xc7, 0xab, 0x08, 0x78, 0x05, 0x0d, 0xd4, 0xd9,
]);

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
