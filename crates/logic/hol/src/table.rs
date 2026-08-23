//! Immutable, content-addressed Ethane tables.

use std::{ops::Deref, sync::Arc};

use covalence_lib_hash::O256;
use covalence_logic_cas::CasFact;

use crate::{Arena, wire};

/// An immutable arena with the address of bytes that decode to it.
///
/// The private representation is an LCF boundary. Safe code can construct a
/// table only by decoding a checked whole-object CAS fact or by encoding and
/// hashing an arena. The source bytes do not need to remain resident.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Table {
    address: O256,
    arena: Arc<Arena>,
}

impl Table {
    /// Encodes and hashes an arena, then introduces the corresponding table.
    ///
    /// # Errors
    ///
    /// Returns an error if the arena cannot be encoded.
    pub fn from_arena(arena: Arena) -> Result<Self, wire::EncodeError> {
        let mut bytes = Vec::new();
        wire::serialize(&arena, &mut bytes)?;
        Ok(Self {
            address: O256::from_bytes(&bytes),
            arena: Arc::new(arena),
        })
    }

    /// Returns the address of bytes that decode to this arena.
    #[must_use]
    pub const fn addr(&self) -> O256 {
        self.address
    }

    /// Returns the shared immutable arena.
    #[must_use]
    pub fn arena(&self) -> &Arc<Arena> {
        &self.arena
    }
}

impl AsRef<Arena> for Table {
    fn as_ref(&self) -> &Arena {
        &self.arena
    }
}

impl Deref for Table {
    type Target = Arena;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl TryFrom<CasFact> for Table {
    type Error = wire::DecodeError;

    /// Decodes a checked whole-object fact and introduces a table.
    ///
    /// # Errors
    ///
    /// Returns an error unless the complete fact bytes encode an Ethane
    /// arena.
    fn try_from(fact: CasFact) -> Result<Self, Self::Error> {
        let address = fact.hash();
        let arena = Arc::new(wire::deserialize(fact.as_ref())?);
        Ok(Self { address, arena })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_bytes_introduce_the_corresponding_table() {
        let mut encoded = Vec::new();
        wire::serialize(&Arena::empty(), &mut encoded).unwrap();
        let bytes = CasFact::from_bytes(encoded);
        let address = bytes.hash();

        let table = Table::try_from(bytes).unwrap();
        assert_eq!(table.addr(), address);
        assert!(table.is_empty());
    }

    #[test]
    fn checked_non_arena_bytes_do_not_introduce_a_table() {
        let bytes = CasFact::from_bytes(&b"not an arena"[..]);
        assert!(Table::try_from(bytes).is_err());
    }

    #[test]
    fn raw_arenas_are_addressed_by_their_encoding() {
        let table = Table::from_arena(Arena::empty()).unwrap();
        let mut encoded = Vec::new();
        wire::serialize(&table, &mut encoded).unwrap();
        assert_eq!(table.addr(), O256::from_bytes(&encoded));
        assert_eq!(table.addr(), table.as_ref().addr());
    }
}
