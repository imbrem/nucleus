#![no_std]
//! Untrusted, allocation-free encoder for the sealed HOL recipe wire format.
//!
//! This crate is deliberately above Nucleus: producing these bytes proves nothing. The
//! authoritative decoder and checked replay remain in `covalence-repl` and Nucleus.

/// Version of the canonical recipe encoding understood by this prototype SDK.
pub const RECIPE_VERSION: u8 = 6;

/// A fixed-capacity canonical recipe suitable for static guest memory.
pub struct EncodedRecipe<const CAPACITY: usize> {
    bytes: [u8; CAPACITY],
    len: usize,
}

impl<const CAPACITY: usize> EncodedRecipe<CAPACITY> {
    /// Returns the initialized recipe prefix.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.bytes.split_at(self.len).0
    }

    /// Returns the initialized recipe length.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns whether this recipe is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the start of the guest-owned fixed storage.
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        self.bytes.as_ptr()
    }
}

/// Allocation-free encoder. It is untrusted convenience code, not a validator.
pub struct RecipeEncoder<const CAPACITY: usize> {
    bytes: [u8; CAPACITY],
    len: usize,
    declared_nodes: u16,
    encoded_nodes: u16,
}

impl<const CAPACITY: usize> RecipeEncoder<CAPACITY> {
    /// Starts a recipe with its final node count and selected namespace index.
    #[must_use]
    pub const fn new(node_count: u16, selected_namespace: u16) -> Self {
        let encoder = Self {
            bytes: [0; CAPACITY],
            len: 0,
            declared_nodes: node_count,
            encoded_nodes: 0,
        };
        encoder
            .byte(RECIPE_VERSION)
            .u16(node_count)
            .u16(selected_namespace)
    }

    const fn byte(mut self, value: u8) -> Self {
        assert!(self.len < CAPACITY, "recipe encoder capacity exceeded");
        self.bytes[self.len] = value;
        self.len += 1;
        self
    }

    const fn bytes(mut self, values: &[u8]) -> Self {
        let mut index = 0;
        while index < values.len() {
            self = self.byte(values[index]);
            index += 1;
        }
        self
    }

    const fn u16(self, value: u16) -> Self {
        self.bytes(&value.to_be_bytes())
    }

    const fn u32(self, value: u32) -> Self {
        self.bytes(&value.to_be_bytes())
    }

    const fn i64(self, value: i64) -> Self {
        self.bytes(&value.to_be_bytes())
    }

    const fn node(mut self, tag: u8) -> Self {
        self.encoded_nodes = self
            .encoded_nodes
            .checked_add(1)
            .expect("recipe node count overflow");
        self.byte(tag)
    }

    /// Encodes the Boolean type node.
    #[must_use]
    pub const fn bool_type(self) -> Self {
        self.node(0)
    }

    /// Encodes a bound term.
    #[must_use]
    pub const fn bound(self, index: u32, ty: u16) -> Self {
        self.node(1).u32(index).u16(ty)
    }

    /// Encodes a lambda term.
    #[must_use]
    pub const fn lambda(self, parameter_type: u16, body: u16) -> Self {
        self.node(2).u16(parameter_type).u16(body)
    }

    /// Encodes a Boolean literal.
    #[must_use]
    pub const fn bool_term(self, value: bool) -> Self {
        self.node(3).byte(value as u8)
    }

    /// Encodes the empty context.
    #[must_use]
    pub const fn empty_context(self) -> Self {
        self.node(4)
    }

    /// Encodes beta conversion.
    #[must_use]
    pub const fn conversion_beta(self, abstraction: u16, argument: u16) -> Self {
        self.node(0x35).u16(abstraction).u16(argument)
    }

    /// Turns a conversion into an equality theorem in a context.
    #[must_use]
    pub const fn conversion_equality(self, context: u16, conversion: u16) -> Self {
        self.node(0x38).u16(context).u16(conversion)
    }

    /// Marks a theorem as kernel state to persist.
    #[must_use]
    pub const fn persist(self, theorem: u16) -> Self {
        self.node(6).u16(theorem)
    }

    /// Adds a namespace with an optional UTF-8 name.
    ///
    /// # Panics
    ///
    /// Panics if the name does not fit the canonical `u16` length or the encoder capacity.
    #[must_use]
    pub const fn namespace(self, name: Option<&str>) -> Self {
        let encoder = self.node(7);
        match name {
            None => encoder.byte(0),
            Some(name) => {
                let bytes = name.as_bytes();
                assert!(bytes.len() <= u16::MAX as usize, "recipe name is too long");
                #[allow(clippy::cast_possible_truncation)]
                let length = bytes.len() as u16;
                encoder.byte(1).u16(length).bytes(bytes)
            }
        }
    }

    /// Exports a context without an optional display name.
    #[must_use]
    pub const fn export_context(self, namespace: u16, export: i64, context: u16) -> Self {
        self.node(9).u16(namespace).i64(export).u16(context).byte(0)
    }

    /// Exports a theorem conclusion without an optional display name.
    #[must_use]
    pub const fn export_theorem(self, namespace: u16, export: i64, theorem: u16) -> Self {
        self.node(8).u16(namespace).i64(export).u16(theorem).byte(0)
    }

    /// Finishes the encoding, checking only the declared node count.
    ///
    /// # Panics
    ///
    /// Panics if the encoded node count differs from the count placed in the header.
    #[must_use]
    pub const fn finish(self) -> EncodedRecipe<CAPACITY> {
        assert!(
            self.encoded_nodes == self.declared_nodes,
            "declared recipe node count does not match encoding"
        );
        EncodedRecipe {
            bytes: self.bytes,
            len: self.len,
        }
    }
}

/// Canonical closed-beta demo recipe generated entirely in untrusted guest code.
pub static CLOSED_BETA_RECIPE: EncodedRecipe<128> = RecipeEncoder::new(11, 8)
    .bool_type()
    .bound(0, 0)
    .lambda(0, 1)
    .bool_term(true)
    .empty_context()
    .conversion_beta(2, 3)
    .conversion_equality(4, 5)
    .persist(6)
    .namespace(Some("demo"))
    .export_context(8, 0, 4)
    .export_theorem(8, 1, 6)
    .finish();

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closed_beta_is_stable_and_nonempty() {
        const EXPECTED_WIRE: &[u8] = &[
            6, 0, 11, 0, 8, // header
            0, // bool type
            1, 0, 0, 0, 0, 0, 0, // bound 0 : bool
            2, 0, 0, 0, 1, // lambda
            3, 1, // true
            4, // empty context
            0x35, 0, 2, 0, 3, // beta
            0x38, 0, 4, 0, 5, // conversion equality
            6, 0, 6, // persist
            7, 1, 0, 4, b'd', b'e', b'm', b'o', // namespace
            9, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, // context export
            8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, // theorem export
        ];
        assert_eq!(CLOSED_BETA_RECIPE.as_bytes(), EXPECTED_WIRE);
    }
}
