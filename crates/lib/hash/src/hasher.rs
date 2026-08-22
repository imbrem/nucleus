use std::hash::Hasher;

/// A table hasher which uses the first eight input bytes directly.
///
/// This is suitable for keys whose leading bytes are already uniformly
/// distributed, such as cryptographic object addresses. It is not a general
/// purpose hash function.
#[derive(Clone, Debug, Default)]
pub struct IdentityHasher {
    prefix: [u8; 8],
    length: usize,
}

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        u64::from_le_bytes(self.prefix)
    }

    fn write(&mut self, bytes: &[u8]) {
        let remaining = self.prefix.len().saturating_sub(self.length);
        let count = remaining.min(bytes.len());
        self.prefix[self.length..self.length + count].copy_from_slice(&bytes[..count]);
        self.length += count;
    }

    fn write_u32(&mut self, value: u32) {
        self.write(&value.to_le_bytes());
    }

    fn write_u64(&mut self, value: u64) {
        self.write(&value.to_le_bytes());
    }
}

/// A standard-library [`Hasher`] backed by unkeyed BLAKE3.
#[cfg(feature = "blake3")]
#[derive(Clone)]
pub struct Blake3Hasher(::blake3::Hasher);

#[cfg(feature = "blake3")]
impl Default for Blake3Hasher {
    fn default() -> Self {
        Self(::blake3::Hasher::new())
    }
}

#[cfg(feature = "blake3")]
impl Hasher for Blake3Hasher {
    fn finish(&self) -> u64 {
        let digest = self.0.finalize();
        u64::from_le_bytes(
            digest.as_bytes()[..8]
                .try_into()
                .expect("BLAKE3 is 32 bytes"),
        )
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }
}

/// A standard-library [`Hasher`] backed by SHA-256.
#[cfg(feature = "sha256")]
#[derive(Clone, Default)]
pub struct Sha256Hasher(sha2::Sha256);

#[cfg(feature = "sha256")]
impl Hasher for Sha256Hasher {
    fn finish(&self) -> u64 {
        use sha2::Digest;

        let digest = self.0.clone().finalize();
        u64::from_le_bytes(digest[..8].try_into().expect("SHA-256 is 32 bytes"))
    }

    fn write(&mut self, bytes: &[u8]) {
        use sha2::Digest;

        self.0.update(bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identity_hasher_uses_the_first_eight_bytes() {
        let mut hasher = IdentityHasher::default();
        hasher.write(&[1, 2, 3]);
        hasher.write(&[4, 5, 6, 7, 8, 9]);
        assert_eq!(
            hasher.finish(),
            u64::from_le_bytes([1, 2, 3, 4, 5, 6, 7, 8])
        );

        let mut hasher = IdentityHasher::default();
        hasher.write_u64(0x0807_0605_0403_0201);
        assert_eq!(hasher.finish(), 0x0807_0605_0403_0201);
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn blake3_hasher_matches_the_address_prefix() {
        let mut hasher = Blake3Hasher::default();
        hasher.write(b"abc");
        assert_eq!(
            hasher.finish(),
            crate::Blake3Hash::from_bytes(b"abc").addr64()
        );
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn sha256_hasher_matches_the_address_prefix() {
        let mut hasher = Sha256Hasher::default();
        hasher.write(b"abc");
        assert_eq!(
            hasher.finish(),
            crate::Sha256Hash::from_bytes(b"abc").addr64()
        );
    }
}
