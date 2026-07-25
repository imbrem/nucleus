//! Fixed-width hash values and optional hashing primitives.
//!
//! Values own their raw bytes independently of their textual encoding.
//! [`O256::hex`] and [`O256::from_hex`] provide explicit text boundaries
//! without changing the value representation.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::str::FromStr;

use covalence_lib_error::snafu;
use snafu::Snafu;

mod blake3;
mod git;

pub use blake3::Blake3;
pub use git::{GitHash, GitObject, Sha1};

#[cfg(feature = "git-sha1")]
pub use git::{git_blob_sha1, git_object_sha1, git_raw_sha1};

/// An error returned when decoding a fixed-width hexadecimal value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum ParseHexError {
    /// The input did not have the required number of hexadecimal digits.
    #[snafu(display("expected {expected} hexadecimal digits, found {actual}"))]
    InvalidLength {
        /// Required input length.
        expected: usize,
        /// Actual input length.
        actual: usize,
    },
    /// The input contained a byte which is not an ASCII hexadecimal digit.
    #[snafu(display("invalid hexadecimal digit at byte {index}"))]
    InvalidDigit {
        /// Byte offset of the invalid digit.
        index: usize,
    },
}

const fn decode_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

const fn parse_hex<const N: usize>(input: &str) -> Result<[u8; N], ParseHexError> {
    let expected = N * 2;
    if input.len() != expected {
        return Err(ParseHexError::InvalidLength {
            expected,
            actual: input.len(),
        });
    }

    let input = input.as_bytes();
    let mut output = [0; N];
    let mut index = 0;
    while index < N {
        let Some(high) = decode_nibble(input[index * 2]) else {
            return Err(ParseHexError::InvalidDigit { index: index * 2 });
        };
        let Some(low) = decode_nibble(input[index * 2 + 1]) else {
            return Err(ParseHexError::InvalidDigit {
                index: index * 2 + 1,
            });
        };
        output[index] = high << 4 | low;
        index += 1;
    }
    Ok(output)
}

/// A lowercase hexadecimal view of a fixed-width value.
#[derive(Clone, Copy, Debug)]
pub struct Hex<'a>(&'a [u8]);

impl fmt::Display for Hex<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(formatter, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// A compile-time namespace for fixed-width names.
///
/// Implementing this trait for one width fixes the valid representation width
/// for that namespace. A later hashing trait can build on this marker without
/// coupling byte names to hashing state or runtime configuration.
pub trait Namespace<const BYTES: usize> {}

/// No namespace claim is attached to the bytes.
pub enum Opaque {}

impl<const BYTES: usize> Namespace<BYTES> for Opaque {}

/// Bytes produced by SHA-256 hashing.
pub enum Sha256 {}

impl Namespace<32> for Sha256 {}

/// Bytes filled by a caller-provided cryptographic random number generator.
pub enum Random {}

impl Namespace<32> for Random {}

/// An owned fixed-width byte name in a compile-time namespace.
///
/// `BYTES` counts bytes, not bits. `Space` occupies no storage and is only a
/// type-safety aid: [`Obj::from_bytes`], [`Obj::from_hex`], and [`Obj::coerce`]
/// can attach any compatible namespace without validating how the bytes were
/// produced.
///
/// The function-pointer form of [`PhantomData`] makes the namespace non-owning.
#[repr(transparent)]
pub struct Obj<const BYTES: usize, Space: Namespace<BYTES> = Opaque> {
    bytes: [u8; BYTES],
    space: PhantomData<fn() -> Space>,
}

/// An opaque owned 256-bit value.
pub type O256 = Obj<32, Opaque>;

/// Constructs an [`O256`] from a hexadecimal string literal.
///
/// The literal is decoded during const evaluation, including when the macro is
/// used in runtime code. Invalid width or digits are compile errors.
///
/// ```
/// use covalence_lib_hash::{O256, o256};
///
/// const VALUE: O256 = o256!(
///     "abababababababababababababababababababababababababababababababab"
/// );
/// assert_eq!(VALUE.as_bytes(), &[0xab; 32]);
/// ```
///
/// ```compile_fail
/// use covalence_lib_hash::o256;
///
/// let _ = o256!("not a 256-bit hexadecimal value");
/// ```
#[macro_export]
macro_rules! o256 {
    ($hex:literal) => {{
        const VALUE: $crate::O256 = match $crate::O256::from_hex($hex) {
            Ok(value) => value,
            Err(_) => panic!("invalid O256 hexadecimal literal"),
        };
        VALUE
    }};
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Obj<BYTES, Space> {
    /// Constructs a namespaced value from its exact bytes without validation.
    #[must_use]
    pub const fn from_bytes(bytes: [u8; BYTES]) -> Self {
        Self {
            bytes,
            space: PhantomData,
        }
    }

    /// Borrows the exact byte representation.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; BYTES] {
        &self.bytes
    }

    /// Returns the exact byte representation.
    #[must_use]
    pub const fn into_bytes(self) -> [u8; BYTES] {
        self.bytes
    }

    /// Changes the compile-time provenance claim without changing the bytes.
    #[must_use]
    pub const fn coerce<NewSpace: Namespace<BYTES>>(self) -> Obj<BYTES, NewSpace> {
        Obj::from_bytes(self.bytes)
    }

    /// Erases the compile-time namespace claim without changing the bytes.
    #[must_use]
    pub const fn opaque(self) -> Obj<BYTES, Opaque> {
        Obj::from_bytes(self.bytes)
    }

    /// Decodes an exact-width hexadecimal representation without validating
    /// the namespace claim.
    ///
    /// Both lowercase and uppercase digits are accepted. Prefixes, whitespace,
    /// separators, and variable-width input are rejected.
    ///
    /// # Errors
    ///
    /// Returns an error when the input has the wrong width or contains a
    /// non-hexadecimal digit.
    pub const fn from_hex(input: &str) -> Result<Self, ParseHexError> {
        match parse_hex(input) {
            Ok(bytes) => Ok(Self::from_bytes(bytes)),
            Err(error) => Err(error),
        }
    }

    /// Returns a zero-allocation lowercase hexadecimal view.
    #[must_use]
    pub const fn hex(&self) -> Hex<'_> {
        Hex(&self.bytes)
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Copy for Obj<BYTES, Space> {}

impl<const BYTES: usize, Space: Namespace<BYTES>> Clone for Obj<BYTES, Space> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Default for Obj<BYTES, Space> {
    fn default() -> Self {
        Self::from_bytes([0; BYTES])
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> PartialEq for Obj<BYTES, Space> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Eq for Obj<BYTES, Space> {}

impl<const BYTES: usize, Space: Namespace<BYTES>> PartialOrd for Obj<BYTES, Space> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Ord for Obj<BYTES, Space> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes.cmp(&other.bytes)
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> Hash for Obj<BYTES, Space> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> fmt::Display for Obj<BYTES, Space> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.hex().fmt(formatter)
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> fmt::Debug for Obj<BYTES, Space> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "Obj<{BYTES}>({self})")
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> FromStr for Obj<BYTES, Space> {
    type Err = ParseHexError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Self::from_hex(input)
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> From<[u8; BYTES]> for Obj<BYTES, Space> {
    fn from(bytes: [u8; BYTES]) -> Self {
        Self::from_bytes(bytes)
    }
}

impl<const BYTES: usize, Space: Namespace<BYTES>> From<Obj<BYTES, Space>> for [u8; BYTES] {
    fn from(value: Obj<BYTES, Space>) -> Self {
        value.into_bytes()
    }
}

#[cfg(feature = "sha256")]
impl O256 {
    /// Computes the SHA-256 digest of `bytes`.
    #[must_use]
    pub fn sha256(bytes: impl AsRef<[u8]>) -> Obj<32, Sha256> {
        use sha2::Digest;
        O256::from_bytes(sha2::Sha256::digest(bytes.as_ref()).into()).coerce()
    }

    /// Computes the SHA-256 digest of bytes read from `reader`.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn sha256_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Obj<32, Sha256>> {
        use sha2::Digest;

        let mut hasher = sha2::Sha256::new();
        let mut buffer = [0; 8 * 1024];
        loop {
            let count = reader.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
        }
        Ok(O256::from_bytes(hasher.finalize().into()).coerce())
    }
}

#[cfg(feature = "random")]
impl O256 {
    /// Constructs a random value using a caller-provided cryptographic RNG.
    pub fn random(
        rng: &mut (impl covalence_lib_rand::Rng + covalence_lib_rand::CryptoRng),
    ) -> Obj<32, Random> {
        O256::from_bytes(rng.random()).coerce()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    use super::*;

    fn hash(value: impl Hash) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn fixed_value_byte_round_trips() {
        let o256_bytes = [0xa5; 32];
        let git_bytes = [0x5a; 20];
        assert_eq!(O256::from_bytes(o256_bytes).as_bytes(), &o256_bytes);
        assert_eq!(O256::from(o256_bytes).into_bytes(), o256_bytes);
        assert_eq!(GitHash::from_bytes(git_bytes).as_bytes(), &git_bytes);
        assert_eq!(<[u8; 20]>::from(GitHash::from(git_bytes)), git_bytes);
    }

    #[test]
    fn fixed_value_formatting_and_parsing() {
        let o256 = O256::from_bytes([0xab; 32]);
        let git = GitHash::from_bytes([0xcd; 20]);
        assert_eq!(o256.to_string(), "ab".repeat(32));
        assert_eq!(format!("{o256:?}"), format!("Obj<32>({o256})"));
        assert_eq!(git.to_string(), "cd".repeat(20));
        assert_eq!(format!("{git:?}"), format!("Obj<20>({git})"));
        assert_eq!(o256.hex().to_string(), "ab".repeat(32));
        assert_eq!(O256::from_hex(&"ab".repeat(32)), Ok(o256));
        assert_eq!("ab".repeat(32).parse(), Ok(o256));
        assert_eq!("AB".repeat(32).parse(), Ok(o256));
        assert_eq!("cd".repeat(20).parse(), Ok(git));
        assert_eq!("CD".repeat(20).parse(), Ok(git));
    }

    #[test]
    fn hexadecimal_parsing_and_o256_macro_are_const_capable() {
        const HEX: O256 = match O256::from_hex(
            "abababababababababababababababababababababababababababababababab",
        ) {
            Ok(value) => value,
            Err(_) => panic!("valid const hexadecimal"),
        };
        const MACRO: O256 =
            o256!("abababababababababababababababababababababababababababababababab");

        assert_eq!(HEX, O256::from_bytes([0xab; 32]));
        assert_eq!(MACRO, HEX);
    }

    #[test]
    fn fixed_value_parsing_is_strict() {
        for invalid in [
            "00".repeat(31),
            "00".repeat(33),
            format!("0x{}", "00".repeat(32)),
            format!(" {}", "00".repeat(32)),
            format!("{} ", "00".repeat(32)),
            format!("0_{}", "00".repeat(31)),
            format!("g0{}", "00".repeat(31)),
        ] {
            assert!(invalid.parse::<O256>().is_err(), "{invalid:?}");
        }

        assert!("00".repeat(19).parse::<GitHash>().is_err());
        assert!("00".repeat(21).parse::<GitHash>().is_err());
        assert_eq!(
            O256::from_hex("00"),
            Err(ParseHexError::InvalidLength {
                expected: 64,
                actual: 2,
            })
        );
        assert_eq!(
            O256::from_hex(&format!("{}g0", "00".repeat(31))),
            Err(ParseHexError::InvalidDigit { index: 62 })
        );
    }

    #[test]
    fn fixed_values_are_bytewise_ordered_and_hashed() {
        let low = O256::from_bytes([0; 32]);
        let mut high_bytes = [0; 32];
        high_bytes[31] = 1;
        let high = O256::from_bytes(high_bytes);
        assert!(low < high);
        assert_eq!(hash(low), hash(O256::from_bytes([0; 32])));
        assert_ne!(hash(low), hash(high));

        let low = GitHash::from_bytes([0; 20]);
        let mut high_bytes = [0; 20];
        high_bytes[19] = 1;
        let high = GitHash::from_bytes(high_bytes);
        assert!(low < high);
        assert_eq!(hash(low), hash(GitHash::from_bytes([0; 20])));
        assert_ne!(hash(low), hash(high));
    }

    #[test]
    fn fixed_value_defaults_are_zero() {
        assert_eq!(O256::default().into_bytes(), [0; 32]);
        assert_eq!(GitHash::default().into_bytes(), [0; 20]);
    }

    #[test]
    fn namespaces_are_zero_sized_claims_and_can_be_changed_explicitly() {
        enum ApplicationTag {}
        impl Namespace<7> for ApplicationTag {}

        let opaque = Obj::<7>::from_bytes([0xa5; 7]);
        let tagged: Obj<7, ApplicationTag> = opaque.coerce();
        let erased = tagged.opaque();
        assert_eq!(tagged.into_bytes(), [0xa5; 7]);
        assert_eq!(erased, opaque);
        assert_eq!(std::mem::size_of::<Obj<7, ApplicationTag>>(), 7);
        assert_eq!(std::mem::align_of::<Obj<7, ApplicationTag>>(), 1);
        assert_eq!(std::mem::size_of::<Obj<32, Blake3>>(), 32);
        assert_eq!(std::mem::size_of::<Obj<20, GitObject>>(), 20);
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn blake3_vectors_and_reader() {
        // Official BLAKE3 test vectors and: printf abc | b3sum
        assert_eq!(
            O256::blake3([]).to_string(),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
        let expected = "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85";
        assert_eq!(O256::blake3(b"abc").to_string(), expected);
        assert_eq!(Blake3::hash(b"abc").to_string(), expected);
        assert_eq!(
            O256::blake3_from_reader(std::io::Cursor::new(b"abc"))
                .unwrap()
                .to_string(),
            expected
        );
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn sha256_vectors_and_reader() {
        // FIPS 180-4 examples; reproducible with: printf abc | sha256sum
        assert_eq!(
            O256::sha256([]).to_string(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        assert_eq!(O256::sha256(b"abc").to_string(), expected);
        assert_eq!(
            O256::sha256_from_reader(std::io::Cursor::new(b"abc"))
                .unwrap()
                .to_string(),
            expected
        );
    }

    #[cfg(feature = "git-sha1")]
    #[test]
    fn git_sha1_vectors_and_framing() {
        // Reproducible with: printf hello | git hash-object --stdin
        assert_eq!(
            git_blob_sha1([]).to_string(),
            "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
        );
        assert_eq!(
            git_blob_sha1(b"hello").to_string(),
            "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0"
        );
        assert_ne!(
            git_blob_sha1(b"hello").as_bytes(),
            git_raw_sha1(b"hello").as_bytes()
        );
        assert_eq!(
            git_blob_sha1(b"hello").into_sha1().into_git_object(),
            git_blob_sha1(b"hello")
        );
        assert_ne!(
            git_object_sha1("blob", b"hello"),
            git_object_sha1("tree", b"hello")
        );
    }

    #[cfg(feature = "random")]
    #[test]
    fn random_is_deterministic_with_a_seeded_rng() {
        use covalence_lib_rand::SeedableRng;

        let mut first = covalence_lib_rand::rngs::StdRng::seed_from_u64(42);
        let mut second = covalence_lib_rand::rngs::StdRng::seed_from_u64(42);
        assert_eq!(O256::random(&mut first), O256::random(&mut second));
        assert_ne!(O256::random(&mut first), Obj::<32, Random>::default());
    }
}
