//! Fixed-width hash values and optional hashing primitives.
//!
//! Values own their raw bytes independently of their textual encoding.
//! [`O256::hex`] and [`O256::from_hex`] provide an explicit hexadecimal
//! boundary; other encodings and structured hash envelopes can be added
//! without changing the value representation.

use std::fmt;
use std::str::FromStr;

use covalence_lib_error::snafu;
use snafu::Snafu;

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

fn parse_hex<const N: usize>(input: &str) -> Result<[u8; N], ParseHexError> {
    let expected = N * 2;
    if input.len() != expected {
        return Err(ParseHexError::InvalidLength {
            expected,
            actual: input.len(),
        });
    }

    let input = input.as_bytes();
    let mut output = [0; N];
    for (index, pair) in input.chunks_exact(2).enumerate() {
        let high =
            decode_nibble(pair[0]).ok_or(ParseHexError::InvalidDigit { index: index * 2 })?;
        let low = decode_nibble(pair[1]).ok_or(ParseHexError::InvalidDigit {
            index: index * 2 + 1,
        })?;
        output[index] = high << 4 | low;
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

macro_rules! fixed_value {
    ($name:ident, $width:literal, $description:literal) => {
        #[doc = $description]
        #[repr(transparent)]
        #[derive(Clone, Copy, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name([u8; $width]);

        impl $name {
            /// Constructs a value from its exact byte representation.
            #[must_use]
            pub const fn from_bytes(bytes: [u8; $width]) -> Self {
                Self(bytes)
            }

            /// Borrows the exact byte representation.
            #[must_use]
            pub const fn as_bytes(&self) -> &[u8; $width] {
                &self.0
            }

            /// Returns the exact byte representation.
            #[must_use]
            pub const fn into_bytes(self) -> [u8; $width] {
                self.0
            }

            /// Decodes an exact-width hexadecimal representation.
            ///
            /// Both lowercase and uppercase digits are accepted. Prefixes,
            /// whitespace, separators, and variable-width input are rejected.
            ///
            /// # Errors
            ///
            /// Returns an error when the input has the wrong width or contains
            /// a non-hexadecimal digit.
            pub fn from_hex(input: &str) -> Result<Self, ParseHexError> {
                parse_hex(input).map(Self)
            }

            /// Returns a zero-allocation lowercase hexadecimal view.
            #[must_use]
            pub const fn hex(&self) -> Hex<'_> {
                Hex(&self.0)
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.hex().fmt(formatter)
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "{}({self})", stringify!($name))
            }
        }

        impl FromStr for $name {
            type Err = ParseHexError;

            fn from_str(input: &str) -> Result<Self, Self::Err> {
                Self::from_hex(input)
            }
        }

        impl From<[u8; $width]> for $name {
            fn from(bytes: [u8; $width]) -> Self {
                Self::from_bytes(bytes)
            }
        }

        impl From<$name> for [u8; $width] {
            fn from(value: $name) -> Self {
                value.into_bytes()
            }
        }
    };
}

fixed_value!(O256, 32, "An opaque owned 256-bit value.");
fixed_value!(GitHash, 20, "A traditional 160-bit Git SHA-1 object name.");

impl O256 {
    /// Computes the BLAKE3 digest of `bytes`.
    #[must_use]
    pub fn blake3(bytes: impl AsRef<[u8]>) -> Self {
        Self::from_bytes(*::blake3::hash(bytes.as_ref()).as_bytes())
    }

    /// Computes the BLAKE3 digest of bytes read from `reader`.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn blake3_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Self> {
        let mut hasher = ::blake3::Hasher::new();
        std::io::copy(&mut reader, &mut hasher)?;
        Ok(Self::from_bytes(*hasher.finalize().as_bytes()))
    }
}

impl O256 {
    /// Computes the SHA-256 digest of `bytes`.
    #[must_use]
    pub fn sha256(bytes: impl AsRef<[u8]>) -> Self {
        use sha2::Digest;
        Self::from_bytes(sha2::Sha256::digest(bytes.as_ref()).into())
    }

    /// Computes the SHA-256 digest of bytes read from `reader`.
    ///
    /// # Errors
    ///
    /// Returns an error if reading from `reader` fails.
    pub fn sha256_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Self> {
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
        Ok(Self::from_bytes(hasher.finalize().into()))
    }
}

/// Computes the raw SHA-1 digest of `bytes`.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_raw_sha1(bytes: impl AsRef<[u8]>) -> GitHash {
    use sha1::Digest;
    GitHash::from_bytes(sha1::Sha1::digest(bytes.as_ref()).into())
}

/// Computes a Git SHA-1 object name using `object_type` framing.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_object_sha1(object_type: &str, bytes: impl AsRef<[u8]>) -> GitHash {
    use sha1::Digest;

    let bytes = bytes.as_ref();
    let mut hasher = sha1::Sha1::new();
    hasher.update(object_type.as_bytes());
    hasher.update(b" ");
    hasher.update(bytes.len().to_string().as_bytes());
    hasher.update(b"\0");
    hasher.update(bytes);
    GitHash::from_bytes(hasher.finalize().into())
}

/// Computes a Git blob SHA-1 object name.
#[cfg(feature = "git-sha1")]
#[must_use]
pub fn git_blob_sha1(bytes: impl AsRef<[u8]>) -> GitHash {
    git_object_sha1("blob", bytes)
}

#[cfg(feature = "random")]
impl O256 {
    /// Constructs a random value using a caller-provided cryptographic RNG.
    pub fn random(
        rng: &mut (impl covalence_lib_rand::Rng + covalence_lib_rand::CryptoRng),
    ) -> Self {
        Self::from_bytes(rng.random())
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
        assert_eq!(format!("{o256:?}"), format!("O256({o256})"));
        assert_eq!(git.to_string(), "cd".repeat(20));
        assert_eq!(format!("{git:?}"), format!("GitHash({git})"));
        assert_eq!(o256.hex().to_string(), "ab".repeat(32));
        assert_eq!(O256::from_hex(&"ab".repeat(32)), Ok(o256));
        assert_eq!("ab".repeat(32).parse(), Ok(o256));
        assert_eq!("AB".repeat(32).parse(), Ok(o256));
        assert_eq!("cd".repeat(20).parse(), Ok(git));
        assert_eq!("CD".repeat(20).parse(), Ok(git));
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
        assert_ne!(git_blob_sha1(b"hello"), git_raw_sha1(b"hello"));
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
        assert_ne!(O256::random(&mut first), O256::default());
    }
}
