//! Fixed-width, namespaced object identifiers.
//!
//! [`Obj`] carries a compact identity together with its intended namespace;
//! the type records that construction but does not prove it. Versioned random
//! roots and collision-resistant child derivation let independently issued
//! hierarchies remain practically disjoint and be mounted without coordination.
//! Their common fixed-width representation lets systems exchange and compose
//! names while preserving the hierarchy that gives them meaning.

use std::{
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    str::FromStr,
};

use covalence_lib_error::snafu;
use snafu::Snafu;

pub mod blake3;
mod git;
#[cfg(feature = "multiformats")]
mod multiformats;
#[cfg(feature = "serde")]
mod serde;

pub use blake3::{
    Blake3, Blake3Hash, COV, COV_ROOT, Cov, CtxKey, CtxKeyNamespace, Sha256, Sha256Hash,
};
pub use git::{Git, GitHash, Sha1};
#[cfg(feature = "multiformats")]
pub use multiformats::{InvalidMultiformat, MultiformatNamespace};

#[cfg(feature = "git-sha1")]
pub use git::{git_blob, git_object, sha1};

mod sealed {
    pub trait Bytes {}

    impl<const N: usize> Bytes for [u8; N] {}
}

/// A fixed-width byte representation.
pub trait ByteArray:
    sealed::Bytes + AsRef<[u8]> + AsMut<[u8]> + Copy + Default + Eq + Ord + Hash + Send + Sync + 'static
{
    /// The representation length in bytes.
    const LEN: usize;
}

impl<const N: usize> ByteArray for [u8; N]
where
    [u8; N]: Default,
{
    const LEN: usize = N;
}

/// A semantic namespace for fixed-width object identifiers.
///
/// Implementations normally carry no data. The width is part of the namespace,
/// while the namespace value itself is only a compile-time claim.
pub trait Namespace {
    /// The representation length in bytes.
    const BYTES: usize;

    /// The representation length in bits.
    const BITS: usize = Self::BYTES * 8;

    /// The namespace's concrete fixed-width array representation.
    ///
    /// Implementations must define this as `[u8; Self::BYTES]`.
    type Bytes: ByteArray;

    /// The namespace used when erasing this semantic claim.
    type Opaque: Namespace<Bytes = Self::Bytes, Opaque = Self::Opaque>;
}

/// A namespace making no semantic claim about its bytes.
pub struct Opaque<const BYTES: usize>;

impl<const BYTES: usize> Namespace for Opaque<BYTES>
where
    [u8; BYTES]: ByteArray,
{
    const BYTES: usize = BYTES;
    type Bytes = [u8; BYTES];
    type Opaque = Self;
}

/// An owned fixed-width identifier in namespace `N`.
///
/// Raw construction and coercion do not validate the namespace claim. The
/// invariant marker permits branded namespaces later without changing layout.
///
/// ```compile_fail
/// use std::marker::PhantomData;
/// use covalence_lib_hash::{Namespace, Obj, Opaque};
///
/// struct Brand<'id>(PhantomData<&'id ()>);
/// impl<'id> Namespace for Brand<'id> {
///     const BYTES: usize = 1;
///     type Bytes = [u8; Self::BYTES];
///     type Opaque = Opaque<1>;
/// }
///
/// // An invariant brand cannot be shortened from `'static` to `'id`.
/// fn shorten<'id>(value: Obj<Brand<'static>>, _: &'id ()) -> Obj<Brand<'id>> {
///     value
/// }
/// ```
#[repr(transparent)]
pub struct Obj<N: Namespace> {
    bytes: N::Bytes,
    namespace: PhantomData<fn(N) -> N>,
}

/// The standard 256-bit Covalence object namespace.
///
/// With the default `serde` feature, values serialize as their 32 raw bytes.
pub type O256 = Obj<Cov>;

/// An opaque object with width `W`.
pub type OpaqueObj<const BYTES: usize> = Obj<Opaque<BYTES>>;

impl<N: Namespace> Obj<N> {
    /// Constructs an object from exact bytes without validating its namespace.
    #[must_use]
    pub const fn from_array(bytes: N::Bytes) -> Self {
        Self {
            bytes,
            namespace: PhantomData,
        }
    }

    /// Borrows the exact array representation.
    #[must_use]
    pub const fn as_bytes(&self) -> &N::Bytes {
        &self.bytes
    }

    /// Returns the exact array representation.
    #[must_use]
    pub const fn into_bytes(self) -> N::Bytes {
        self.bytes
    }

    /// Changes the namespace claim without changing the bytes.
    #[must_use]
    pub const fn coerce<M>(self) -> Obj<M>
    where
        M: Namespace<Bytes = N::Bytes>,
    {
        Obj::from_array(self.bytes)
    }

    /// Removes the namespace claim without changing the bytes.
    #[must_use]
    pub const fn opaque(self) -> Obj<N::Opaque> {
        Obj::from_array(self.bytes)
    }

    /// Decodes exact-width hexadecimal bytes without validating the namespace.
    ///
    /// # Errors
    ///
    /// Returns an error for the wrong width or a non-hexadecimal digit.
    pub const fn from_hex<const BYTES: usize>(input: &str) -> Result<Self, ParseHexError>
    where
        N: Namespace<Bytes = [u8; BYTES]>,
    {
        match parse_hex(input) {
            Ok(bytes) => Ok(Self::from_array(bytes)),
            Err(error) => Err(error),
        }
    }

    /// Decodes canonical padded standard Base64 without validating the
    /// namespace claim.
    ///
    /// # Errors
    ///
    /// Returns an error for the wrong width, invalid alphabet, misplaced
    /// padding, or non-canonical trailing bits.
    pub const fn from_base64<const BYTES: usize>(input: &str) -> Result<Self, ParseBase64Error>
    where
        N: Namespace<Bytes = [u8; BYTES]>,
    {
        match parse_base64(input) {
            Ok(bytes) => Ok(Self::from_array(bytes)),
            Err(error) => Err(error),
        }
    }

    /// Returns a zero-allocation lowercase hexadecimal view.
    #[must_use]
    pub fn hex(&self) -> Hex<'_> {
        Hex(self.as_ref())
    }
}

impl<N: TagNamespace> Obj<N> {
    /// Derives a child object by tagging `bytes` with this object.
    #[must_use]
    pub fn tag(&self, bytes: impl AsRef<[u8]>) -> Obj<N::Tag> {
        N::tag(self, bytes)
    }

    /// Derives a child object by tagging bytes read from `reader`.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    pub fn tag_from_reader(&self, reader: impl std::io::Read) -> std::io::Result<Obj<N::Tag>> {
        N::tag_from_reader(self, reader)
    }

    /// Draws one output-width value from a CSPRNG and tags it.
    #[cfg(feature = "random")]
    pub fn tag_random<R>(&self, rng: &mut R) -> Obj<N::Tag>
    where
        R: covalence_lib_rand::Rng + covalence_lib_rand::CryptoRng,
    {
        let mut bytes = <N::Tag as Namespace>::Bytes::default();
        rng.fill(bytes.as_mut());
        self.tag(bytes)
    }
}

impl<N: Namespace> AsRef<[u8]> for Obj<N> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<N: Namespace> Copy for Obj<N> {}
impl<N: Namespace> Clone for Obj<N> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<N: Namespace> Default for Obj<N> {
    fn default() -> Self {
        Self::from_array(Default::default())
    }
}
impl<N: Namespace> PartialEq for Obj<N> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}
impl<N: Namespace> Eq for Obj<N> {}
impl<N: Namespace> PartialOrd for Obj<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<N: Namespace> Ord for Obj<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes.cmp(&other.bytes)
    }
}
impl<N: Namespace> Hash for Obj<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}
impl<N: Namespace> fmt::Display for Obj<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.hex().fmt(formatter)
    }
}
impl<N: Namespace> fmt::Debug for Obj<N> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "Obj<{}>({self})", std::any::type_name::<N>())
    }
}
impl<N: Namespace> FromStr for Obj<N> {
    type Err = ParseHexError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let expected = N::Bytes::LEN.saturating_mul(2);
        if input.len() != expected {
            return Err(ParseHexError::InvalidLength {
                expected,
                actual: input.len(),
            });
        }
        let mut bytes = N::Bytes::default();
        for (index, pair) in input.as_bytes().chunks_exact(2).enumerate() {
            let high =
                decode_nibble(pair[0]).ok_or(ParseHexError::InvalidDigit { index: index * 2 })?;
            let low = decode_nibble(pair[1]).ok_or(ParseHexError::InvalidDigit {
                index: index * 2 + 1,
            })?;
            bytes.as_mut()[index] = high << 4 | low;
        }
        Ok(Self::from_array(bytes))
    }
}

/// A namespace constructible by hashing content.
pub trait HashNamespace: Namespace + Sized {
    /// Hashes in-memory bytes.
    fn hash(bytes: impl AsRef<[u8]>) -> Obj<Self>;

    /// Hashes bytes from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    fn hash_from_reader(reader: impl std::io::Read) -> std::io::Result<Obj<Self>>;
}

impl<N: HashNamespace> Obj<N> {
    /// Constructs an object by hashing in namespace `N`.
    #[must_use]
    pub fn from_bytes(bytes: impl AsRef<[u8]>) -> Self {
        N::hash(bytes)
    }

    /// Constructs an object by hashing bytes from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    pub fn from_reader(reader: impl std::io::Read) -> std::io::Result<Self> {
        N::hash_from_reader(reader)
    }
}

/// A namespace constructible by hashing content with a key of type `K`.
pub trait KeyedNamespace<K: ?Sized>: Namespace + Sized {
    /// Hashes in-memory bytes with `key`.
    fn keyed(key: &K, bytes: impl AsRef<[u8]>) -> Obj<Self>;

    /// Hashes bytes from a reader with `key`.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    fn keyed_from_reader(key: &K, reader: impl std::io::Read) -> std::io::Result<Obj<Self>>;
}

impl<N: Namespace> Obj<N> {
    /// Constructs an object by keyed hashing in namespace `N`.
    #[must_use]
    pub fn with_key<K: ?Sized>(key: &K, bytes: impl AsRef<[u8]>) -> Self
    where
        N: KeyedNamespace<K>,
    {
        N::keyed(key, bytes)
    }

    /// Constructs an object by keyed hashing bytes from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    pub fn with_key_from_reader<K: ?Sized>(
        key: &K,
        reader: impl std::io::Read,
    ) -> std::io::Result<Self>
    where
        N: KeyedNamespace<K>,
    {
        N::keyed_from_reader(key, reader)
    }
}

/// A namespace constructible directly from a CSPRNG.
#[cfg(feature = "random")]
pub trait RandomNamespace: Namespace + Sized {
    /// Draws exactly one object-width value from `rng`.
    fn random<R>(rng: &mut R) -> Obj<Self>
    where
        R: covalence_lib_rand::Rng + covalence_lib_rand::CryptoRng,
    {
        let mut bytes = Self::Bytes::default();
        rng.fill(bytes.as_mut());
        Obj::from_array(bytes)
    }
}

/// A namespace whose objects can key child tags.
pub trait TagNamespace: Namespace + Sized {
    /// Namespace of tagged children.
    type Tag: Namespace;

    /// Tags in-memory bytes.
    fn tag(key: &Obj<Self>, bytes: impl AsRef<[u8]>) -> Obj<Self::Tag>;

    /// Tags bytes from a reader.
    ///
    /// # Errors
    ///
    /// Returns an error if reading fails.
    fn tag_from_reader(
        key: &Obj<Self>,
        reader: impl std::io::Read,
    ) -> std::io::Result<Obj<Self::Tag>>;
}

/// A namespace anchored by a stable root context.
pub trait RootedNamespace: Namespace + Sized {
    /// Namespace containing the root context key.
    type Context: Namespace;

    /// Random opaque identity embedded in the root context string.
    const OPAQUE_ROOT: Obj<Self::Opaque>;

    /// Human-readable, versioned BLAKE3 derive-key context.
    const ROOT_CTX_KEY: &'static str;

    /// Precomputed context key derived from [`Self::ROOT_CTX_KEY`].
    const ROOT_CTX: Obj<Self::Context>;

    /// Empty-string root object under [`Self::ROOT_CTX`].
    const ROOT: Obj<Self>;
}

/// A namespace supporting range verification with evidence of type `E`.
pub trait RangeProofNamespace<E>: Namespace + Sized {
    /// Verification failure.
    type Error;

    /// Verifies `data` against `evidence` and an expected root.
    ///
    /// The returned absolute range is the portion of the original object
    /// authenticated by the proof.
    ///
    /// # Errors
    ///
    /// Returns the namespace implementation's error when the evidence, data,
    /// or reconstructed root is invalid.
    fn verify_range(
        root: &Obj<Self>,
        evidence: E,
        data: &[u8],
    ) -> Result<std::ops::Range<u64>, Self::Error>;
}

impl<N: Namespace> Obj<N> {
    /// Verifies a byte range against this expected root.
    ///
    /// # Errors
    ///
    /// Returns the namespace implementation's error when verification fails.
    pub fn verify_range<E>(
        &self,
        evidence: E,
        data: &[u8],
    ) -> Result<std::ops::Range<u64>, <N as RangeProofNamespace<E>>::Error>
    where
        N: RangeProofNamespace<E>,
    {
        N::verify_range(self, evidence, data)
    }
}

/// A lowercase hexadecimal view.
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

/// An error decoding fixed-width hexadecimal text.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
pub enum ParseHexError {
    /// The input had the wrong number of hexadecimal digits.
    #[snafu(display("expected {expected} hexadecimal digits, found {actual}"))]
    InvalidLength { expected: usize, actual: usize },
    /// A byte was not an ASCII hexadecimal digit.
    #[snafu(display("invalid hexadecimal digit at byte {index}"))]
    InvalidDigit { index: usize },
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
    let expected = N.saturating_mul(2);
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

mod base64_error {
    use super::{Snafu, snafu};

    #[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
    #[snafu(crate_root(snafu))]
    pub enum Error {
        /// The encoded input had the wrong width.
        #[snafu(display("expected {expected} Base64 bytes, found {actual}"))]
        InvalidLength { expected: usize, actual: usize },
        /// A byte was outside the standard Base64 alphabet.
        #[snafu(display("invalid Base64 byte at offset {index}"))]
        InvalidByte { index: usize },
        /// Padding was absent or outside its canonical final position.
        #[snafu(display("invalid Base64 padding at offset {index}"))]
        InvalidPadding { index: usize },
        /// Unused bits in the final quantum were non-zero.
        #[snafu(display("non-canonical Base64 trailing bits at offset {index}"))]
        NonCanonical { index: usize },
    }
}

/// An error decoding canonical padded standard Base64.
pub use base64_error::Error as ParseBase64Error;

const fn base64_length(bytes: usize) -> usize {
    bytes / 3 * 4
        + match bytes % 3 {
            0 => 0,
            _ => 4,
        }
}

const fn decode_base64(byte: u8, index: usize) -> Result<u8, ParseBase64Error> {
    match byte {
        b'A'..=b'Z' => Ok(byte - b'A'),
        b'a'..=b'z' => Ok(byte - b'a' + 26),
        b'0'..=b'9' => Ok(byte - b'0' + 52),
        b'+' => Ok(62),
        b'/' => Ok(63),
        b'=' => Err(ParseBase64Error::InvalidPadding { index }),
        _ => Err(ParseBase64Error::InvalidByte { index }),
    }
}

const fn parse_base64<const N: usize>(input: &str) -> Result<[u8; N], ParseBase64Error> {
    let expected = base64_length(N);
    if input.len() != expected {
        return Err(ParseBase64Error::InvalidLength {
            expected,
            actual: input.len(),
        });
    }

    let input = input.as_bytes();
    let mut output = [0; N];
    let mut input_index = 0;
    let mut output_index = 0;

    while N - output_index >= 3 {
        let a = match decode_base64(input[input_index], input_index) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let b = match decode_base64(input[input_index + 1], input_index + 1) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let c = match decode_base64(input[input_index + 2], input_index + 2) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        let d = match decode_base64(input[input_index + 3], input_index + 3) {
            Ok(value) => value,
            Err(error) => return Err(error),
        };
        output[output_index] = a << 2 | b >> 4;
        output[output_index + 1] = b << 4 | c >> 2;
        output[output_index + 2] = c << 6 | d;
        input_index += 4;
        output_index += 3;
    }

    match N - output_index {
        0 => {}
        1 => {
            let a = match decode_base64(input[input_index], input_index) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let b = match decode_base64(input[input_index + 1], input_index + 1) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if input[input_index + 2] != b'=' {
                return Err(ParseBase64Error::InvalidPadding {
                    index: input_index + 2,
                });
            }
            if input[input_index + 3] != b'=' {
                return Err(ParseBase64Error::InvalidPadding {
                    index: input_index + 3,
                });
            }
            if b & 0x0f != 0 {
                return Err(ParseBase64Error::NonCanonical {
                    index: input_index + 1,
                });
            }
            output[output_index] = a << 2 | b >> 4;
        }
        2 => {
            let a = match decode_base64(input[input_index], input_index) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let b = match decode_base64(input[input_index + 1], input_index + 1) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            let c = match decode_base64(input[input_index + 2], input_index + 2) {
                Ok(value) => value,
                Err(error) => return Err(error),
            };
            if input[input_index + 3] != b'=' {
                return Err(ParseBase64Error::InvalidPadding {
                    index: input_index + 3,
                });
            }
            if c & 0x03 != 0 {
                return Err(ParseBase64Error::NonCanonical {
                    index: input_index + 2,
                });
            }
            output[output_index] = a << 2 | b >> 4;
            output[output_index + 1] = b << 4 | c >> 2;
        }
        _ => unreachable!(),
    }
    Ok(output)
}

#[doc(hidden)]
#[must_use]
pub const fn __o256_from_hex(input: &str) -> O256 {
    match O256::from_hex(input) {
        Ok(value) => value,
        Err(_) => panic!("invalid o256 hex literal"),
    }
}

/// Constructs an [`O256`] from a hexadecimal literal at compile time.
///
/// ```compile_fail
/// use covalence_lib_hash::{O256, o256};
/// const INVALID: O256 = o256!("00");
/// ```
#[macro_export]
macro_rules! o256 {
    ($hex:literal) => {{
        const VALUE: $crate::O256 = $crate::__o256_from_hex($hex);
        VALUE
    }};
}

/// Declares a checked-in BLAKE3 context key.
///
/// The context expression documents what must be used to validate the
/// precomputed value; validation is performed in a test because BLAKE3 is not
/// const-evaluable.
#[macro_export]
macro_rules! ctx_key {
    ($context:expr, $hex:literal) => {{
        const _: &str = $context;
        const VALUE: $crate::CtxKey = $crate::o256!($hex).coerce();
        VALUE
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __o256_path_start {
    ($root:expr; $first:ident $($tail:tt)*) => {{
        let value = $root.tag(stringify!($first));
        $crate::__o256_path_tail!(value; $($tail)*)
    }};
    ($root:expr; { $first:expr } $($tail:tt)*) => {{
        let value = $root.tag($first);
        $crate::__o256_path_tail!(value; $($tail)*)
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __o256_path_tail {
    ($value:ident;) => {
        $value
    };
    ($value:ident; . $next:ident $($tail:tt)*) => {{
        let value = $value.tag(stringify!($next));
        $crate::__o256_path_tail!(value; $($tail)*)
    }};
    ($value:ident; . { $next:expr } $($tail:tt)*) => {{
        let value = $value.tag($next);
        $crate::__o256_path_tail!(value; $($tail)*)
    }};
}

/// Derives an absolute or relative O256 path.
///
/// Absolute paths begin with `::` and default to [`COV`]. A named context
/// key may precede `::`. Relative paths start with a named O256 followed by
/// `.`. Braced expressions may provide either a root or an interpolated path
/// segment.
///
/// ```
/// # #[cfg(feature = "blake3")] {
/// use covalence_lib_hash::{o256_path, COV, COV_ROOT};
///
/// let absolute = o256_path!(::sexpr.list);
/// assert_eq!(absolute, o256_path!(COV::sexpr.list));
///
/// let relative = o256_path!(COV_ROOT.sexpr.list);
/// assert_eq!(relative, COV_ROOT.tag("sexpr").tag("list"));
///
/// let segment = "dynamic";
/// assert_eq!(
///     o256_path!(COV::sexpr.{segment}),
///     COV.tag("sexpr").tag(segment),
/// );
/// # }
/// ```
#[macro_export]
macro_rules! o256_path {
    (:: $($path:tt)+) => {{
        $crate::__o256_path_start!($crate::COV; $($path)+)
    }};
    ($context:ident :: $($path:tt)+) => {{
        let context: $crate::CtxKey = $context;
        $crate::__o256_path_start!(context; $($path)+)
    }};
    ({ $context:expr } :: $($path:tt)+) => {{
        let context: $crate::CtxKey = $context;
        $crate::__o256_path_start!(context; $($path)+)
    }};
    ($root:ident . $($path:tt)+) => {{
        let root: $crate::O256 = $root;
        $crate::__o256_path_start!(root; $($path)+)
    }};
    ({ $root:expr } . $($path:tt)+) => {{
        let root: $crate::O256 = $root;
        $crate::__o256_path_start!(root; $($path)+)
    }};
    // Legacy expression form for non-identifier path components.
    ($root:expr, $first:expr $(, $rest:expr)* $(,)?) => {{
        let value = $root.tag($first);
        $(let value = value.tag($rest);)*
        value
    }};
}

/// Asserts that an O256 literal is the named path below a root.
///
/// This is intended for tests accompanying checked-in protocol constants.
#[macro_export]
macro_rules! assert_o256_path {
    ($expected:expr, $($path:tt)+) => {
        assert_eq!($expected, $crate::o256_path!($($path)+))
    };
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::rc::Rc;

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
        assert_eq!(O256::from_array(o256_bytes).as_bytes(), &o256_bytes);
        assert_eq!(O256::from_array(o256_bytes).into_bytes(), o256_bytes);
        assert_eq!(GitHash::from_array(git_bytes).as_bytes(), &git_bytes);
        assert_eq!(GitHash::from_array(git_bytes).into_bytes(), git_bytes);
    }

    #[test]
    fn fixed_value_formatting_and_parsing() {
        let o256 = O256::from_array([0xab; 32]);
        let git = GitHash::from_array([0xcd; 20]);
        assert_eq!(o256.to_string(), "ab".repeat(32));
        assert!(format!("{o256:?}").ends_with(&format!(">({o256})")));
        assert_eq!(git.to_string(), "cd".repeat(20));
        assert!(format!("{git:?}").ends_with(&format!(">({git})")));
        assert_eq!(O256::from_hex(&"ab".repeat(32)), Ok(o256));
        assert_eq!("AB".repeat(32).parse(), Ok(o256));
        assert_eq!("CD".repeat(20).parse(), Ok(git));
    }

    #[test]
    fn fixed_values_parse_from_hex_and_base64_in_constants() {
        const HEX: O256 = match O256::from_hex(
            "abababababababababababababababababababababababababababababababab",
        ) {
            Ok(value) => value,
            Err(_) => panic!("valid hexadecimal"),
        };
        const BASE64: O256 = match O256::from_base64("q6urq6urq6urq6urq6urq6urq6urq6urq6urq6urq6s=")
        {
            Ok(value) => value,
            Err(_) => panic!("valid Base64"),
        };
        const GIT_BASE64: GitHash = match GitHash::from_base64("zMzMzMzMzMzMzMzMzMzMzMzMzMw=") {
            Ok(value) => value,
            Err(_) => panic!("valid Base64"),
        };

        assert_eq!(HEX, O256::from_array([0xab; 32]));
        assert_eq!(BASE64, O256::from_array([0xab; 32]));
        assert_eq!(GIT_BASE64, GitHash::from_array([0xcc; 20]));
    }

    #[test]
    fn base64_parsing_requires_canonical_padding() {
        assert_eq!(
            OpaqueObj::<1>::from_base64("AA"),
            Err(ParseBase64Error::InvalidLength {
                expected: 4,
                actual: 2,
            })
        );
        assert_eq!(
            OpaqueObj::<1>::from_base64("AB=="),
            Err(ParseBase64Error::NonCanonical { index: 1 })
        );
        assert_eq!(
            OpaqueObj::<2>::from_base64("AAB="),
            Err(ParseBase64Error::NonCanonical { index: 2 })
        );
        assert_eq!(
            OpaqueObj::<3>::from_base64("AAA!"),
            Err(ParseBase64Error::InvalidByte { index: 3 })
        );
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
        let low = O256::from_array([0; 32]);
        let mut high_bytes = [0; 32];
        high_bytes[31] = 1;
        let high = O256::from_array(high_bytes);
        assert!(low < high);
        assert_eq!(hash(low), hash(O256::from_array([0; 32])));
        assert_ne!(hash(low), hash(high));

        let low = GitHash::from_array([0; 20]);
        let mut high_bytes = [0; 20];
        high_bytes[19] = 1;
        let high = GitHash::from_array(high_bytes);
        assert!(low < high);
        assert_eq!(hash(low), hash(GitHash::from_array([0; 20])));
        assert_ne!(hash(low), hash(high));
    }

    #[test]
    fn fixed_values_default_to_zero() {
        assert_eq!(O256::default().into_bytes(), [0; 32]);
        assert_eq!(GitHash::default().into_bytes(), [0; 20]);
    }

    impl Namespace for Rc<()> {
        const BYTES: usize = 7;
        type Bytes = [u8; Self::BYTES];
        type Opaque = Opaque<7>;
    }

    #[test]
    fn representation_and_value_traits_do_not_depend_on_namespace() {
        fn require<T: Copy + Clone + Eq + Ord + Hash + Send + Sync>() {}
        require::<Obj<Rc<()>>>();

        assert_eq!(std::mem::size_of::<Obj<Rc<()>>>(), 7);
        assert_eq!(std::mem::align_of::<Obj<Rc<()>>>(), 1);
        assert_eq!(Cov::BYTES, 32);
        assert_eq!(Cov::BITS, 256);
        assert_eq!(Git::BYTES, 20);
        assert_eq!(Git::BITS, 160);
    }

    #[test]
    fn namespace_representatives_are_constructible_zsts() {
        let representatives = (
            Cov,
            Blake3,
            Sha256,
            CtxKeyNamespace,
            Git,
            Sha1,
            Opaque::<32>,
        );
        assert_eq!(std::mem::size_of_val(&representatives), 0);
        assert_eq!(std::mem::size_of::<Cov>(), 0);
        assert_eq!(std::mem::size_of::<Blake3>(), 0);
        assert_eq!(std::mem::size_of::<Opaque<32>>(), 0);
    }

    #[test]
    fn coercion_and_erasure_preserve_only_bytes() {
        let standard = O256::from_array([0xa5; 32]);
        let opaque: OpaqueObj<32> = standard.opaque();
        let opaque_again: OpaqueObj<32> = opaque.opaque();
        let context: CtxKey = standard.coerce();
        assert_eq!(opaque_again.as_ref(), &[0xa5; 32]);
        assert_eq!(context.as_ref(), standard.as_ref());
    }

    #[test]
    fn literal_macros_are_const_and_paths_are_checked() {
        const VALUE: O256 =
            o256!("abababababababababababababababababababababababababababababababab");
        const CONTEXT: CtxKey = ctx_key!(
            "test context",
            "abababababababababababababababababababababababababababababababab"
        );
        assert_eq!(VALUE.as_bytes(), &[0xab; 32]);
        assert_eq!(CONTEXT.as_bytes(), &[0xab; 32]);

        #[cfg(feature = "blake3")]
        {
            let expected = COV.tag("test").tag("leaf");
            assert_eq!(o256_path!(::test.leaf), expected);
            assert_eq!(o256_path!(COV::test.leaf), expected);
            assert_eq!(
                o256_path!(COV_ROOT.test.leaf),
                COV_ROOT.tag("test").tag("leaf")
            );
            assert_o256_path!(expected, ::test.leaf);
            assert_o256_path!(expected, COV::test.leaf);
            assert_o256_path!(COV_ROOT.tag("test").tag("leaf"), COV_ROOT.test.leaf);
            let segment = "leaf";
            assert_eq!(o256_path!(COV::test.{segment}), expected);
            assert_eq!(o256_path!({ Cov::ROOT_CTX }::test.{segment}), expected);
            assert_eq!(
                o256_path!({ Cov::ROOT }.test.{segment}),
                Cov::ROOT.tag("test").tag(segment)
            );
        }
    }
}
