//! Covalence and BLAKE3-family namespaces and operations.

mod cv;
mod konst;

pub use cv::{Blake3Cv, Blake3Merkle};

use crate::{Namespace, O256, Obj, Opaque, RootedNamespace};

#[cfg(any(feature = "blake3", feature = "sha256"))]
use crate::HashNamespace;
#[cfg(feature = "blake3")]
use crate::{KeyedNamespace, TagNamespace};

/// Covalence's interoperable 256-bit namespace.
///
/// Byte hashing currently embeds BLAKE3 into this namespace. SHA-256 remains
/// separate for now; a future explicit namespace-embedding API could add it
/// without making the algorithm-specific [`Sha256`] namespace ambiguous.
pub struct Cov;

impl Namespace for Cov {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// Unkeyed BLAKE3 digests.
///
/// This algorithm-specific namespace deliberately supports neither random
/// construction nor self-tagging.
///
/// ```compile_fail
/// use covalence_lib_hash::{Blake3, RandomNamespace};
///
/// fn require_random<N: RandomNamespace>() {}
/// require_random::<Blake3>();
/// ```
pub struct Blake3;

impl Namespace for Blake3 {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// An unkeyed BLAKE3 digest.
///
/// With the default `serde` feature, values use a DAG-JSON link containing a
/// `CIDv1` with the `raw` codec and `blake3-256` multihash code.
pub type Blake3Hash = Obj<Blake3>;

/// SHA-256 digests.
pub struct Sha256;

impl Namespace for Sha256 {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// A SHA-256 digest.
///
/// With the default `serde` feature, values use a DAG-JSON link containing a
/// `CIDv1` with the `raw` codec and `sha2-256` multihash code.
pub type Sha256Hash = Obj<Sha256>;

/// BLAKE3 derive-key context keys.
pub struct CtxKeyNamespace;

impl Namespace for CtxKeyNamespace {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// A BLAKE3 context key.
pub type CtxKey = Obj<CtxKeyNamespace>;

impl Cov {
    /// Random identity embedded in [`Self::ROOT_CTX_KEY`].
    pub const OPAQUE_ROOT: Obj<Opaque<32>> =
        crate::o256!("38d89420af90780c9e244ee03024ec81f62f4e68949152d64f0a8c5d8caede4e").opaque();

    /// Versioned BLAKE3 derive-key context anchoring the standard hierarchy.
    pub const ROOT_CTX_KEY: &'static str =
        "covalence 0.0.0 38d89420af90780c9e244ee03024ec81f62f4e68949152d64f0a8c5d8caede4e";

    /// BLAKE3 context key derived from [`Self::ROOT_CTX_KEY`].
    ///
    /// The hexadecimal literal is redundant: the compiler derives the key, and
    /// the literal records the expected value and fails the build if the
    /// hierarchy ever moves.
    pub const ROOT_CTX: CtxKey = crate::ctx_key!(
        const Cov::ROOT_CTX_KEY,
        "9d4dd8ba210b01b0332a3481238222c990c6a7f6df58a1a63f2e741833793a96"
    );

    /// Context-keyed hash of the empty string under [`Self::ROOT_CTX`].
    pub const ROOT: O256 = crate::checked_o256!(
        Cov::ROOT_CTX.croot(),
        "ca3ad8d7ae65099e3cc8caa64aff13976f6ba3863a77454dd8b37fb6efd1f783"
    );
}

/// Standard Covalence BLAKE3 context key.
pub const COV: CtxKey = Cov::ROOT_CTX;

/// Root object of the standard Covalence hierarchy.
pub const COV_ROOT: O256 = Cov::ROOT;

impl RootedNamespace for Cov {
    type Context = CtxKeyNamespace;
    const OPAQUE_ROOT: Obj<Self::Opaque> = Self::OPAQUE_ROOT;
    const ROOT_CTX_KEY: &'static str = Self::ROOT_CTX_KEY;
    const ROOT_CTX: CtxKey = Self::ROOT_CTX;
    const ROOT: Obj<Self> = Self::ROOT;
}

#[cfg(feature = "blake3")]
fn finish<N>(
    mut hasher: ::blake3::Hasher,
    mut reader: impl std::io::Read,
) -> std::io::Result<Obj<N>>
where
    N: Namespace<Bytes = [u8; 32]>,
{
    std::io::copy(&mut reader, &mut hasher)?;
    Ok(Obj::from_array(*hasher.finalize().as_bytes()))
}

#[cfg(feature = "blake3")]
impl HashNamespace for Blake3 {
    fn hash(bytes: impl AsRef<[u8]>) -> Obj<Self> {
        Obj::from_array(*::blake3::hash(bytes.as_ref()).as_bytes())
    }

    fn hash_from_reader(reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        finish(::blake3::Hasher::new(), reader)
    }
}

impl Obj<Blake3> {
    /// Embeds this BLAKE3 digest into the Covalence namespace.
    ///
    /// Covalence uses BLAKE3 as its current content-hash embedding, so this
    /// operation preserves the representation exactly.
    #[must_use]
    pub const fn into_o256(self) -> O256 {
        self.coerce()
    }

    /// Hashes bytes in a `const` context.
    ///
    /// This is the compile-time form of unkeyed BLAKE3. It agrees with the
    /// runtime implementation on every input, but compresses one block at a
    /// time; prefer the runtime form for anything but the short inputs that
    /// appear in constants.
    ///
    /// ```
    /// use covalence_lib_hash::Blake3Hash;
    ///
    /// const DIGEST: Blake3Hash = Blake3Hash::chash(b"abc");
    /// assert_eq!(
    ///     DIGEST.to_string(),
    ///     "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85",
    /// );
    /// ```
    #[must_use]
    pub const fn chash(bytes: &[u8]) -> Self {
        Obj::from_array(konst::hash(bytes))
    }
}

impl From<Obj<Blake3>> for O256 {
    fn from(value: Obj<Blake3>) -> Self {
        value.into_o256()
    }
}

#[cfg(feature = "blake3")]
impl HashNamespace for Cov {
    fn hash(bytes: impl AsRef<[u8]>) -> Obj<Self> {
        Obj::from_array(*::blake3::hash(bytes.as_ref()).as_bytes())
    }

    fn hash_from_reader(reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        finish(::blake3::Hasher::new(), reader)
    }
}

#[cfg(feature = "blake3")]
impl KeyedNamespace<O256> for Cov {
    fn keyed(key: &O256, bytes: impl AsRef<[u8]>) -> Obj<Self> {
        Obj::from_array(*::blake3::keyed_hash(key.as_bytes(), bytes.as_ref()).as_bytes())
    }

    fn keyed_from_reader(key: &O256, reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        finish(::blake3::Hasher::new_keyed(key.as_bytes()), reader)
    }
}

#[cfg(feature = "blake3")]
impl KeyedNamespace<str> for Cov {
    fn keyed(context: &str, bytes: impl AsRef<[u8]>) -> Obj<Self> {
        Obj::from_array(::blake3::derive_key(context, bytes.as_ref()))
    }

    fn keyed_from_reader(context: &str, reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        finish(::blake3::Hasher::new_derive_key(context), reader)
    }
}

#[cfg(feature = "blake3")]
impl KeyedNamespace<String> for Cov {
    fn keyed(context: &String, bytes: impl AsRef<[u8]>) -> Obj<Self> {
        Cov::keyed(context.as_str(), bytes)
    }

    fn keyed_from_reader(
        context: &String,
        reader: impl std::io::Read,
    ) -> std::io::Result<Obj<Self>> {
        Cov::keyed_from_reader(context.as_str(), reader)
    }
}

#[cfg(feature = "blake3")]
impl KeyedNamespace<CtxKey> for Cov {
    fn keyed(key: &CtxKey, bytes: impl AsRef<[u8]>) -> Obj<Self> {
        use ::blake3::hazmat::HasherExt;
        let mut hasher = ::blake3::Hasher::new_from_context_key(key.as_bytes());
        hasher.update(bytes.as_ref());
        Obj::from_array(*hasher.finalize().as_bytes())
    }

    fn keyed_from_reader(key: &CtxKey, reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
        use ::blake3::hazmat::HasherExt;
        finish(
            ::blake3::Hasher::new_from_context_key(key.as_bytes()),
            reader,
        )
    }
}

#[cfg(feature = "blake3")]
impl Obj<CtxKeyNamespace> {
    /// Derives a context key from a human-readable context string.
    #[must_use]
    pub fn derive(context: &str) -> CtxKey {
        Obj::from_array(::blake3::hazmat::hash_derive_key_context(context))
    }

    /// Returns the empty-string root under this context key.
    #[must_use]
    pub fn root(&self) -> O256 {
        O256::with_ctx(self, [])
    }
}

impl Obj<CtxKeyNamespace> {
    /// Derives a context key from a context string in a `const` context.
    ///
    /// This is the compile-time form of `derive`, and the way a checked-in
    /// context key is now written.
    ///
    /// ```
    /// use covalence_lib_hash::CtxKey;
    ///
    /// const KEY: CtxKey = CtxKey::cderive("covalence example context");
    /// ```
    #[must_use]
    pub const fn cderive(context: &str) -> CtxKey {
        Obj::from_array(konst::hash_derive_key_context(context))
    }

    /// Tags bytes under this context key in a `const` context.
    ///
    /// This is the compile-time form of [`tag`](Obj::tag).
    #[must_use]
    pub const fn ctag(&self, bytes: &[u8]) -> O256 {
        O256::cctx(self, bytes)
    }

    /// Returns the empty-string root under this context key, in a `const`
    /// context.
    ///
    /// This is the compile-time form of `root`.
    #[must_use]
    pub const fn croot(&self) -> O256 {
        self.ctag(&[])
    }
}

#[cfg(feature = "blake3")]
impl O256 {
    /// Hashes bytes under a context key.
    #[must_use]
    pub fn with_ctx(key: &CtxKey, bytes: impl AsRef<[u8]>) -> Self {
        Self::with_key(key, bytes)
    }

    /// Returns the root of the standard Covalence hierarchy.
    #[must_use]
    pub const fn root() -> Self {
        Cov::ROOT
    }
}

impl O256 {
    /// Hashes bytes in a `const` context.
    ///
    /// This is the compile-time form of [`from_bytes`](Obj::from_bytes), and
    /// agrees with it on every input. Const evaluation is an interpreter, so
    /// it is meant for the short inputs constants are built from: an input of
    /// tens of kilobytes exceeds rustc's `long_running_const_eval` limit, and
    /// at run time this is far slower than the vectorized implementation.
    ///
    /// ```
    /// use covalence_lib_hash::O256;
    ///
    /// const DIGEST: O256 = O256::chash(b"abc");
    /// assert_eq!(
    ///     DIGEST.to_string(),
    ///     "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85",
    /// );
    /// ```
    #[must_use]
    pub const fn chash(bytes: &[u8]) -> Self {
        Obj::from_array(konst::hash(bytes))
    }

    /// Hashes bytes under a 256-bit key in a `const` context.
    ///
    /// This is the compile-time form of
    /// [`with_key`](Obj::with_key)`::<O256>`.
    #[must_use]
    pub const fn ckeyed(key: &O256, bytes: &[u8]) -> Self {
        Obj::from_array(konst::keyed_hash(key.as_bytes(), bytes))
    }

    /// Hashes bytes under a human-readable context string, in a `const`
    /// context.
    ///
    /// This is the compile-time form of [`with_key`](Obj::with_key)`::<str>`.
    /// It hashes the context on every call; deriving the key once with
    /// [`CtxKey::cderive`] and calling [`cctx`](Self::cctx) reaches the same
    /// object without repeating that work.
    #[must_use]
    pub const fn cderive_key(context: &str, bytes: &[u8]) -> Self {
        Obj::from_array(konst::derive_key(context, bytes))
    }

    /// Hashes bytes under a context key in a `const` context.
    ///
    /// This is the compile-time form of `with_ctx`.
    #[must_use]
    pub const fn cctx(key: &CtxKey, bytes: &[u8]) -> Self {
        Obj::from_array(konst::hash_from_context_key(key.as_bytes(), bytes))
    }

    /// Derives a child object by tagging bytes with this object, in a `const`
    /// context.
    ///
    /// This is the compile-time form of [`tag`](Obj::tag).
    ///
    /// ```
    /// use covalence_lib_hash::{COV_ROOT, O256};
    ///
    /// const LIST: O256 = COV_ROOT.ctag(b"sexpr").ctag(b"list");
    /// ```
    #[must_use]
    pub const fn ctag(&self, bytes: &[u8]) -> Self {
        Self::ckeyed(self, bytes)
    }
}

#[cfg(feature = "sha256")]
impl HashNamespace for Sha256 {
    fn hash(bytes: impl AsRef<[u8]>) -> Obj<Self> {
        use sha2::Digest;
        Obj::from_array(sha2::Sha256::digest(bytes.as_ref()).into())
    }

    fn hash_from_reader(mut reader: impl std::io::Read) -> std::io::Result<Obj<Self>> {
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
        Ok(Obj::from_array(hasher.finalize().into()))
    }
}

#[cfg(feature = "random")]
impl O256 {
    /// Draws a standard object from a caller-provided CSPRNG.
    pub fn random<R>(rng: &mut R) -> Self
    where
        R: covalence_lib_rand::Rng + covalence_lib_rand::CryptoRng,
    {
        <Cov as crate::RandomNamespace>::random(rng)
    }
}

#[cfg(feature = "blake3")]
impl TagNamespace for Cov {
    type Tag = Cov;

    fn tag(key: &Obj<Self>, bytes: impl AsRef<[u8]>) -> Obj<Self::Tag> {
        Cov::keyed(key, bytes)
    }

    fn tag_from_reader(
        key: &Obj<Self>,
        reader: impl std::io::Read,
    ) -> std::io::Result<Obj<Self::Tag>> {
        Cov::keyed_from_reader(key, reader)
    }
}

#[cfg(feature = "blake3")]
impl TagNamespace for CtxKeyNamespace {
    type Tag = Cov;

    fn tag(key: &Obj<Self>, bytes: impl AsRef<[u8]>) -> Obj<Self::Tag> {
        Cov::keyed(key, bytes)
    }

    fn tag_from_reader(
        key: &Obj<Self>,
        reader: impl std::io::Read,
    ) -> std::io::Result<Obj<Self::Tag>> {
        Cov::keyed_from_reader(key, reader)
    }
}

#[cfg(feature = "random")]
impl crate::RandomNamespace for Cov {}

#[cfg(test)]
mod const_tests {
    use super::*;

    /// Published BLAKE3 vectors, which the const implementation must
    /// reproduce without the reference implementation being compiled in.
    #[test]
    fn const_hashing_reproduces_published_vectors() {
        const EMPTY: O256 = O256::chash(b"");
        const ABC: O256 = O256::chash(b"abc");
        const DIGEST: Blake3Hash = Blake3Hash::chash(b"abc");

        assert_eq!(
            EMPTY.to_string(),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
        assert_eq!(
            ABC.to_string(),
            "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
        );
        assert_eq!(DIGEST.into_o256(), ABC);
    }

    /// The standard hierarchy is derived, not checked in, so evaluating these
    /// constants at all exercises the derive-key context and context-key modes
    /// against the values [`Cov`] records.
    #[test]
    fn the_standard_hierarchy_is_derived_at_compile_time() {
        assert_eq!(Cov::ROOT_CTX, CtxKey::cderive(Cov::ROOT_CTX_KEY));
        assert_eq!(Cov::ROOT, Cov::ROOT_CTX.croot());
        assert_eq!(Cov::ROOT, COV.ctag(b""));
        assert_eq!(
            Cov::ROOT_CTX.to_string(),
            "9d4dd8ba210b01b0332a3481238222c990c6a7f6df58a1a63f2e741833793a96"
        );
        assert_eq!(
            Cov::ROOT.to_string(),
            "ca3ad8d7ae65099e3cc8caa64aff13976f6ba3863a77454dd8b37fb6efd1f783"
        );
    }

    /// Inputs long enough to build a tree still evaluate at compile time.
    #[test]
    fn multi_chunk_inputs_evaluate_at_compile_time() {
        const INPUT: [u8; 2049] = [0x5a; 2049];
        const DIGEST: O256 = O256::chash(&INPUT);
        const TAGGED: O256 = COV_ROOT.ctag(&INPUT);

        assert_ne!(DIGEST, O256::default());
        assert_ne!(TAGGED, DIGEST);
    }
}

#[cfg(all(test, any(feature = "blake3", feature = "sha256", feature = "random")))]
mod tests {
    use super::*;

    /// Lengths that straddle every block, chunk, and subtree boundary the tree
    /// hasher distinguishes.
    #[cfg(feature = "blake3")]
    const BOUNDARY_LENGTHS: &[usize] = &[
        0, 1, 2, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025, 2047, 2048, 2049, 3072, 3073, 4096,
        4097, 5120, 6144, 8192, 8193, 16_384, 16_385, 31_744, 65_536,
    ];

    #[cfg(feature = "blake3")]
    fn boundary_input(length: usize) -> Vec<u8> {
        (0..length)
            .map(|index| u8::try_from(index % 251).expect("index modulo 251 is a byte"))
            .collect()
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn const_hashing_matches_the_reference_implementation_in_every_mode() {
        let key = O256::from_array([7; 32]);
        let context = "covalence 0.0.0 const hashing test context";
        let context_key = CtxKey::derive(context);

        assert_eq!(context_key, CtxKey::cderive(context));

        for &length in BOUNDARY_LENGTHS {
            let input = boundary_input(length);
            assert_eq!(
                O256::chash(&input),
                O256::from_bytes(&input),
                "unkeyed hash of {length} bytes"
            );
            assert_eq!(
                Blake3Hash::chash(&input),
                Blake3Hash::from_bytes(&input),
                "unkeyed digest of {length} bytes"
            );
            assert_eq!(
                O256::ckeyed(&key, &input),
                O256::with_key(&key, &input),
                "keyed hash of {length} bytes"
            );
            assert_eq!(key.ctag(&input), key.tag(&input), "tag of {length} bytes");
            assert_eq!(
                O256::cderive_key(context, &input),
                O256::with_key(context, &input),
                "derived key from {length} bytes"
            );
            assert_eq!(
                O256::cctx(&context_key, &input),
                O256::with_ctx(&context_key, &input),
                "context-keyed hash of {length} bytes"
            );
            assert_eq!(
                context_key.ctag(&input),
                context_key.tag(&input),
                "context tag of {length} bytes"
            );
        }
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn const_subtree_hashing_matches_the_reference_implementation() {
        for chunks in [1_u64, 2, 4, 8] {
            for offset in [0_u64, 8, 16, 64] {
                let length =
                    usize::try_from(chunks).expect("chunk count fits") * ::blake3::CHUNK_LEN;
                let input = boundary_input(length);
                let input_offset = offset * ::blake3::CHUNK_LEN as u64;
                assert_eq!(
                    Blake3Cv::csubtree(input_offset, &input),
                    Blake3Cv::from_subtree(input_offset, &input),
                    "{chunks} chunks at chunk {offset}"
                );
            }
        }
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn blake3_vectors_and_reader() {
        const CONST_BLAKE3: Blake3Hash = Blake3Hash::from_array([0xa5; 32]);
        const CONST_O256: O256 = CONST_BLAKE3.into_o256();

        fn assert_blake3(_: Blake3Hash) {}
        fn assert_covalence(_: O256) {}

        assert_eq!(
            O256::from_bytes([]).to_string(),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
        let expected = "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85";
        let covalence = O256::from_bytes(b"abc");
        let blake3 = Blake3Hash::from_bytes(b"abc");
        assert_covalence(covalence);
        assert_blake3(blake3);
        assert_eq!(covalence.to_string(), expected);
        assert_eq!(blake3.to_string(), expected);
        assert_eq!(covalence.opaque(), blake3.opaque());

        assert_eq!(CONST_O256.as_bytes(), CONST_BLAKE3.as_bytes());
        assert_eq!(O256::from(blake3), covalence);

        assert_eq!(
            O256::from_reader(std::io::Cursor::new(b"abc"))
                .unwrap()
                .to_string(),
            expected
        );
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn sha256_vectors_and_reader() {
        fn assert_sha256_namespace(_: Obj<Sha256>) {}

        assert_eq!(
            Sha256Hash::from_bytes([]).to_string(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
        let digest = Sha256Hash::from_bytes(b"abc");
        assert_sha256_namespace(digest);
        let _: crate::OpaqueObj<32> = digest.opaque();
        assert_eq!(digest.to_string(), expected);
        assert_eq!(
            Sha256Hash::from_reader(std::io::Cursor::new(b"abc"))
                .unwrap()
                .to_string(),
            expected
        );
    }

    #[cfg(feature = "random")]
    #[test]
    fn random_is_deterministic_with_a_seeded_rng() {
        use covalence_lib_rand::SeedableRng;

        let mut first = covalence_lib_rand::rngs::StdRng::seed_from_u64(42);
        let mut second = covalence_lib_rand::rngs::StdRng::seed_from_u64(42);
        assert_eq!(O256::random(&mut first), Obj::random(&mut second));
        assert_ne!(O256::random(&mut first), Obj::default());
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn each_blake3_key_mode_matches_its_reference_api() {
        use ::blake3::hazmat::HasherExt;

        let bytes = b"payload";
        let key = O256::from_array([7; 32]);
        assert_eq!(
            Cov::keyed(&key, bytes).as_bytes(),
            ::blake3::keyed_hash(key.as_bytes(), bytes).as_bytes()
        );

        let context = String::from("covalence test context");
        let context_key = CtxKey::derive(&context);
        assert_eq!(
            Cov::keyed(context.as_str(), bytes),
            Cov::keyed(&context, bytes)
        );
        assert_eq!(
            Cov::keyed(context.as_str(), bytes),
            Cov::keyed(&context_key, bytes)
        );

        let mut reference = ::blake3::Hasher::new_from_context_key(context_key.as_bytes());
        reference.update(bytes);
        assert_eq!(
            Cov::keyed(&context_key, bytes).as_bytes(),
            reference.finalize().as_bytes()
        );
        assert_ne!(Cov::keyed(&key, bytes), Cov::keyed(&context_key, bytes));
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn all_blake3_reader_modes_match_in_memory_hashing() {
        let bytes = b"reader payload";
        let key = O256::from_array([3; 32]);
        let context = "covalence reader context";
        let context_key = CtxKey::derive(context);

        assert_eq!(
            O256::from_bytes(bytes),
            O256::from_reader(std::io::Cursor::new(bytes)).unwrap()
        );
        assert_eq!(
            O256::with_key(&key, bytes),
            O256::with_key_from_reader(&key, std::io::Cursor::new(bytes)).unwrap()
        );
        assert_eq!(
            O256::with_key(context, bytes),
            O256::with_key_from_reader(context, std::io::Cursor::new(bytes)).unwrap()
        );
        assert_eq!(
            O256::with_ctx(&context_key, bytes),
            O256::with_key_from_reader(&context_key, std::io::Cursor::new(bytes)).unwrap()
        );
        assert_eq!(
            key.tag(bytes),
            key.tag_from_reader(std::io::Cursor::new(bytes)).unwrap()
        );
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn reader_errors_are_preserved_by_every_blake3_mode() {
        struct Failing;
        impl std::io::Read for Failing {
            fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("expected failure"))
            }
        }

        let key = O256::from_array([3; 32]);
        let context_key = CtxKey::derive("failure context");
        assert!(O256::from_reader(Failing).is_err());
        assert!(O256::with_key_from_reader(&key, Failing).is_err());
        assert!(O256::with_key_from_reader("failure context", Failing).is_err());
        assert!(O256::with_key_from_reader(&context_key, Failing).is_err());
        assert!(key.tag_from_reader(Failing).is_err());
    }

    #[cfg(feature = "sha256")]
    #[test]
    fn sha256_reader_errors_are_preserved() {
        struct Failing;
        impl std::io::Read for Failing {
            fn read(&mut self, _: &mut [u8]) -> std::io::Result<usize> {
                Err(std::io::Error::other("expected failure"))
            }
        }

        assert!(Sha256Hash::from_reader(Failing).is_err());
    }

    #[cfg(feature = "blake3")]
    #[test]
    fn root_and_tag_hierarchy_are_reproducible() {
        assert_eq!(
            Cov::ROOT_CTX,
            CtxKey::derive(Cov::ROOT_CTX_KEY),
            "changing the context intentionally changes the hierarchy"
        );
        assert_eq!(
            Cov::ROOT_CTX_KEY,
            format!("covalence 0.0.0 {}", Cov::OPAQUE_ROOT)
        );
        assert_eq!(Cov::ROOT, Cov::ROOT_CTX.root());
        assert_eq!(Cov::ROOT, Cov::ROOT_CTX.tag([]));
        assert_eq!(Cov::ROOT, O256::root());

        let value = O256::from_bytes(b"value");
        assert_eq!(value.tag(value), value.tag(value.as_bytes()));
        assert_eq!(
            Cov::ROOT.tag("sexpr").tag("list"),
            O256::with_key(&O256::with_key(&Cov::ROOT, "sexpr"), "list")
        );
    }

    #[cfg(all(feature = "blake3", feature = "random"))]
    #[test]
    fn tag_random_is_deterministic_for_a_seeded_csprng() {
        use covalence_lib_rand::SeedableRng;

        let mut first = covalence_lib_rand::rngs::StdRng::seed_from_u64(7);
        let mut second = covalence_lib_rand::rngs::StdRng::seed_from_u64(7);
        let first_tag = Cov::ROOT_CTX.tag_random(&mut first);
        assert_eq!(first_tag, Cov::ROOT_CTX.tag_random(&mut second));
        assert_ne!(first_tag, Cov::ROOT_CTX.tag_random(&mut first));
    }
}
