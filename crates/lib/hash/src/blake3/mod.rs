//! Covalence and BLAKE3-family namespaces and operations.

#[cfg(feature = "blake3")]
mod cv;

#[cfg(feature = "blake3")]
pub mod tree;

#[cfg(feature = "blake3")]
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

    /// Precomputed BLAKE3 context key for [`Self::ROOT_CTX_KEY`].
    pub const ROOT_CTX: CtxKey = crate::ctx_key!(
        Cov::ROOT_CTX_KEY,
        "9d4dd8ba210b01b0332a3481238222c990c6a7f6df58a1a63f2e741833793a96"
    );

    /// Context-keyed hash of the empty string under [`Self::ROOT_CTX`].
    pub const ROOT: O256 =
        crate::o256!("ca3ad8d7ae65099e3cc8caa64aff13976f6ba3863a77454dd8b37fb6efd1f783");
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

#[cfg(all(test, any(feature = "blake3", feature = "sha256", feature = "random")))]
mod tests {
    use super::*;

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
