//! Offline access to the pinned WebAssembly 3.0 bundle.

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash};
use covalence_lib_error::snafu::Snafu;

use crate::{
    ArtifactError, BundleManifest, IlDocument, IlError, Limits, ManifestError, SPECTEC_VERSION,
    WASM_3_RELEASE, WASM_3_REVISION, WASM_UPSTREAM,
};

/// Canonical DRISL manifest bytes for the pinned WebAssembly 3.0 bundle.
pub const WASM_3_MANIFEST_BYTES: &[u8] = include_bytes!("../vendor/wasm-3.0/manifest.drisl");

/// Exact elaborated IL bytes emitted by the pinned `SpecTec` executable.
pub const WASM_3_AST_BYTES: &[u8] = include_bytes!("../vendor/wasm-3.0/wasm-3.0.ast.sexp");

/// An offline-verified view of the pinned WebAssembly 3.0 inputs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Wasm3Bundle {
    manifest: BundleManifest,
    manifest_cid: Cid,
    il: IlDocument,
}

impl Wasm3Bundle {
    /// Returns the exact decoded bundle manifest.
    #[must_use]
    pub const fn manifest(&self) -> &BundleManifest {
        &self.manifest
    }

    /// Returns the canonical SHA-256 DRISL CID of the manifest.
    #[must_use]
    pub const fn manifest_cid(&self) -> Cid {
        self.manifest_cid
    }

    /// Returns the exhaustive elaborated IL inventory.
    #[must_use]
    pub const fn il(&self) -> &IlDocument {
        &self.il
    }
}

/// Why the checked-in WebAssembly 3.0 bundle did not match its pinned identity.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Wasm3Error {
    /// The canonical manifest could not be decoded.
    #[snafu(display("could not decode pinned Wasm 3.0 manifest: {source}"))]
    Manifest {
        /// Underlying canonical schema error.
        source: ManifestError,
    },
    /// A release identity field drifted from the compile-time pin.
    #[snafu(display("pinned Wasm 3.0 manifest has unexpected {field}"))]
    Identity {
        /// Field whose exact value changed.
        field: &'static str,
    },
    /// The elaborated IL bytes did not match the manifest.
    #[snafu(display("pinned Wasm 3.0 IL does not match its artifact record: {source}"))]
    Artifact {
        /// Exact byte-identity mismatch.
        source: ArtifactError,
    },
    /// The elaborated IL declaration envelope could not be recognized.
    #[snafu(display("could not inventory pinned Wasm 3.0 IL: {source}"))]
    Il {
        /// Underlying syntax, limit, or root-shape error.
        source: IlError,
    },
    /// The parsed metrics disagreed with the manifest.
    #[snafu(display("pinned Wasm 3.0 IL metrics disagree with the manifest"))]
    Summary,
}

/// Loads and verifies the complete checked-in WebAssembly 3.0 bundle offline.
///
/// This establishes byte identity and a complete declaration inventory, not
/// semantic correspondence or theorem validity.
///
/// # Errors
///
/// Returns an error if any manifest identity, content address, metric, syntax,
/// resource bound, or declaration-envelope check fails.
pub fn wasm3_bundle() -> Result<Wasm3Bundle, Wasm3Error> {
    let manifest = BundleManifest::decode(WASM_3_MANIFEST_BYTES)
        .map_err(|source| Wasm3Error::Manifest { source })?;
    for (field, matches) in [
        ("upstream repository", manifest.upstream == WASM_UPSTREAM),
        ("upstream revision", manifest.revision == WASM_3_REVISION),
        ("release name", manifest.release == WASM_3_RELEASE),
        (
            "SpecTec generator version",
            manifest.generator_version == SPECTEC_VERSION,
        ),
    ] {
        if !matches {
            return Err(Wasm3Error::Identity { field });
        }
    }
    manifest
        .ast
        .artifact
        .verify(WASM_3_AST_BYTES)
        .map_err(|source| Wasm3Error::Artifact { source })?;
    let il = IlDocument::parse(WASM_3_AST_BYTES, Limits::default())
        .map_err(|source| Wasm3Error::Il { source })?;
    if il.parsed().summary != manifest.ast.summary {
        return Err(Wasm3Error::Summary);
    }
    let manifest_cid = drisl::address(CidCodec::Drisl, CidHash::Sha256, WASM_3_MANIFEST_BYTES);
    Ok(Wasm3Bundle {
        manifest,
        manifest_cid,
        il,
    })
}
