//! Execution of untrusted proof requests extracted from `.cov` trees.

use std::sync::Arc;

use covalence_data_cas::AsyncCas;
use covalence_data_vfs::ResourceVfs;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_hol::Kernel;
use covalence_nucleus_script::{CompiledTree, ProofSource};

use crate::{ProofError, Strategy};

/// One checked kernel returned by a named script proof request.
#[derive(Debug)]
pub struct ScriptProofOutput {
    name: String,
    kernel: Kernel,
}

impl ScriptProofOutput {
    /// Returns the module-qualified proof name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Borrows the checked kernel returned by the proof component.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Splits the navigation name from the checked kernel.
    #[must_use]
    pub fn into_parts(self) -> (String, Kernel) {
        (self.name, self.kernel)
    }
}

/// Failure while resolving or running a `.cov` proof declaration.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ScriptProofError {
    /// A VFS-backed component could not be read.
    #[snafu(display("could not read proof {name} component {resource:?}: {source}"))]
    Resource {
        /// Module-qualified proof name.
        name: String,
        /// Opaque VFS resource key.
        resource: String,
        /// VFS failure.
        source: std::io::Error,
    },
    /// A resource-backed declaration had no VFS provider.
    #[snafu(display("proof {name} needs a VFS to load component {resource:?}"))]
    MissingVfs {
        /// Module-qualified proof name.
        name: String,
        /// Opaque VFS resource key.
        resource: String,
    },
    /// A content-addressed declaration had no CAS provider.
    #[snafu(display("proof {name} needs a CAS to load component {address}"))]
    MissingCas {
        /// Module-qualified proof name.
        name: String,
        /// Requested component address.
        address: O256,
    },
    /// Component instantiation or execution failed.
    #[snafu(display("proof {name} failed: {source}"))]
    Proof {
        /// Module-qualified proof name.
        name: String,
        /// Portable proof runtime failure.
        source: Box<ProofError>,
    },
}

/// Resolves and runs every proof declared in a compiled source tree.
///
/// Resource-backed components are loaded from `resources`. Address-backed
/// components require `cas`. When supplied, the same CAS is also exposed to
/// the instantiated component during execution. Proof syntax, resource
/// selection, and execution order remain outside the trusted kernel.
///
/// # Errors
///
/// Returns an error when a component resource is absent, an address has no CAS,
/// component validation/instantiation fails, or a component rejects its
/// request. Outputs completed before the failure are discarded by this helper.
pub fn run_script_proofs(
    tree: &CompiledTree,
    resources: Option<Arc<dyn ResourceVfs>>,
    cas: Option<Arc<dyn AsyncCas>>,
) -> Result<Vec<ScriptProofOutput>, ScriptProofError> {
    // Own the capability bundle so this API has the same shape as future
    // Python and WIT hosts without monomorphizing orchestration per VFS type.
    let capabilities = (resources, cas);
    let mut kernel = tree.module().kernel().fork();
    let mut outputs = Vec::with_capacity(tree.proofs().len());
    for declaration in tree.proofs() {
        let name = declaration.name().to_owned();
        let mut strategy = match declaration.source() {
            ProofSource::Resource(resource) => {
                let resources =
                    capabilities
                        .0
                        .as_ref()
                        .ok_or_else(|| ScriptProofError::MissingVfs {
                            name: name.clone(),
                            resource: resource.to_string(),
                        })?;
                let bytes =
                    resources
                        .read(resource)
                        .map_err(|source| ScriptProofError::Resource {
                            name: name.clone(),
                            resource: resource.to_string(),
                            source,
                        })?;
                match &capabilities.1 {
                    Some(provider) => Strategy::from_bytes_with_cas(&bytes, Arc::clone(provider)),
                    None => Strategy::from_bytes(&bytes),
                }
            }
            ProofSource::Address(address) => {
                let provider =
                    capabilities
                        .1
                        .as_ref()
                        .ok_or_else(|| ScriptProofError::MissingCas {
                            name: name.clone(),
                            address: *address,
                        })?;
                Strategy::from_address(*address, Arc::clone(provider))
            }
        }
        .map_err(|source| ScriptProofError::Proof {
            name: name.clone(),
            source: Box::new(source),
        })?;
        let arguments = declaration
            .target()
            .map_or_else(Vec::new, |address| address.as_bytes().to_vec());
        kernel = strategy
            .apply_tactic(0, arguments, Some(kernel))
            .map_err(|source| ScriptProofError::Proof {
                name: name.clone(),
                source: Box::new(source),
            })?;
        outputs.push(ScriptProofOutput {
            name,
            kernel: kernel.fork(),
        });
    }
    Ok(outputs)
}
