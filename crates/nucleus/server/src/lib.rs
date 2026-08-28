//! Untrusted native server assembly around Nucleus checked core.
//!
//! This crate owns and exposes checked kernel state, but creates no trusted
//! facts itself. HTTP parsing, routing, storage selection, and observations of
//! kernel metadata remain outside the trusted computing base.

use std::net::SocketAddr;
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use axum::extract::State;
use axum::routing::get;
use axum::{Json, Router};
use covalence_data_cas::{CasService, SharedIndexCas};
use covalence_lib_serde::Serialize;
use covalence_nucleus_core::hol::Kernel;

/// A Nucleus kernel paired with a composable CAS service.
pub struct NucleusServer<C = SharedIndexCas> {
    kernel: RwLock<Kernel>,
    cas: Arc<C>,
}

impl NucleusServer<SharedIndexCas> {
    /// Creates an empty kernel with an empty in-memory CAS.
    #[must_use]
    pub fn empty() -> Self {
        Self::new(Kernel::new(), Arc::new(SharedIndexCas::new()))
    }
}

impl Default for NucleusServer<SharedIndexCas> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<C> NucleusServer<C> {
    /// Creates a server assembly from checked kernel state and a CAS service.
    #[must_use]
    pub const fn new(kernel: Kernel, cas: Arc<C>) -> Self {
        Self {
            kernel: RwLock::new(kernel),
            cas,
        }
    }

    /// Borrows the checked kernel for observation.
    pub fn kernel(&self) -> RwLockReadGuard<'_, Kernel> {
        self.kernel
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Borrows the checked kernel for checked operations.
    pub fn kernel_mut(&self) -> RwLockWriteGuard<'_, Kernel> {
        self.kernel
            .write()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Clones the registered CAS service handle.
    #[must_use]
    pub fn cas(&self) -> Arc<C> {
        Arc::clone(&self.cas)
    }
}

impl<C> NucleusServer<C>
where
    C: CasService + 'static,
{
    /// Builds all currently supported Nucleus HTTP routes.
    pub fn router(self: &Arc<Self>) -> Router {
        Router::new()
            .route("/nucleus", get(kernel_info::<C>))
            .with_state(Arc::clone(self))
            .merge(covalence_data_cas_http::router(Arc::clone(&self.cas)))
    }

    /// Serves this Nucleus instance on a background runtime.
    ///
    /// # Errors
    ///
    /// Returns an error when the runtime cannot start or the address cannot be
    /// bound.
    pub fn serve(self: &Arc<Self>, address: SocketAddr) -> std::io::Result<Serving> {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(2)
            .enable_all()
            .build()?;
        let listener = runtime.block_on(tokio::net::TcpListener::bind(address))?;
        let address = listener.local_addr()?;
        let (shutdown, shutdown_signal) = tokio::sync::oneshot::channel();
        let router = self.router();

        std::thread::spawn(move || {
            runtime.block_on(async move {
                let _ = axum::serve(listener, router)
                    .with_graceful_shutdown(async move {
                        let _ = shutdown_signal.await;
                    })
                    .await;
            });
        });

        Ok(Serving {
            address,
            shutdown: Some(shutdown),
        })
    }
}

#[derive(Serialize)]
#[serde(crate = "covalence_lib_serde")]
struct KernelInfo {
    address: String,
    rows: usize,
    init: Option<InitInfo>,
}

#[derive(Serialize)]
#[serde(crate = "covalence_lib_serde")]
struct InitInfo {
    address: String,
    rows: usize,
}

async fn kernel_info<C>(State(server): State<Arc<NucleusServer<C>>>) -> Json<KernelInfo> {
    let kernel = server.kernel();
    Json(KernelInfo {
        address: kernel.addr().hex().to_string(),
        rows: kernel.len(),
        init: kernel.init_prefix().map(|(address, rows)| InitInfo {
            address: address.hex().to_string(),
            rows,
        }),
    })
}

/// A running Nucleus HTTP server.
///
/// Dropping it requests graceful shutdown.
pub struct Serving {
    address: SocketAddr,
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
}

impl Serving {
    /// Returns the actual bound address.
    #[must_use]
    pub const fn address(&self) -> SocketAddr {
        self.address
    }

    /// Returns the base URL clients should use.
    #[must_use]
    pub fn base_url(&self) -> String {
        format!("http://{}", self.address)
    }
}

impl Drop for Serving {
    fn drop(&mut self) {
        if let Some(shutdown) = self.shutdown.take() {
            let _ = shutdown.send(());
        }
    }
}
