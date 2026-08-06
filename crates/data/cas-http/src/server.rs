//! A read-only HTTP service over a [`Cas`].
//!
//! Everything fiddly is a library's: `axum` routes, `headers` parses `Range`
//! and formats `Content-Range`, `tower-http` does CORS. What is written here is
//! the address lookup and the bounds.

use std::net::SocketAddr;
use std::str::FromStr;
use std::sync::Arc;

use axum::Router;
use axum::extract::{Path, State};
use axum::http::{StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::get;
use axum_extra::TypedHeader;
use bytes::Bytes;
use covalence_data_cas::{Cas, CasObject};
use covalence_lib_hash::O256;
use tower_http::cors::{Any, CorsLayer};

use crate::{MAX_RESPONSE_BYTES, OBJECT_PREFIX};

/// A running service.
///
/// Dropping it shuts the service down.
pub struct Serving {
    address: SocketAddr,
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
}

impl Serving {
    /// The address actually bound, including the port when port 0 was asked
    /// for.
    #[must_use]
    pub const fn address(&self) -> SocketAddr {
        self.address
    }

    /// The base URL a client should use.
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

/// Serves `cas` read-only on `address`.
///
/// The runtime lives in a thread of its own, so callers stay synchronous; the
/// rest of this workspace has no async in it and does not acquire any by using
/// this.
///
/// Reads run on the runtime's worker threads and the [`Cas`] interface is
/// synchronous, so a slow store blocks a worker. That is fine for a resident
/// store and would not be for a remote one.
///
/// # Errors
///
/// Returns an error when the runtime cannot start or the address cannot be
/// bound.
pub fn serve<C>(cas: Arc<C>, address: SocketAddr) -> std::io::Result<Serving>
where
    C: Cas + Send + Sync + 'static,
    C::Error: std::fmt::Display,
{
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()?;

    let listener = runtime.block_on(tokio::net::TcpListener::bind(address))?;
    let address = listener.local_addr()?;

    let (shutdown, shutdown_signal) = tokio::sync::oneshot::channel();
    let router = router(cas);

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

fn router<C>(cas: Arc<C>) -> Router
where
    C: Cas + Send + Sync + 'static,
    C::Error: std::fmt::Display,
{
    // The demo page is served from a different origin than the kernel, and a
    // ranged read needs `Range` to survive preflight.
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any)
        .expose_headers([header::CONTENT_RANGE, header::CONTENT_LENGTH]);

    Router::new()
        // `get` also answers HEAD, which is how a client asks for a length.
        .route(&format!("{OBJECT_PREFIX}{{address}}"), get(object::<C>))
        .layer(cors)
        .with_state(cas)
}

/// Serves one object, whole or ranged.
async fn object<C>(
    State(cas): State<Arc<C>>,
    Path(address): Path<String>,
    range: Option<TypedHeader<headers::Range>>,
) -> Response
where
    C: Cas + Send + Sync + 'static,
    C::Error: std::fmt::Display,
{
    let Ok(address) = O256::from_str(&address) else {
        return StatusCode::NOT_FOUND.into_response();
    };
    let object = match cas.open(address) {
        Ok(Some(object)) => object,
        Ok(None) => return StatusCode::NOT_FOUND.into_response(),
        Err(error) => {
            return (StatusCode::INTERNAL_SERVER_ERROR, error.to_string()).into_response();
        }
    };
    let len = object.len();

    let Some(TypedHeader(range)) = range else {
        if len > MAX_RESPONSE_BYTES {
            // A client wanting more must ask for ranges, which is what a VFS
            // does anyway.
            return StatusCode::PAYLOAD_TOO_LARGE.into_response();
        }
        return match read(&object, 0..len) {
            Ok(bytes) => (immutable_headers(), bytes).into_response(),
            Err(error) => (StatusCode::INTERNAL_SERVER_ERROR, error).into_response(),
        };
    };

    // `headers` does the parsing and the satisfiability rules; take the first
    // range and refuse a multi-range request rather than half-answering it.
    let mut ranges = range.satisfiable_ranges(len);
    let Some((start, end)) = ranges.next() else {
        return unsatisfiable(len);
    };
    if ranges.next().is_some() {
        return StatusCode::RANGE_NOT_SATISFIABLE.into_response();
    }

    let start = match start {
        std::ops::Bound::Included(start) => start,
        std::ops::Bound::Excluded(start) => start.saturating_add(1),
        std::ops::Bound::Unbounded => 0,
    };
    let end = match end {
        std::ops::Bound::Included(end) => end.saturating_add(1),
        std::ops::Bound::Excluded(end) => end,
        std::ops::Bound::Unbounded => len,
    }
    .min(len);

    if start >= len || end <= start {
        return unsatisfiable(len);
    }
    if end - start > MAX_RESPONSE_BYTES {
        return StatusCode::PAYLOAD_TOO_LARGE.into_response();
    }

    match read(&object, start..end) {
        Ok(bytes) => (
            StatusCode::PARTIAL_CONTENT,
            immutable_headers(),
            // `Content-Range` is inclusive at both ends; `headers` formats it.
            TypedHeader(
                headers::ContentRange::bytes(start..end, len)
                    .unwrap_or_else(|_| unreachable!("range was validated against len")),
            ),
            bytes,
        )
            .into_response(),
        Err(error) => (StatusCode::INTERNAL_SERVER_ERROR, error).into_response(),
    }
}

fn unsatisfiable(len: u64) -> Response {
    let mut response = StatusCode::RANGE_NOT_SATISFIABLE.into_response();
    if let Ok(value) = header::HeaderValue::from_str(&format!("bytes */{len}")) {
        response.headers_mut().insert(header::CONTENT_RANGE, value);
    }
    response
}

/// A content address names fixed bytes, so a response can be cached forever.
fn immutable_headers() -> [(header::HeaderName, &'static str); 3] {
    [
        (header::CONTENT_TYPE, "application/octet-stream"),
        (header::ACCEPT_RANGES, "bytes"),
        (header::CACHE_CONTROL, "public, max-age=31536000, immutable"),
    ]
}

fn read<O: CasObject>(object: &O, range: std::ops::Range<u64>) -> Result<Bytes, String>
where
    O::Error: std::fmt::Display,
{
    object.read(range).map_err(|error| error.to_string())
}
