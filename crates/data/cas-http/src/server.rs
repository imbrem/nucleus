//! HTTP transport over a transport-neutral [`CasService`].

use std::net::SocketAddr;
use std::str::FromStr;
use std::sync::Arc;

use axum::extract::{DefaultBodyLimit, Path, Request, State};
use axum::http::{HeaderMap, Method, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use covalence_data_cas::{
    ByteRange, CasService, CasServiceError, ObjectRanges, PrefixResolution, StoredObject,
};
use covalence_lib_hash::O256;
use covalence_lib_serde::{Deserialize, Serialize};
use futures::StreamExt;
use tower_http::cors::{Any, CorsLayer};

use crate::{
    MAX_RESPONSE_BYTES, MAX_UPLOAD_BYTES, MIN_HASH_PREFIX_HEX, OBJECT_PREFIX, UPLOAD_PATH,
};

/// A running service.
///
/// Dropping it shuts the service down.
pub struct Serving {
    address: SocketAddr,
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
}

impl Serving {
    /// The address actually bound, including the port when port 0 was asked for.
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

/// Serves a transport-neutral CAS service on a background runtime.
///
/// # Errors
///
/// Returns an error when the runtime cannot start or the address cannot be bound.
pub fn serve<S>(service: Arc<S>, address: SocketAddr) -> std::io::Result<Serving>
where
    S: CasService + ?Sized + 'static,
{
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .build()?;
    let listener = runtime.block_on(tokio::net::TcpListener::bind(address))?;
    let address = listener.local_addr()?;
    let (shutdown, shutdown_signal) = tokio::sync::oneshot::channel();
    let router = router(service);

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

fn router<S>(service: Arc<S>) -> Router
where
    S: CasService + ?Sized + 'static,
{
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any)
        .expose_headers([
            header::CONTENT_RANGE,
            header::CONTENT_LENGTH,
            header::CONTENT_LOCATION,
            header::LOCATION,
        ]);

    Router::new()
        .route(UPLOAD_PATH, post(upload::<S>).put(upload::<S>))
        .route(
            &format!("{OBJECT_PREFIX}{{address}}"),
            get(legacy_object::<S>),
        )
        .route(
            &format!("{OBJECT_PREFIX}{{algorithm}}/{{address}}"),
            get(algorithm_object::<S>).put(algorithm_put::<S>),
        )
        .layer(DefaultBodyLimit::max(MAX_UPLOAD_BYTES))
        .layer(cors)
        .with_state(service)
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(crate = "covalence_lib_serde")]
pub(crate) struct StoredObjectDto {
    pub(crate) algorithm: String,
    pub(crate) hash: String,
    pub(crate) bytes: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) index: Option<u64>,
}

impl From<StoredObject> for StoredObjectDto {
    fn from(stored: StoredObject) -> Self {
        Self {
            algorithm: "blake3".to_owned(),
            hash: stored.address.hex().to_string(),
            bytes: stored.len,
            index: stored.index,
        }
    }
}

#[derive(Serialize)]
#[serde(crate = "covalence_lib_serde")]
struct ErrorDto<'a> {
    error: &'a str,
    message: String,
}

#[derive(Deserialize, Serialize)]
#[serde(crate = "covalence_lib_serde")]
pub(crate) struct PrefixChoicesDto {
    pub(crate) algorithm: String,
    pub(crate) prefix: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) hints: Option<PrefixHintsDto>,
}

#[derive(Deserialize, Serialize)]
#[serde(crate = "covalence_lib_serde")]
pub(crate) struct PrefixHintsDto {
    pub(crate) prefixes: Vec<String>,
    pub(crate) covers_all_matches: bool,
    pub(crate) all_prefixes_match: bool,
}

async fn upload<S>(State(service): State<Arc<S>>, request: Request) -> Response
where
    S: CasService + ?Sized,
{
    match stream_upload(service.as_ref(), None, request).await {
        Ok(stored) => stored_response(StatusCode::CREATED, stored),
        Err(error) => service_error(&error),
    }
}

async fn algorithm_put<S>(
    State(service): State<Arc<S>>,
    Path((algorithm, address)): Path<(String, String)>,
    request: Request,
) -> Response
where
    S: CasService + ?Sized,
{
    if algorithm != "blake3" {
        return unsupported_algorithm(&algorithm);
    }
    let Ok(address) = O256::from_str(&address) else {
        return api_error(
            StatusCode::BAD_REQUEST,
            "invalid_hash",
            "verified PUT requires a complete 64-digit hexadecimal BLAKE3 hash".to_owned(),
        );
    };
    match stream_upload(service.as_ref(), Some(address), request).await {
        Ok(stored) => stored_response(StatusCode::OK, stored),
        Err(error) => service_error(&error),
    }
}

async fn resolve_address<S>(service: &S, input: &str) -> Result<O256, Response>
where
    S: CasService + ?Sized,
{
    if input.len() == 64 {
        return O256::from_str(input).map_err(|_| {
            api_error(
                StatusCode::BAD_REQUEST,
                "invalid_hash",
                "expected hexadecimal BLAKE3 hash digits".to_owned(),
            )
        });
    }
    if input.len() < MIN_HASH_PREFIX_HEX {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "hash_prefix_too_short",
            format!("hash prefixes must contain at least {MIN_HASH_PREFIX_HEX} hexadecimal digits"),
        ));
    }
    if input.len() > 64 || !input.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(api_error(
            StatusCode::BAD_REQUEST,
            "invalid_hash_prefix",
            "expected at most 64 hexadecimal BLAKE3 hash digits".to_owned(),
        ));
    }
    let prefix = input.to_ascii_lowercase();
    match service.resolve_blake3_prefix(prefix.clone()).await {
        Ok(PrefixResolution::Unique(address)) => {
            let location = format!("/cas/blake3/{}", address.hex());
            let mut response = StatusCode::TEMPORARY_REDIRECT.into_response();
            if let Ok(location) = header::HeaderValue::from_str(&location) {
                response.headers_mut().insert(header::LOCATION, location);
            }
            response.headers_mut().insert(
                header::CACHE_CONTROL,
                header::HeaderValue::from_static("no-store"),
            );
            Err(response)
        }
        Ok(PrefixResolution::Missing) => Err(api_error(
            StatusCode::NOT_FOUND,
            "hash_prefix_not_found",
            format!("no BLAKE3 address has prefix {prefix}"),
        )),
        Ok(PrefixResolution::Ambiguous { hints }) => Err((
            StatusCode::MULTIPLE_CHOICES,
            Json(PrefixChoicesDto {
                algorithm: "blake3".to_owned(),
                prefix,
                hints: hints.map(|hints| PrefixHintsDto {
                    prefixes: hints.prefixes,
                    covers_all_matches: hints.covers_all_matches,
                    all_prefixes_match: hints.all_prefixes_match,
                }),
            }),
        )
            .into_response()),
        Ok(PrefixResolution::Unsupported) => Err(api_error(
            StatusCode::NOT_IMPLEMENTED,
            "prefix_lookup_unsupported",
            "this CAS does not support BLAKE3 prefix lookup".to_owned(),
        )),
        Err(error) => Err(service_error(&error)),
    }
}

async fn stream_upload<S>(
    service: &S,
    expected: Option<O256>,
    request: Request,
) -> Result<StoredObject, CasServiceError>
where
    S: CasService + ?Sized,
{
    let mut upload = service.begin_upload(expected).await?;
    let mut body = request.into_body().into_data_stream();
    let mut received = 0u64;
    while let Some(chunk) = body.next().await {
        let chunk = chunk.map_err(|source| CasServiceError::Provider {
            source: Box::new(source),
        })?;
        received = received.saturating_add(chunk.len() as u64);
        if received > MAX_UPLOAD_BYTES as u64 {
            return Err(CasServiceError::ObjectTooLarge {
                len: received,
                limit: MAX_UPLOAD_BYTES as u64,
            });
        }
        upload.write(chunk).await?;
    }
    upload.finish().await
}

fn stored_response(status: StatusCode, stored: StoredObject) -> Response {
    let location = format!("/cas/blake3/{}", stored.address.hex());
    let mut response = (status, Json(StoredObjectDto::from(stored))).into_response();
    if let Ok(location) = header::HeaderValue::from_str(&location) {
        response.headers_mut().insert(header::LOCATION, location);
    }
    response
}

async fn legacy_object<S>(
    state: State<Arc<S>>,
    Path(address): Path<String>,
    method: Method,
    headers: HeaderMap,
) -> Response
where
    S: CasService + ?Sized,
{
    object(state, address, method, headers, true).await
}

async fn algorithm_object<S>(
    state: State<Arc<S>>,
    Path((algorithm, address)): Path<(String, String)>,
    method: Method,
    headers: HeaderMap,
) -> Response
where
    S: CasService + ?Sized,
{
    if algorithm != "blake3" {
        return unsupported_algorithm(&algorithm);
    }
    object(state, address, method, headers, false).await
}

async fn object<S>(
    State(service): State<Arc<S>>,
    address: String,
    method: Method,
    headers: HeaderMap,
    legacy: bool,
) -> Response
where
    S: CasService + ?Sized,
{
    let address = match resolve_address(service.as_ref(), &address).await {
        Ok(address) => address,
        Err(response) => return response,
    };
    let canonical = format!("/cas/blake3/{}", address.hex());

    if method == Method::HEAD {
        return match service.get_ranges(address, Vec::new()).await {
            Ok(Some(object)) => head_response(object.len, &canonical, legacy),
            Ok(None) => not_found(address),
            Err(error) => service_error(&error),
        };
    }

    let Some(range) = headers.get(header::RANGE) else {
        return match service.get(address).await {
            Ok(Some(bytes)) if bytes.len() as u64 <= MAX_RESPONSE_BYTES => {
                let mut response = (immutable_headers(), bytes).into_response();
                set_content_location(&mut response, &canonical, legacy);
                response
            }
            Ok(Some(_)) => api_error(
                StatusCode::PAYLOAD_TOO_LARGE,
                "response_too_large",
                format!("whole-object responses are limited to {MAX_RESPONSE_BYTES} bytes"),
            ),
            Ok(None) => not_found(address),
            Err(error) => service_error(&error),
        };
    };

    let Some(range) = range.to_str().ok().and_then(parse_ranges) else {
        return api_error(
            StatusCode::BAD_REQUEST,
            "invalid_range",
            "expected a byte Range header".to_owned(),
        );
    };
    match service.get_ranges(address, range).await {
        Ok(Some(object)) if object.parts.is_empty() => unsatisfiable(object.len),
        Ok(Some(object)) if object.parts.len() == 1 => single_range(object, &canonical, legacy),
        Ok(Some(object)) => multiple_ranges(address, object, &canonical, legacy),
        Ok(None) => not_found(address),
        Err(CasServiceError::InvalidRange { len, .. }) => unsatisfiable(len),
        Err(error) => service_error(&error),
    }
}

fn parse_ranges(value: &str) -> Option<Vec<ByteRange>> {
    let specs = value.strip_prefix("bytes=")?;
    specs
        .split(',')
        .map(|spec| {
            let (start, end) = spec.trim().split_once('-')?;
            match (start.is_empty(), end.is_empty()) {
                (true, false) => Some(ByteRange::Suffix(end.parse().ok()?)),
                (false, true) => Some(ByteRange::From(start.parse().ok()?)),
                (false, false) => {
                    let start = start.parse().ok()?;
                    let inclusive_end: u64 = end.parse().ok()?;
                    Some(ByteRange::Bounded(start..inclusive_end.checked_add(1)?))
                }
                (true, true) => None,
            }
        })
        .collect()
}

fn single_range(object: ObjectRanges, canonical: &str, legacy: bool) -> Response {
    let part = object
        .parts
        .into_iter()
        .next()
        .unwrap_or_else(|| unreachable!());
    if part.bytes.len() as u64 > MAX_RESPONSE_BYTES {
        return api_error(
            StatusCode::PAYLOAD_TOO_LARGE,
            "response_too_large",
            format!("range responses are limited to {MAX_RESPONSE_BYTES} bytes"),
        );
    }
    let mut response = (
        StatusCode::PARTIAL_CONTENT,
        immutable_headers(),
        [(
            header::CONTENT_RANGE,
            format!(
                "bytes {}-{}/{}",
                part.range.start,
                part.range.end - 1,
                object.len
            ),
        )],
        part.bytes,
    )
        .into_response();
    set_content_location(&mut response, canonical, legacy);
    response
}

fn multiple_ranges(address: O256, object: ObjectRanges, canonical: &str, legacy: bool) -> Response {
    let payload_len = object.parts.iter().fold(0u64, |total, part| {
        total.saturating_add(part.bytes.len() as u64)
    });
    if payload_len > MAX_RESPONSE_BYTES {
        return api_error(
            StatusCode::PAYLOAD_TOO_LARGE,
            "response_too_large",
            format!("combined range payloads are limited to {MAX_RESPONSE_BYTES} bytes"),
        );
    }
    let boundary = format!("nucleus-{:016x}", address.addr64());
    let mut body = Vec::new();
    for part in object.parts {
        body.extend_from_slice(format!(
            "--{boundary}\r\nContent-Type: application/octet-stream\r\nContent-Range: bytes {}-{}/{}\r\n\r\n",
            part.range.start,
            part.range.end - 1,
            object.len
        ).as_bytes());
        body.extend_from_slice(&part.bytes);
        body.extend_from_slice(b"\r\n");
    }
    body.extend_from_slice(format!("--{boundary}--\r\n").as_bytes());
    let mut response = (
        StatusCode::PARTIAL_CONTENT,
        [(
            header::CONTENT_TYPE,
            format!("multipart/byteranges; boundary={boundary}"),
        )],
        body,
    )
        .into_response();
    set_content_location(&mut response, canonical, legacy);
    response
}

fn head_response(len: u64, canonical: &str, legacy: bool) -> Response {
    let mut response = (
        immutable_headers(),
        [(header::CONTENT_LENGTH, len.to_string())],
    )
        .into_response();
    set_content_location(&mut response, canonical, legacy);
    response
}

fn unsatisfiable(len: u64) -> Response {
    let mut response = api_error(
        StatusCode::RANGE_NOT_SATISFIABLE,
        "range_not_satisfiable",
        format!("no requested range is satisfiable for an object of {len} bytes"),
    );
    if let Ok(value) = header::HeaderValue::from_str(&format!("bytes */{len}")) {
        response.headers_mut().insert(header::CONTENT_RANGE, value);
    }
    response
}

fn immutable_headers() -> [(header::HeaderName, &'static str); 4] {
    [
        (header::CONTENT_TYPE, "application/octet-stream"),
        (header::ACCEPT_RANGES, "bytes"),
        (header::CACHE_CONTROL, "public, max-age=31536000, immutable"),
        (
            header::HeaderName::from_static("cross-origin-resource-policy"),
            "cross-origin",
        ),
    ]
}

fn set_content_location(response: &mut Response, canonical: &str, legacy: bool) {
    if legacy && let Ok(value) = header::HeaderValue::from_str(canonical) {
        response
            .headers_mut()
            .insert(header::CONTENT_LOCATION, value);
    }
}

fn unsupported_algorithm(algorithm: &str) -> Response {
    api_error(
        StatusCode::NOT_IMPLEMENTED,
        "unsupported_hash_algorithm",
        format!("hash algorithm {algorithm:?} is not supported; supported: blake3"),
    )
}

fn not_found(address: O256) -> Response {
    api_error(
        StatusCode::NOT_FOUND,
        "object_not_found",
        format!("CAS object {address} was not found"),
    )
}

fn service_error(error: &CasServiceError) -> Response {
    match error {
        CasServiceError::AddressMismatch { .. } => api_error(
            StatusCode::UNPROCESSABLE_ENTITY,
            "hash_mismatch",
            error.to_string(),
        ),
        CasServiceError::InvalidRange { len, .. } => unsatisfiable(*len),
        CasServiceError::UploadFinished => api_error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "upload_finished",
            error.to_string(),
        ),
        CasServiceError::ObjectTooLarge { .. } => api_error(
            StatusCode::PAYLOAD_TOO_LARGE,
            "object_too_large",
            error.to_string(),
        ),
        CasServiceError::Provider { .. } => api_error(
            StatusCode::INTERNAL_SERVER_ERROR,
            "provider_error",
            error.to_string(),
        ),
    }
}

fn api_error(status: StatusCode, error: &'static str, message: String) -> Response {
    (status, Json(ErrorDto { error, message })).into_response()
}
