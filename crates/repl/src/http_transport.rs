//! Minimal synchronous HTTP transport for signed kernel-service frames.
//!
//! This module is deliberately only a byte transport. The recipient key is pinned out of band,
//! but grant and result signature verification belongs to `signed_client`. Every exchange uses a
//! fresh TCP connection, `Connection: close`, and exactly one request; callers must never retry an
//! invocation after an ambiguous I/O failure.

use std::error::Error as StdError;
use std::fmt;
use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::time::Duration;

use covalence_kernel_service::wire::{MAX_WIRE_PAYLOAD_BYTES, PublicKeyIdentity};

/// Binary endpoint which issues a recipient-signed channel grant.
pub const CHANNEL_PATH: &str = "/v0/channel";
/// Binary endpoint which accepts an invocation and returns its recipient-signed result.
pub const INVOCATION_PATH: &str = "/v0/invocation";

const BINARY_CONTENT_TYPE: &str = "application/octet-stream";
const TEXT_CONTENT_TYPE: &str = "text/plain; charset=utf-8";
const MAX_HEADER_BYTES: usize = 8 << 10;
const MAX_DIAGNOSTIC_BYTES: usize = 4 << 10;
// The current canonical invocation/result overheads are below 384 bytes. Keeping the transport
// limit independent of their precise layout lets the wire decoder remain the source of truth.
const MAX_SIGNED_FRAME_BYTES: usize = MAX_WIRE_PAYLOAD_BYTES + 384;
const CHANNEL_CALLER_BYTES: usize = 32;
const MAX_CHANNEL_GRANT_BYTES: usize = 512;
const BOOTSTRAP_TOKEN_BYTES: usize = 32;

/// One-time, high-entropy bootstrap capability for authorizing a caller key.
pub type BootstrapToken = [u8; BOOTSTRAP_TOKEN_BYTES];

/// Numeric loopback endpoint with an independently supplied recipient-key pin.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct LoopbackHttpEndpoint {
    address: SocketAddr,
    recipient: PublicKeyIdentity,
    connect_timeout: Duration,
    io_timeout: Duration,
    bootstrap_token: Option<BootstrapToken>,
}

impl fmt::Debug for LoopbackHttpEndpoint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LoopbackHttpEndpoint")
            .field("address", &self.address)
            .field("recipient", &self.recipient)
            .field("connect_timeout", &self.connect_timeout)
            .field("io_timeout", &self.io_timeout)
            .field("has_bootstrap_token", &self.bootstrap_token.is_some())
            .finish()
    }
}

impl LoopbackHttpEndpoint {
    /// Constructs an endpoint. Hostnames and non-loopback addresses are not representable.
    ///
    /// # Errors
    ///
    /// Rejects a non-loopback address or a zero timeout.
    pub fn new(
        address: SocketAddr,
        recipient: PublicKeyIdentity,
        connect_timeout: Duration,
        io_timeout: Duration,
    ) -> Result<Self, HttpTransportError> {
        if !address.ip().is_loopback() {
            return Err(HttpTransportError::NonLoopbackAddress(address));
        }
        if connect_timeout.is_zero() || io_timeout.is_zero() {
            return Err(HttpTransportError::ZeroTimeout);
        }
        Ok(Self {
            address,
            recipient,
            connect_timeout,
            io_timeout,
            bootstrap_token: None,
        })
    }

    /// Adds a one-time bootstrap capability to the next channel request.
    #[must_use]
    pub const fn with_bootstrap_token(mut self, token: BootstrapToken) -> Self {
        self.bootstrap_token = Some(token);
        self
    }

    /// Exact numeric address used for both TCP and the HTTP `Host` field.
    #[must_use]
    pub const fn address(&self) -> SocketAddr {
        self.address
    }

    /// Out-of-band recipient-key pin. The signed client must verify every grant against it.
    #[must_use]
    pub const fn pinned_recipient(&self) -> PublicKeyIdentity {
        self.recipient
    }

    /// Requests one recipient-signed channel grant for `caller`.
    ///
    /// This method performs one request and never follows redirects or retries failures.
    ///
    /// # Errors
    ///
    /// Returns a strict HTTP framing, endpoint-bound, or network I/O error.
    pub fn request_channel(
        &self,
        caller: PublicKeyIdentity,
    ) -> Result<Vec<u8>, HttpTransportError> {
        self.post(
            CHANNEL_PATH,
            &caller,
            MAX_CHANNEL_GRANT_BYTES,
            self.bootstrap_token.as_ref(),
        )
    }

    /// Exchanges exact canonical invocation bytes for exact signed-result bytes.
    ///
    /// This method performs one request and never follows redirects or retries failures. Any I/O
    /// error is ambiguous and the caller must abandon the pending invocation and poison its route.
    ///
    /// # Errors
    ///
    /// Returns a frame-size, strict HTTP framing, endpoint-bound, or network I/O error.
    pub fn invoke(&self, invocation: &[u8]) -> Result<Vec<u8>, HttpTransportError> {
        if invocation.len() > MAX_SIGNED_FRAME_BYTES {
            return Err(HttpTransportError::BodyTooLarge {
                limit: MAX_SIGNED_FRAME_BYTES,
                actual: invocation.len(),
            });
        }
        self.post(INVOCATION_PATH, invocation, MAX_SIGNED_FRAME_BYTES, None)
    }

    fn post(
        &self,
        path: &'static str,
        body: &[u8],
        response_limit: usize,
        bootstrap_token: Option<&BootstrapToken>,
    ) -> Result<Vec<u8>, HttpTransportError> {
        let mut stream = TcpStream::connect_timeout(&self.address, self.connect_timeout)
            .map_err(HttpTransportError::Io)?;
        stream
            .set_read_timeout(Some(self.io_timeout))
            .map_err(HttpTransportError::Io)?;
        stream
            .set_write_timeout(Some(self.io_timeout))
            .map_err(HttpTransportError::Io)?;

        let host = authority(self.address);
        let authorization = bootstrap_token.map_or_else(String::new, |token| {
            format!("Authorization: Nucleus-Bootstrap {}\r\n", encode_hex(token))
        });
        let head = format!(
            "POST {path} HTTP/1.1\r\nHost: {host}\r\nContent-Type: {BINARY_CONTENT_TYPE}\r\nContent-Length: {}\r\n{authorization}Connection: close\r\n\r\n",
            body.len()
        );
        stream
            .write_all(head.as_bytes())
            .and_then(|()| stream.write_all(body))
            .and_then(|()| stream.flush())
            .map_err(HttpTransportError::Io)?;

        let (head, headers) = read_head(&mut stream)?;
        let status = parse_response_head(&head)?;
        if status == 200 {
            require_binary_headers(&headers, &host, false)?;
            read_body(&mut stream, &headers, response_limit)
        } else {
            require_error_headers(&headers)?;
            let body = read_body(&mut stream, &headers, MAX_DIAGNOSTIC_BYTES)?;
            Err(HttpTransportError::HttpStatus {
                status,
                diagnostic: String::from_utf8_lossy(&body).into_owned(),
            })
        }
    }
}

/// A strictly framed request accepted by a loopback kernel HTTP server.
#[derive(Eq, PartialEq)]
pub enum KernelHttpRequest {
    /// Request a channel for this exact caller verification key.
    Channel {
        /// Caller verification key to bind into the recipient-signed grant.
        caller: PublicKeyIdentity,
        /// Optional one-time bootstrap capability.
        bootstrap_token: Option<BootstrapToken>,
    },
    /// Submit exact canonical signed-invocation bytes.
    Invocation(Vec<u8>),
}

impl fmt::Debug for KernelHttpRequest {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Channel {
                caller,
                bootstrap_token,
            } => formatter
                .debug_struct("Channel")
                .field("caller", caller)
                .field("has_bootstrap_token", &bootstrap_token.is_some())
                .finish(),
            Self::Invocation(bytes) => formatter
                .debug_tuple("Invocation")
                .field(&format_args!("{} bytes", bytes.len()))
                .finish(),
        }
    }
}

/// Reads one request from a connection accepted on `local_address`.
///
/// The caller should service at most this one request and then close the connection. This function
/// enforces the exact numeric `Host`, rejects transfer/content encoding, and requires a declared
/// binary body length within the endpoint-specific bound.
///
/// # Errors
///
/// Returns an error for a non-loopback listener, invalid timeout, network I/O failure, or any
/// request outside the closed and strictly bounded HTTP contract.
pub fn read_server_request(
    stream: &mut TcpStream,
    local_address: SocketAddr,
    io_timeout: Duration,
) -> Result<KernelHttpRequest, HttpTransportError> {
    if !local_address.ip().is_loopback() {
        return Err(HttpTransportError::NonLoopbackAddress(local_address));
    }
    if io_timeout.is_zero() {
        return Err(HttpTransportError::ZeroTimeout);
    }
    stream
        .set_read_timeout(Some(io_timeout))
        .map_err(HttpTransportError::Io)?;
    stream
        .set_write_timeout(Some(io_timeout))
        .map_err(HttpTransportError::Io)?;

    let (head, headers) = read_head(stream)?;
    let path = parse_request_head(&head)?;
    require_binary_headers(&headers, &authority(local_address), true)?;
    match path {
        CHANNEL_PATH => {
            let body = read_body(stream, &headers, CHANNEL_CALLER_BYTES)?;
            let caller = body.try_into().map_err(|body: Vec<u8>| {
                HttpTransportError::UnexpectedBodyLength {
                    expected: CHANNEL_CALLER_BYTES,
                    actual: body.len(),
                }
            })?;
            Ok(KernelHttpRequest::Channel {
                caller,
                bootstrap_token: parse_bootstrap_authorization(headers.authorization.as_deref())?,
            })
        }
        INVOCATION_PATH => {
            if headers.authorization.is_some() {
                return Err(HttpTransportError::UnexpectedAuthorization);
            }
            Ok(KernelHttpRequest::Invocation(read_body(
                stream,
                &headers,
                MAX_SIGNED_FRAME_BYTES,
            )?))
        }
        _ => Err(HttpTransportError::UnknownPath(path.to_owned())),
    }
}

/// Writes one successful binary response and flushes it. The connection must then be closed.
///
/// # Errors
///
/// Returns an error when `body` exceeds the signed-frame bound or writing fails.
pub fn write_server_success(stream: &mut TcpStream, body: &[u8]) -> Result<(), HttpTransportError> {
    if body.len() > MAX_SIGNED_FRAME_BYTES {
        return Err(HttpTransportError::BodyTooLarge {
            limit: MAX_SIGNED_FRAME_BYTES,
            actual: body.len(),
        });
    }
    write_response(stream, 200, "OK", BINARY_CONTENT_TYPE, body)
}

/// Writes a bounded unsigned boundary diagnostic and flushes it. Semantic service failures belong
/// in a signed successful response, not here.
///
/// # Errors
///
/// Returns an error for a non-error status, unsafe reason phrase, or network write failure.
pub fn write_server_boundary_error(
    stream: &mut TcpStream,
    status: u16,
    reason: &'static str,
    diagnostic: &str,
) -> Result<(), HttpTransportError> {
    if !(400..=599).contains(&status) {
        return Err(HttpTransportError::InvalidErrorStatus(status));
    }
    let bytes = diagnostic.as_bytes();
    let body = &bytes[..bytes.len().min(MAX_DIAGNOSTIC_BYTES)];
    write_response(stream, status, reason, TEXT_CONTENT_TYPE, body)
}

fn write_response(
    stream: &mut TcpStream,
    status: u16,
    reason: &str,
    content_type: &str,
    body: &[u8],
) -> Result<(), HttpTransportError> {
    if !reason
        .bytes()
        .all(|byte| byte == b' ' || byte.is_ascii_alphanumeric())
    {
        return Err(HttpTransportError::InvalidReasonPhrase);
    }
    let head = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream
        .write_all(head.as_bytes())
        .and_then(|()| stream.write_all(body))
        .and_then(|()| stream.flush())
        .map_err(HttpTransportError::Io)
}

#[derive(Default)]
struct Headers {
    host: Option<String>,
    content_type: Option<String>,
    content_length: Option<usize>,
    connection: Option<String>,
    transfer_encoding: bool,
    content_encoding: bool,
    authorization: Option<String>,
}

fn read_head(stream: &mut impl Read) -> Result<(String, Headers), HttpTransportError> {
    let mut head_bytes = Vec::with_capacity(512);
    let mut byte = [0_u8; 1];
    while !head_bytes.ends_with(b"\r\n\r\n") {
        if head_bytes.len() == MAX_HEADER_BYTES {
            return Err(HttpTransportError::HeadersTooLarge);
        }
        match stream.read(&mut byte) {
            Ok(0) => return Err(HttpTransportError::TruncatedHeaders),
            Ok(_) => head_bytes.push(byte[0]),
            Err(error) => return Err(HttpTransportError::Io(error)),
        }
    }
    let head = std::str::from_utf8(&head_bytes)
        .map_err(|_| HttpTransportError::NonAsciiHeaders)?
        .to_owned();
    if !head.is_ascii() {
        return Err(HttpTransportError::NonAsciiHeaders);
    }
    let headers = parse_headers(&head)?;
    Ok((head, headers))
}

fn read_body(
    stream: &mut impl Read,
    headers: &Headers,
    body_limit: usize,
) -> Result<Vec<u8>, HttpTransportError> {
    let body_length = headers
        .content_length
        .ok_or(HttpTransportError::MissingHeader("Content-Length"))?;
    if body_length > body_limit {
        return Err(HttpTransportError::BodyTooLarge {
            limit: body_limit,
            actual: body_length,
        });
    }
    let mut body = vec![0_u8; body_length];
    stream
        .read_exact(&mut body)
        .map_err(HttpTransportError::Io)?;
    Ok(body)
}

fn parse_headers(head: &str) -> Result<Headers, HttpTransportError> {
    let mut lines = head.strip_suffix("\r\n\r\n").unwrap_or(head).split("\r\n");
    let _start_line = lines.next().ok_or(HttpTransportError::MalformedStartLine)?;
    let mut headers = Headers::default();
    for line in lines {
        let (name, value) = line
            .split_once(':')
            .ok_or(HttpTransportError::MalformedHeader)?;
        if name.is_empty() || name.bytes().any(|byte| !is_header_name_byte(byte)) {
            return Err(HttpTransportError::MalformedHeader);
        }
        let value = value.trim_matches([' ', '\t']);
        if value
            .bytes()
            .any(|byte| byte.is_ascii_control() && byte != b'\t')
        {
            return Err(HttpTransportError::MalformedHeader);
        }
        if name.eq_ignore_ascii_case("host") {
            set_once(&mut headers.host, value, "Host")?;
        } else if name.eq_ignore_ascii_case("content-type") {
            set_once(&mut headers.content_type, value, "Content-Type")?;
        } else if name.eq_ignore_ascii_case("content-length") {
            if headers.content_length.is_some() || value.is_empty() {
                return Err(HttpTransportError::DuplicateHeader("Content-Length"));
            }
            if !value.bytes().all(|byte| byte.is_ascii_digit())
                || (value.len() > 1 && value.starts_with('0'))
            {
                return Err(HttpTransportError::InvalidContentLength);
            }
            headers.content_length = Some(
                value
                    .parse()
                    .map_err(|_| HttpTransportError::InvalidContentLength)?,
            );
        } else if name.eq_ignore_ascii_case("connection") {
            set_once(&mut headers.connection, value, "Connection")?;
        } else if name.eq_ignore_ascii_case("authorization") {
            set_once(&mut headers.authorization, value, "Authorization")?;
        } else if name.eq_ignore_ascii_case("transfer-encoding") {
            headers.transfer_encoding = true;
        } else if name.eq_ignore_ascii_case("content-encoding") {
            headers.content_encoding = true;
        }
    }
    Ok(headers)
}

fn set_once(
    slot: &mut Option<String>,
    value: &str,
    name: &'static str,
) -> Result<(), HttpTransportError> {
    if slot.is_some() {
        return Err(HttpTransportError::DuplicateHeader(name));
    }
    *slot = Some(value.to_owned());
    Ok(())
}

fn require_binary_headers(
    headers: &Headers,
    expected_host: &str,
    require_host: bool,
) -> Result<(), HttpTransportError> {
    reject_encodings(headers)?;
    if require_host && headers.host.as_deref() != Some(expected_host) {
        return Err(HttpTransportError::HostMismatch);
    }
    if headers.content_type.as_deref() != Some(BINARY_CONTENT_TYPE) {
        return Err(HttpTransportError::UnexpectedContentType);
    }
    if !headers
        .connection
        .as_deref()
        .is_some_and(|value| value.eq_ignore_ascii_case("close"))
    {
        return Err(HttpTransportError::ConnectionNotClose);
    }
    Ok(())
}

fn require_error_headers(headers: &Headers) -> Result<(), HttpTransportError> {
    reject_encodings(headers)?;
    if headers.content_type.as_deref() != Some(TEXT_CONTENT_TYPE) {
        return Err(HttpTransportError::UnexpectedContentType);
    }
    if !headers
        .connection
        .as_deref()
        .is_some_and(|value| value.eq_ignore_ascii_case("close"))
    {
        return Err(HttpTransportError::ConnectionNotClose);
    }
    Ok(())
}

fn reject_encodings(headers: &Headers) -> Result<(), HttpTransportError> {
    if headers.transfer_encoding {
        return Err(HttpTransportError::TransferEncodingForbidden);
    }
    if headers.content_encoding {
        return Err(HttpTransportError::ContentEncodingForbidden);
    }
    Ok(())
}

fn parse_request_head(head: &str) -> Result<&str, HttpTransportError> {
    let line = head
        .split("\r\n")
        .next()
        .ok_or(HttpTransportError::MalformedStartLine)?;
    let mut fields = line.split(' ');
    match (fields.next(), fields.next(), fields.next(), fields.next()) {
        (Some("POST"), Some(path), Some("HTTP/1.1"), None) => Ok(path),
        _ => Err(HttpTransportError::MalformedStartLine),
    }
}

fn parse_response_head(head: &str) -> Result<u16, HttpTransportError> {
    let line = head
        .split("\r\n")
        .next()
        .ok_or(HttpTransportError::MalformedStartLine)?;
    let mut fields = line.splitn(3, ' ');
    if fields.next() != Some("HTTP/1.1") {
        return Err(HttpTransportError::MalformedStartLine);
    }
    let status = fields
        .next()
        .ok_or(HttpTransportError::MalformedStartLine)?;
    if status.len() != 3 || !status.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(HttpTransportError::MalformedStartLine);
    }
    status
        .parse()
        .map_err(|_| HttpTransportError::MalformedStartLine)
}

fn authority(address: SocketAddr) -> String {
    match address {
        SocketAddr::V4(_) => address.to_string(),
        SocketAddr::V6(address) => format!("[{}]:{}", address.ip(), address.port()),
    }
}

fn parse_bootstrap_authorization(
    authorization: Option<&str>,
) -> Result<Option<BootstrapToken>, HttpTransportError> {
    let Some(value) = authorization else {
        return Ok(None);
    };
    let encoded = value
        .strip_prefix("Nucleus-Bootstrap ")
        .ok_or(HttpTransportError::InvalidAuthorization)?;
    if encoded.len() != BOOTSTRAP_TOKEN_BYTES * 2 {
        return Err(HttpTransportError::InvalidAuthorization);
    }
    let mut token = [0_u8; BOOTSTRAP_TOKEN_BYTES];
    for (destination, pair) in token.iter_mut().zip(encoded.as_bytes().chunks_exact(2)) {
        *destination = (decode_hex_digit(pair[0])? << 4) | decode_hex_digit(pair[1])?;
    }
    Ok(Some(token))
}

fn encode_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn decode_hex_digit(byte: u8) -> Result<u8, HttpTransportError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(HttpTransportError::InvalidAuthorization),
    }
}

const fn is_header_name_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || matches!(
            byte,
            b'!' | b'#'
                | b'$'
                | b'%'
                | b'&'
                | b'\''
                | b'*'
                | b'+'
                | b'-'
                | b'.'
                | b'^'
                | b'_'
                | b'`'
                | b'|'
                | b'~'
        )
}

/// Strict HTTP boundary or I/O failure.
#[derive(Debug)]
pub enum HttpTransportError {
    /// Endpoint was not a numeric loopback address.
    NonLoopbackAddress(SocketAddr),
    /// A network timeout was zero.
    ZeroTimeout,
    /// Network I/O failed; invocation failures are ambiguous and must not be retried.
    Io(io::Error),
    /// Header block exceeded the fixed bound.
    HeadersTooLarge,
    /// Peer closed before the header terminator.
    TruncatedHeaders,
    /// HTTP headers were not ASCII.
    NonAsciiHeaders,
    /// HTTP start line was not the exact supported HTTP/1.1 form.
    MalformedStartLine,
    /// A header line was malformed.
    MalformedHeader,
    /// A singleton framing header occurred more than once.
    DuplicateHeader(&'static str),
    /// A required header was absent.
    MissingHeader(&'static str),
    /// Content-Length was not one canonical unsigned decimal integer.
    InvalidContentLength,
    /// Body exceeded its endpoint-specific bound.
    BodyTooLarge { limit: usize, actual: usize },
    /// Fixed-size endpoint body had another length.
    UnexpectedBodyLength { expected: usize, actual: usize },
    /// Request Host did not exactly match the listener's numeric authority.
    HostMismatch,
    /// Content-Type was not the exact type required by the endpoint.
    UnexpectedContentType,
    /// Transfer-Encoding is unsupported and forbidden.
    TransferEncodingForbidden,
    /// Content-Encoding is unsupported and forbidden.
    ContentEncodingForbidden,
    /// Connection was not explicitly one-shot.
    ConnectionNotClose,
    /// Request path was not one of the two closed endpoints.
    UnknownPath(String),
    /// Authorization was malformed or not canonical.
    InvalidAuthorization,
    /// Authorization was supplied to an endpoint which does not accept it.
    UnexpectedAuthorization,
    /// Peer returned an unsigned HTTP boundary failure.
    HttpStatus { status: u16, diagnostic: String },
    /// Boundary-error helper was given a non-error status.
    InvalidErrorStatus(u16),
    /// Response reason phrase was unsafe for an HTTP start line.
    InvalidReasonPhrase,
}

impl fmt::Display for HttpTransportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonLoopbackAddress(address) => {
                write!(formatter, "non-loopback endpoint {address}")
            }
            Self::ZeroTimeout => formatter.write_str("HTTP timeout must be nonzero"),
            Self::Io(error) => write!(formatter, "HTTP transport I/O failed: {error}"),
            Self::HeadersTooLarge => formatter.write_str("HTTP headers exceed the fixed limit"),
            Self::TruncatedHeaders => formatter.write_str("HTTP headers were truncated"),
            Self::NonAsciiHeaders => formatter.write_str("HTTP headers must be ASCII"),
            Self::MalformedStartLine => {
                formatter.write_str("malformed or unsupported HTTP start line")
            }
            Self::MalformedHeader => formatter.write_str("malformed HTTP header"),
            Self::DuplicateHeader(name) => write!(formatter, "duplicate {name} header"),
            Self::MissingHeader(name) => write!(formatter, "missing {name} header"),
            Self::InvalidContentLength => formatter.write_str("invalid Content-Length header"),
            Self::BodyTooLarge { limit, actual } => {
                write!(formatter, "HTTP body is {actual} bytes; limit is {limit}")
            }
            Self::UnexpectedBodyLength { expected, actual } => {
                write!(
                    formatter,
                    "HTTP body is {actual} bytes; expected {expected}"
                )
            }
            Self::HostMismatch => formatter.write_str("HTTP Host does not match the listener"),
            Self::UnexpectedContentType => formatter.write_str("unexpected HTTP Content-Type"),
            Self::TransferEncodingForbidden => {
                formatter.write_str("Transfer-Encoding is forbidden")
            }
            Self::ContentEncodingForbidden => formatter.write_str("Content-Encoding is forbidden"),
            Self::ConnectionNotClose => formatter.write_str("Connection: close is required"),
            Self::UnknownPath(path) => write!(formatter, "unknown kernel HTTP path {path}"),
            Self::InvalidAuthorization => formatter.write_str("invalid bootstrap Authorization"),
            Self::UnexpectedAuthorization => {
                formatter.write_str("Authorization is not accepted on this endpoint")
            }
            Self::HttpStatus { status, diagnostic } => {
                write!(
                    formatter,
                    "kernel HTTP boundary returned {status}: {diagnostic}"
                )
            }
            Self::InvalidErrorStatus(status) => {
                write!(formatter, "invalid HTTP error status {status}")
            }
            Self::InvalidReasonPhrase => formatter.write_str("invalid HTTP reason phrase"),
        }
    }
}

impl StdError for HttpTransportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;
    use std::thread;

    #[test]
    fn rejects_non_loopback_endpoint() {
        let address = "192.0.2.1:1234".parse().unwrap();
        assert!(matches!(
            LoopbackHttpEndpoint::new(
                address,
                [0; 32],
                Duration::from_secs(1),
                Duration::from_secs(1)
            ),
            Err(HttpTransportError::NonLoopbackAddress(_))
        ));
    }

    #[test]
    fn parses_only_strict_binary_framing() {
        let input = b"POST /v0/channel HTTP/1.1\r\nHost: 127.0.0.1:7\r\nContent-Type: application/octet-stream\r\nContent-Length: 32\r\nConnection: close\r\n\r\n01234567890123456789012345678901";
        let mut input = &input[..];
        let (head, headers) = read_head(&mut input).unwrap();
        assert_eq!(parse_request_head(&head).unwrap(), CHANNEL_PATH);
        require_binary_headers(&headers, "127.0.0.1:7", true).unwrap();
        assert_eq!(
            read_body(&mut input, &headers, MAX_SIGNED_FRAME_BYTES)
                .unwrap()
                .len(),
            32
        );
    }

    #[test]
    fn rejects_duplicate_content_length() {
        let input = b"HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 0\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";
        assert!(matches!(
            read_head(&mut &input[..]),
            Err(HttpTransportError::DuplicateHeader("Content-Length"))
        ));
    }

    #[test]
    fn formats_ipv6_authority_with_brackets() {
        let address = "[::1]:4321".parse().unwrap();
        assert_eq!(authority(address), "[::1]:4321");
    }

    #[test]
    fn client_and_server_exchange_exact_one_shot_bytes() {
        let listener = match TcpListener::bind("127.0.0.1:0") {
            Ok(listener) => listener,
            Err(error) if error.kind() == io::ErrorKind::PermissionDenied => return,
            Err(error) => panic!("could not bind loopback test listener: {error}"),
        };
        let address = listener.local_addr().unwrap();
        let server = thread::spawn(move || {
            let (mut channel, _) = listener.accept().unwrap();
            assert_eq!(
                read_server_request(&mut channel, address, Duration::from_secs(1)).unwrap(),
                KernelHttpRequest::Channel {
                    caller: [7; 32],
                    bootstrap_token: Some([3; 32]),
                }
            );
            write_server_success(&mut channel, b"grant").unwrap();

            let (mut invocation, _) = listener.accept().unwrap();
            assert_eq!(
                read_server_request(&mut invocation, address, Duration::from_secs(1)).unwrap(),
                KernelHttpRequest::Invocation(b"signed invocation".to_vec())
            );
            write_server_success(&mut invocation, b"signed result").unwrap();
        });
        let endpoint = LoopbackHttpEndpoint::new(
            address,
            [9; 32],
            Duration::from_secs(1),
            Duration::from_secs(1),
        )
        .unwrap()
        .with_bootstrap_token([3; 32]);
        assert_eq!(endpoint.request_channel([7; 32]).unwrap(), b"grant");
        assert_eq!(
            endpoint.invoke(b"signed invocation").unwrap(),
            b"signed result"
        );
        server.join().unwrap();
    }
}
