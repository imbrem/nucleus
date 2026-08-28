//! The HTTP service, exercised over a real socket.
//!
//! Requests are written as raw bytes rather than through a client library:
//! what is being tested is the wire behaviour a browser will see, and a client
//! that normalises responses would hide exactly the mistakes worth catching.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::Arc;

use covalence_data_cas::SharedIndexCas;
use covalence_data_cas_http::{HttpCas, Serving, serve};
use covalence_lib_hash::O256;

/// Starts a service holding `objects`, returning it and their addresses.
fn started(objects: &[&'static [u8]]) -> (Serving, Vec<O256>) {
    let cas = Arc::new(SharedIndexCas::new());
    let addresses = objects
        .iter()
        .map(|bytes| cas.insert(*bytes).unwrap())
        .collect();
    let serving = serve(cas, "127.0.0.1:0".parse().unwrap()).unwrap();
    (serving, addresses)
}

/// Sends a raw request and returns (head, body).
fn request(serving: &Serving, lines: &[String]) -> (String, Vec<u8>) {
    request_with_body(serving, lines, &[])
}

fn request_with_body(
    serving: &Serving,
    lines: &[String],
    request_body: &[u8],
) -> (String, Vec<u8>) {
    let mut stream = TcpStream::connect(serving.address()).unwrap();
    let mut text = lines.join("\r\n");
    text.push_str("\r\n\r\n");
    stream.write_all(text.as_bytes()).unwrap();
    stream.write_all(request_body).unwrap();
    stream.flush().unwrap();

    let mut response = Vec::new();
    stream.read_to_end(&mut response).unwrap();

    let split = response
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .expect("a response has a blank line after its head");
    (
        String::from_utf8_lossy(&response[..split]).into_owned(),
        response[split + 4..].to_vec(),
    )
}

fn get(serving: &Serving, address: O256, extra: &[&str]) -> (String, Vec<u8>) {
    let mut lines = vec![
        format!("GET /cas/{} HTTP/1.1", address.hex()),
        "Host: localhost".to_owned(),
        "Connection: close".to_owned(),
    ];
    lines.extend(extra.iter().map(|line| (*line).to_owned()));
    request(serving, &lines)
}

#[test]
fn serves_a_whole_object() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = get(&serving, addresses[0], &[]);

    assert!(head.starts_with("HTTP/1.1 200 OK"), "{head}");
    assert_eq!(body, b"hello world");
    assert!(head.contains("accept-ranges: bytes"), "{head}");
    // A content address names fixed bytes, so this is cacheable forever.
    assert!(head.contains("immutable"), "{head}");
}

#[test]
fn serves_an_exact_range() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = get(&serving, addresses[0], &["Range: bytes=6-10"]);

    assert!(head.starts_with("HTTP/1.1 206 Partial Content"), "{head}");
    // `Content-Range` is inclusive at both ends.
    assert!(head.contains("content-range: bytes 6-10/11"), "{head}");
    assert_eq!(body, b"world");
}

#[test]
fn an_open_ended_range_runs_to_the_end() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = get(&serving, addresses[0], &["Range: bytes=6-"]);

    assert!(head.contains("content-range: bytes 6-10/11"), "{head}");
    assert_eq!(body, b"world");
}

#[test]
fn a_suffix_range_counts_from_the_end() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = get(&serving, addresses[0], &["Range: bytes=-5"]);

    assert!(head.starts_with("HTTP/1.1 206 Partial Content"), "{head}");
    assert_eq!(body, b"world");
}

#[test]
fn a_range_past_the_end_is_unsatisfiable() {
    let (serving, addresses) = started(&[b"hello"]);
    let (head, body) = get(&serving, addresses[0], &["Range: bytes=99-100"]);

    assert!(
        head.starts_with("HTTP/1.1 416 Range Not Satisfiable"),
        "{head}"
    );
    // The client is told how long the object actually is.
    assert!(head.contains("content-range: bytes */5"), "{head}");
    assert!(String::from_utf8_lossy(&body).contains("range_not_satisfiable"));
}

#[test]
fn a_multi_range_request_returns_standard_multipart_bytes() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = get(&serving, addresses[0], &["Range: bytes=0-1,4-5"]);

    assert!(head.starts_with("HTTP/1.1 206 Partial Content"), "{head}");
    assert!(head.contains("multipart/byteranges"), "{head}");
    let body = String::from_utf8_lossy(&body);
    assert!(body.contains("Content-Range: bytes 0-1/11"), "{body}");
    assert!(body.contains("\r\nhe\r\n"), "{body}");
    assert!(body.contains("Content-Range: bytes 4-5/11"), "{body}");
    assert!(body.contains("\r\no \r\n"), "{body}");
}

#[test]
fn an_absent_address_is_not_found() {
    let (serving, _) = started(&[]);
    let (head, _) = get(&serving, O256::from_bytes(b"absent"), &[]);
    assert!(head.starts_with("HTTP/1.1 404 Not Found"), "{head}");
}

#[test]
fn a_malformed_address_is_a_clear_client_error() {
    let (serving, _) = started(&[]);
    let (head, _) = request(
        &serving,
        &[
            "GET /cas/not-an-address HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.starts_with("HTTP/1.1 400 Bad Request"), "{head}");
}

#[test]
fn head_reports_the_length_without_a_body() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, body) = request(
        &serving,
        &[
            format!("HEAD /cas/{} HTTP/1.1", addresses[0].hex()),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );

    assert!(head.starts_with("HTTP/1.1 200 OK"), "{head}");
    assert!(head.contains("content-length: 11"), "{head}");
    assert!(body.is_empty(), "HEAD must not carry a body");
}

#[test]
fn writes_are_refused() {
    let (serving, addresses) = started(&[b"hello"]);
    let (head, _) = request(
        &serving,
        &[
            format!("PUT /cas/{} HTTP/1.1", addresses[0].hex()),
            "Host: localhost".to_owned(),
            "Content-Length: 0".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.starts_with("HTTP/1.1 405"), "{head}");
}

#[test]
fn put_upload_hashes_and_admits_streamed_bytes() {
    let (serving, _) = started(&[]);
    let payload = b"uploaded through the service";
    let (head, body) = request_with_body(
        &serving,
        &[
            "PUT /cas/upload HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            format!("Content-Length: {}", payload.len()),
            "Connection: close".to_owned(),
        ],
        payload,
    );
    let address = O256::from_bytes(payload);
    assert!(head.starts_with("HTTP/1.1 201 Created"), "{head}");
    assert!(
        head.contains(&format!("location: /cas/blake3/{}", address.hex())),
        "{head}"
    );
    assert!(String::from_utf8_lossy(&body).contains(&address.hex().to_string()));
    assert_eq!(get(&serving, address, &[]).1, payload);
}

#[test]
fn post_upload_is_the_conventional_alias() {
    let (serving, _) = started(&[]);
    let payload = b"post upload";
    let (head, _) = request_with_body(
        &serving,
        &[
            "POST /cas/upload HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            format!("Content-Length: {}", payload.len()),
            "Connection: close".to_owned(),
        ],
        payload,
    );
    assert!(head.starts_with("HTTP/1.1 201 Created"), "{head}");
}

#[test]
fn verified_put_accepts_only_the_addressed_bytes() {
    let (serving, _) = started(&[]);
    let payload = b"verified upload";
    let address = O256::from_bytes(payload);
    let path = format!("/cas/blake3/{}", address.hex());
    let (head, _) = request_with_body(
        &serving,
        &[
            format!("PUT {path} HTTP/1.1"),
            "Host: localhost".to_owned(),
            format!("Content-Length: {}", payload.len()),
            "Connection: close".to_owned(),
        ],
        payload,
    );
    assert!(head.starts_with("HTTP/1.1 200 OK"), "{head}");

    let wrong = O256::from_bytes(b"another object");
    let (head, body) = request_with_body(
        &serving,
        &[
            format!("PUT /cas/blake3/{} HTTP/1.1", wrong.hex()),
            "Host: localhost".to_owned(),
            format!("Content-Length: {}", payload.len()),
            "Connection: close".to_owned(),
        ],
        payload,
    );
    assert!(
        head.starts_with("HTTP/1.1 422 Unprocessable Entity"),
        "{head}"
    );
    assert!(String::from_utf8_lossy(&body).contains("hash_mismatch"));
}

#[test]
fn unsupported_hash_algorithms_are_explicit() {
    let (serving, _) = started(&[]);
    let (head, body) = request(
        &serving,
        &[
            "GET /cas/sha256/00 HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.starts_with("HTTP/1.1 501 Not Implemented"), "{head}");
    assert!(String::from_utf8_lossy(&body).contains("unsupported_hash_algorithm"));
}

#[test]
fn a_unique_hash_prefix_redirects_to_the_canonical_full_address() {
    let (serving, addresses) = started(&[b"prefix-addressed object"]);
    let full = addresses[0].hex().to_string();
    let prefix = &full[..12];
    let (head, body) = request(
        &serving,
        &[
            format!("GET /cas/blake3/{prefix} HTTP/1.1"),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(
        head.starts_with("HTTP/1.1 307 Temporary Redirect"),
        "{head}"
    );
    assert!(
        head.contains(&format!("location: /cas/blake3/{full}")),
        "{head}"
    );
    assert!(head.contains("cache-control: no-store"), "{head}");
    assert!(body.is_empty());
}

#[test]
fn address_prefixes_have_a_minimum_length() {
    let (serving, _) = started(&[]);
    let (head, body) = request(
        &serving,
        &[
            "GET /cas/blake3/abcd HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.starts_with("HTTP/1.1 400 Bad Request"), "{head}");
    assert!(String::from_utf8_lossy(&body).contains("hash_prefix_too_short"));
}

#[test]
fn an_http_cas_can_be_reexposed_as_a_proxy_without_special_code() {
    let upstream_cas = Arc::new(SharedIndexCas::new());
    let upstream = serve(Arc::clone(&upstream_cas), "127.0.0.1:0".parse().unwrap()).unwrap();
    let remote = Arc::new(HttpCas::new(&upstream.base_url()).unwrap());
    let proxy = serve(remote, "127.0.0.1:0".parse().unwrap()).unwrap();
    let payload = b"composed through an HTTP CAS";

    let (head, _) = request_with_body(
        &proxy,
        &[
            "PUT /cas/upload HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            format!("Content-Length: {}", payload.len()),
            "Connection: close".to_owned(),
        ],
        payload,
    );
    assert!(head.starts_with("HTTP/1.1 201 Created"), "{head}");
    let address = O256::from_bytes(payload);
    assert!(upstream_cas.contains(address));
    assert_eq!(get(&proxy, address, &[]).1, payload);

    let full = address.hex().to_string();
    let (head, _) = request(
        &proxy,
        &[
            format!("GET /cas/blake3/{} HTTP/1.1", &full[..12]),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(
        head.starts_with("HTTP/1.1 307 Temporary Redirect"),
        "{head}"
    );
    assert!(
        head.contains(&format!("location: /cas/blake3/{full}")),
        "{head}"
    );
}

#[test]
fn a_cross_origin_page_may_read_and_may_send_range() {
    let (serving, addresses) = started(&[b"hello world"]);

    let (head, _) = request(
        &serving,
        &[
            format!("OPTIONS /cas/{} HTTP/1.1", addresses[0].hex()),
            "Host: localhost".to_owned(),
            "Origin: http://localhost:8000".to_owned(),
            "Access-Control-Request-Method: GET".to_owned(),
            "Access-Control-Request-Headers: range".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.contains("access-control-allow-origin"), "{head}");

    // And the response a browser reads must expose the range headers, or the
    // page cannot tell what it was given.
    let (head, _) = get(
        &serving,
        addresses[0],
        &["Origin: http://localhost:8000", "Range: bytes=0-4"],
    );
    assert!(head.contains("access-control-expose-headers"), "{head}");
    assert!(head.to_lowercase().contains("content-range"), "{head}");
}

#[test]
fn the_bytes_served_hash_to_the_address_requested() {
    // The property a client must check, checked here so a regression in the
    // server shows up as a server test rather than a mysterious client error.
    let payload = b"the quick brown fox";
    let (serving, addresses) = started(&[payload]);
    let (_, body) = get(&serving, addresses[0], &[]);

    assert_eq!(O256::from_bytes(&body), addresses[0]);
}

#[test]
fn dropping_the_service_stops_it() {
    let (serving, addresses) = started(&[b"hello"]);
    let address = serving.address();
    assert!(
        get(&serving, addresses[0], &[])
            .0
            .starts_with("HTTP/1.1 200")
    );

    drop(serving);

    // Graceful shutdown is not instant; the connection must fail before long.
    let refused = (0..50).any(|_| {
        std::thread::sleep(std::time::Duration::from_millis(20));
        TcpStream::connect(address).is_err()
    });
    assert!(
        refused,
        "the port must stop accepting once the service drops"
    );
}
