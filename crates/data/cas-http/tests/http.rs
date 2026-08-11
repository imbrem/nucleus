//! The HTTP service, exercised over a real socket.
//!
//! Requests are written as raw bytes rather than through a client library:
//! what is being tested is the wire behaviour a browser will see, and a client
//! that normalises responses would hide exactly the mistakes worth catching.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::Arc;

use covalence_data_cas::MemoryCas;
use covalence_data_cas_http::{Serving, serve};
use covalence_lib_hash::O256;

/// Starts a service holding `objects`, returning it and their addresses.
fn started(objects: &[&'static [u8]]) -> (Serving, Vec<O256>) {
    let cas = Arc::new(MemoryCas::new());
    let addresses = objects
        .iter()
        .map(|bytes| cas.insert(*bytes).unwrap())
        .collect();
    let serving = serve(cas, "127.0.0.1:0".parse().unwrap()).unwrap();
    (serving, addresses)
}

/// Sends a raw request and returns (head, body).
fn request(serving: &Serving, lines: &[String]) -> (String, Vec<u8>) {
    let mut stream = TcpStream::connect(serving.address()).unwrap();
    let mut text = lines.join("\r\n");
    text.push_str("\r\n\r\n");
    stream.write_all(text.as_bytes()).unwrap();
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
    assert!(body.is_empty());
}

#[test]
fn a_multi_range_request_is_refused_rather_than_half_answered() {
    let (serving, addresses) = started(&[b"hello world"]);
    let (head, _) = get(&serving, addresses[0], &["Range: bytes=0-1,4-5"]);

    // Answering only the first range would give a client bytes it did not ask
    // for while looking like success.
    assert!(
        head.starts_with("HTTP/1.1 416 Range Not Satisfiable"),
        "{head}"
    );
}

#[test]
fn an_absent_address_is_not_found() {
    let (serving, _) = started(&[]);
    let (head, _) = get(&serving, O256::from_bytes(b"absent"), &[]);
    assert!(head.starts_with("HTTP/1.1 404 Not Found"), "{head}");
}

#[test]
fn a_malformed_address_is_not_found() {
    let (serving, _) = started(&[]);
    let (head, _) = request(
        &serving,
        &[
            "GET /cas/not-an-address HTTP/1.1".to_owned(),
            "Host: localhost".to_owned(),
            "Connection: close".to_owned(),
        ],
    );
    assert!(head.starts_with("HTTP/1.1 404 Not Found"), "{head}");
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
