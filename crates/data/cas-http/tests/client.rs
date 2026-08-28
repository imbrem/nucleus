//! Async HTTP CAS client tests over deterministic local servers.

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::Arc;

use covalence_data_cas::{
    AsyncCas, AsyncCasError, ByteRange, CasService, RangePart, SharedIndexCas,
};
use covalence_data_cas_http::{HttpCas, HttpCasError, serve};
use covalence_lib_hash::O256;

#[test]
fn rejects_non_http_urls_at_configuration_time() {
    assert!(matches!(
        HttpCas::new("ftp://example.invalid/not-a-service"),
        Err(HttpCasError::UnsupportedScheme { .. })
    ));
}

#[test]
fn fetches_raw_bytes_and_a_checked_fact() {
    let source = Arc::new(SharedIndexCas::new());
    let address = source.insert(b"from HTTP" as &[u8]).unwrap();
    let serving = serve(source, "127.0.0.1:0".parse().unwrap()).unwrap();
    let client = HttpCas::new(&serving.base_url()).unwrap();

    run(async {
        assert_eq!(
            client.get_bytes(address).await.unwrap().unwrap(),
            b"from HTTP" as &[u8]
        );
        let provider: &dyn AsyncCas = &client;
        let fact = provider.get_fact(address).await.unwrap().unwrap();
        assert_eq!(fact.hash(), address);
        assert_eq!(fact.bytes(), b"from HTTP" as &[u8]);
    });
}

#[test]
fn absent_objects_are_not_errors() {
    let source = Arc::new(SharedIndexCas::new());
    let serving = serve(source, "127.0.0.1:0".parse().unwrap()).unwrap();
    let client = HttpCas::new(&serving.base_url()).unwrap();

    run(async {
        assert!(
            client
                .get_bytes(O256::from_bytes(b"absent"))
                .await
                .unwrap()
                .is_none()
        );
    });
}

#[test]
fn corrupt_successful_responses_remain_untrusted_bytes() {
    let address = O256::from_bytes(b"expected");
    let (base, server) = fixed_server("200 OK", b"different");
    let client = HttpCas::new(&base).unwrap();

    run(async {
        assert_eq!(
            client.get_bytes(address).await.unwrap().unwrap(),
            b"different" as &[u8]
        );
    });
    server.join().unwrap();
}

#[test]
fn shared_default_fact_lookup_rejects_corrupt_responses() {
    let address = O256::from_bytes(b"expected");
    let (base, server) = fixed_server("200 OK", b"different");
    let client = HttpCas::new(&base).unwrap();
    let provider: &dyn AsyncCas = &client;

    run(async {
        assert!(matches!(
            provider.get_fact(address).await,
            Err(AsyncCasError::Check { .. })
        ));
    });
    server.join().unwrap();
}

#[test]
fn responses_without_a_length_are_still_bounded() {
    let address = O256::from_bytes(b"address is irrelevant");
    let (base, server) = fixed_server("200 OK", &[0; 17]);
    let client = HttpCas::new(&base).unwrap().with_max_object_bytes(16);

    run(async {
        assert!(matches!(
            client.get_bytes(address).await,
            Err(HttpCasError::TooLarge { limit: 16, .. })
        ));
    });
    server.join().unwrap();
}

#[test]
fn declared_oversized_responses_are_rejected() {
    let address = O256::from_bytes(b"address is irrelevant");
    let (base, server) = declared_server("200 OK", 17, "", b"");
    let client = HttpCas::new(&base).unwrap().with_max_object_bytes(16);

    run(async {
        assert!(matches!(
            client.get_bytes(address).await,
            Err(HttpCasError::TooLarge { limit: 16, .. })
        ));
    });
    server.join().unwrap();
}

#[test]
fn redirects_are_not_followed() {
    let address = O256::from_bytes(b"address is irrelevant");
    let (base, server) = declared_server(
        "302 Found",
        0,
        "Location: http://127.0.0.1:1/escaped\r\n",
        b"",
    );
    let client = HttpCas::new(&base).unwrap();

    run(async {
        assert!(matches!(
            client.get_bytes(address).await,
            Err(HttpCasError::Status { status, .. }) if status.as_u16() == 302
        ));
    });
    server.join().unwrap();
}

#[test]
fn server_failures_are_not_reported_as_absence() {
    let address = O256::from_bytes(b"address is irrelevant");
    let (base, server) = fixed_server("500 Internal Server Error", &[]);
    let client = HttpCas::new(&base).unwrap();

    run(async {
        assert!(matches!(
            client.get_bytes(address).await,
            Err(HttpCasError::Status { status, .. }) if status.as_u16() == 500
        ));
    });
    server.join().unwrap();
}

#[test]
fn multiple_ranges_use_one_http_request() {
    let address = O256::from_bytes(b"batch address");
    let boundary = "batch-boundary";
    let body = format!(
        "--{boundary}\r\nContent-Type: application/octet-stream\r\nContent-Range: bytes 0-1/8\r\n\r\nab\r\n--{boundary}\r\nContent-Type: application/octet-stream\r\nContent-Range: bytes 5-7/8\r\n\r\nfgh\r\n--{boundary}--\r\n"
    );
    let (base, server) = range_server(boundary, body.into_bytes());
    let client = HttpCas::new(&base).unwrap();

    run(async {
        let result = client
            .get_ranges(
                address,
                vec![ByteRange::Bounded(0..2), ByteRange::Bounded(5..8)],
            )
            .await
            .unwrap()
            .unwrap();
        assert_eq!(result.len, 8);
        assert_eq!(
            result.parts,
            [
                RangePart {
                    range: 0..2,
                    bytes: b"ab".as_slice().into(),
                },
                RangePart {
                    range: 5..8,
                    bytes: b"fgh".as_slice().into(),
                },
            ]
        );
    });
    server.join().unwrap();
}

fn run(future: impl Future<Output = ()>) {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(future);
}

/// Starts a one-request server without framework response normalization.
///
/// In particular it omits `Content-Length`, exercising the streaming size
/// limit rather than only the early header check.
fn fixed_server(
    status: &'static str,
    body: &'static [u8],
) -> (String, std::thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let address = listener.local_addr().unwrap();
    let task = std::thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        let mut request = [0; 4096];
        let _ = stream.read(&mut request).unwrap();
        write!(stream, "HTTP/1.1 {status}\r\nConnection: close\r\n\r\n").unwrap();
        stream.write_all(body).unwrap();
    });
    (format!("http://{address}"), task)
}

/// Starts a one-request server with an explicit declared response length.
fn declared_server(
    status: &'static str,
    content_length: u64,
    headers: &'static str,
    body: &'static [u8],
) -> (String, std::thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let address = listener.local_addr().unwrap();
    let task = std::thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        let mut request = [0; 4096];
        let _ = stream.read(&mut request).unwrap();
        write!(
            stream,
            "HTTP/1.1 {status}\r\nContent-Length: {content_length}\r\n{headers}Connection: close\r\n\r\n"
        )
        .unwrap();
        stream.write_all(body).unwrap();
    });
    (format!("http://{address}"), task)
}

fn range_server(boundary: &'static str, body: Vec<u8>) -> (String, std::thread::JoinHandle<()>) {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let address = listener.local_addr().unwrap();
    let task = std::thread::spawn(move || {
        let (mut stream, _) = listener.accept().unwrap();
        let mut request = [0; 4096];
        let count = stream.read(&mut request).unwrap();
        let request = String::from_utf8_lossy(&request[..count]).to_ascii_lowercase();
        assert!(request.contains("range: bytes=0-1,5-7\r\n"), "{request}");
        write!(
            stream,
            "HTTP/1.1 206 Partial Content\r\nContent-Type: multipart/byteranges; boundary={boundary}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
            body.len()
        )
        .unwrap();
        stream.write_all(&body).unwrap();
    });
    (format!("http://{address}"), task)
}
