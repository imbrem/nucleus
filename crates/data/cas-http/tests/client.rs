//! Async HTTP CAS client tests over deterministic local servers.

use std::io::{Read, Write};
use std::net::TcpListener;
use std::sync::Arc;

use covalence_data_cas::{AsyncCas, AsyncCasError, SharedIndexCas};
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
