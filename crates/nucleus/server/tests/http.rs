use std::io::{Read, Write};
use std::net::TcpStream;
use std::sync::Arc;

use covalence_nucleus_server::{NucleusServer, Serving};

fn request(serving: &Serving, request: &[u8]) -> (String, Vec<u8>) {
    let mut stream = TcpStream::connect(serving.address()).unwrap();
    stream.write_all(request).unwrap();
    stream.flush().unwrap();
    let mut response = Vec::new();
    stream.read_to_end(&mut response).unwrap();
    let split = response
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .unwrap();
    (
        String::from_utf8_lossy(&response[..split]).into_owned(),
        response[split + 4..].to_vec(),
    )
}

#[test]
fn serves_kernel_observation_and_composed_cas_routes() {
    let server = Arc::new(NucleusServer::empty());
    let serving = server.serve("127.0.0.1:0".parse().unwrap()).unwrap();

    let (head, body) = request(
        &serving,
        b"GET /nucleus HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n",
    );
    assert!(head.starts_with("HTTP/1.1 200 OK"), "{head}");
    let body = String::from_utf8(body).unwrap();
    assert!(body.contains("\"rows\":0"), "{body}");
    assert!(
        body.contains(&server.kernel().addr().hex().to_string()),
        "{body}"
    );

    let payload = b"nucleus server CAS";
    let request_head = format!(
        "PUT /cas/upload HTTP/1.1\r\nHost: localhost\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        payload.len()
    );
    let mut bytes = request_head.into_bytes();
    bytes.extend_from_slice(payload);
    let (head, _) = request(&serving, &bytes);
    assert!(head.starts_with("HTTP/1.1 201 Created"), "{head}");
    assert!(
        server
            .cas()
            .contains(covalence_lib_hash::O256::from_bytes(payload))
    );
}
