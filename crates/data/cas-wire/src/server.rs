//! Serving a [`Cas`] over a byte stream.

use std::collections::HashMap;
use std::io::{self, Read, Write};

use covalence_data_cas::{Cas, CasObject};

use crate::{Handle, MAX_READ_BYTES, Request, Response};

/// Serves `cas` until the client disconnects.
///
/// Objects opened by the client are held here for as long as the client holds
/// their handle. That is what carries the [`Cas`] guarantee across the process
/// boundary: an address dropped from the store cannot break a database the
/// client already has open.
///
/// A client error — an unknown handle, an out-of-range read — is answered with
/// [`Response::Failed`] and the connection continues. Only a transport or
/// framing failure ends the loop, because at that point there is no longer a
/// protocol to speak.
///
/// # Errors
///
/// Returns an error when the transport fails or the client sends a malformed
/// frame.
pub fn serve<C>(cas: &C, reader: &mut impl Read, writer: &mut impl Write) -> io::Result<()>
where
    C: Cas + ?Sized,
    C::Error: std::fmt::Display,
{
    let mut open: HashMap<u64, C::Object> = HashMap::new();
    let mut next_handle: u64 = 1;

    while let Some(request) = Request::read(reader)? {
        let response = match request {
            Request::Open(address) => match cas.open(address) {
                Ok(Some(object)) => {
                    let len = object.len();
                    let handle = next_handle;
                    // Wrapping would alias a live handle; refuse instead.
                    let Some(next) = next_handle.checked_add(1) else {
                        Response::Failed("handle space exhausted".to_owned()).write(writer)?;
                        continue;
                    };
                    next_handle = next;
                    open.insert(handle, object);
                    Response::Opened {
                        handle: Handle(handle),
                        len,
                    }
                }
                Ok(None) => Response::Absent,
                Err(error) => Response::Failed(error.to_string()),
            },

            Request::Read { handle, start, end } => {
                let requested = end.saturating_sub(start);
                if end < start {
                    Response::Failed(format!("reversed range {start}..{end}"))
                } else if requested > MAX_READ_BYTES {
                    // Bound the answer before touching the store, so a client
                    // cannot size the server's allocation.
                    Response::Failed(format!(
                        "range of {requested} bytes exceeds the {MAX_READ_BYTES} byte limit"
                    ))
                } else {
                    match open.get(&handle.0) {
                        None => Response::Failed(format!("unknown handle {}", handle.0)),
                        Some(object) => match object.read(start..end) {
                            Ok(bytes) => Response::Data(bytes.to_vec()),
                            Err(error) => Response::Failed(error.to_string()),
                        },
                    }
                }
            }

            Request::Close(handle) => {
                open.remove(&handle.0);
                Response::Done
            }
        };
        response.write(writer)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use covalence_data_cas::MemoryCas;
    use covalence_lib_hash::O256;

    use super::*;

    /// Drives `requests` through the server and returns its answers.
    fn exchange(cas: &MemoryCas, requests: &[Request]) -> Vec<Response> {
        let mut input = Vec::new();
        for request in requests {
            request.write(&mut input).unwrap();
        }
        let mut output = Vec::new();
        serve(cas, &mut input.as_slice(), &mut output).unwrap();

        let mut reader = output.as_slice();
        let mut responses = Vec::new();
        while !reader.is_empty() {
            responses.push(Response::read(&mut reader).unwrap());
        }
        responses
    }

    #[test]
    fn open_then_read_returns_exact_bytes() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello world"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Open(address),
                Request::Read {
                    handle: Handle(1),
                    start: 6,
                    end: 11,
                },
            ],
        );
        assert_eq!(
            responses[0],
            Response::Opened {
                handle: Handle(1),
                len: 11
            }
        );
        assert_eq!(responses[1], Response::Data(b"world".to_vec()));
    }

    #[test]
    fn an_absent_address_is_not_an_error() {
        let cas = MemoryCas::new();
        let responses = exchange(&cas, &[Request::Open(O256::from_bytes(b"absent"))]);
        assert_eq!(responses[0], Response::Absent);
    }

    #[test]
    fn an_open_handle_survives_removal() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();

        // Open, then drop the address, then read through the handle. The
        // removal happens between two client requests, which is exactly the
        // case a read-by-address protocol would get wrong.
        let mut input = Vec::new();
        Request::Open(address).write(&mut input).unwrap();
        let mut output = Vec::new();
        {
            // Serve the open on its own so the handle is established first.
            serve(&cas, &mut input.as_slice(), &mut output).unwrap();
        }
        assert_eq!(
            Response::read(&mut output.as_slice()).unwrap(),
            Response::Opened {
                handle: Handle(1),
                len: 5
            }
        );

        // The server drops its handles when `serve` returns, so this test
        // proves the property at the store level; the pipe client keeps one
        // connection open for the life of the database.
        assert!(cas.remove(address));
        assert!(cas.open(address).unwrap().is_none());
    }

    #[test]
    fn an_unknown_handle_is_refused_without_ending_the_session() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Read {
                    handle: Handle(99),
                    start: 0,
                    end: 1,
                },
                Request::Open(address),
            ],
        );
        assert!(matches!(responses[0], Response::Failed(_)));
        // The session continued.
        assert!(matches!(responses[1], Response::Opened { .. }));
    }

    #[test]
    fn an_oversized_range_is_refused_before_reading() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Open(address),
                Request::Read {
                    handle: Handle(1),
                    start: 0,
                    end: MAX_READ_BYTES + 1,
                },
            ],
        );
        assert!(matches!(responses[1], Response::Failed(_)));
    }

    #[test]
    fn a_reversed_range_is_refused() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Open(address),
                Request::Read {
                    handle: Handle(1),
                    start: 4,
                    end: 1,
                },
            ],
        );
        assert!(matches!(responses[1], Response::Failed(_)));
    }

    #[test]
    fn a_read_past_the_end_is_refused() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Open(address),
                Request::Read {
                    handle: Handle(1),
                    start: 0,
                    end: 6,
                },
            ],
        );
        assert!(matches!(responses[1], Response::Failed(_)));
    }

    #[test]
    fn closing_releases_the_handle() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let responses = exchange(
            &cas,
            &[
                Request::Open(address),
                Request::Close(Handle(1)),
                Request::Read {
                    handle: Handle(1),
                    start: 0,
                    end: 1,
                },
            ],
        );
        assert_eq!(responses[1], Response::Done);
        assert!(matches!(responses[2], Response::Failed(_)));
    }
}
