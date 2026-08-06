//! A [`Cas`] backed by a server on the other end of a byte stream.

use std::io::{self, Read, Write};
use std::ops::Range;
use std::sync::{Arc, Mutex};

use bytes::Bytes;
use covalence_data_cas::{Cas, CasObject};
use covalence_lib_hash::O256;

use crate::{Handle, Request, Response};

/// A transport carrying the CAS protocol.
///
/// The two halves are separate because the common case is a pair of pipes
/// rather than one duplex object.
pub struct Transport<R, W> {
    reader: R,
    writer: W,
}

impl<R: Read, W: Write> Transport<R, W> {
    /// Pairs a reader and a writer.
    pub const fn new(reader: R, writer: W) -> Self {
        Self { reader, writer }
    }

    /// Sends one request and waits for its answer.
    fn exchange(&mut self, request: &Request) -> io::Result<Response> {
        request.write(&mut self.writer)?;
        Response::read(&mut self.reader)
    }
}

/// A CAS served by another process.
///
/// # Why the transport is behind a mutex
///
/// The protocol is strictly one request, one answer, on one stream, with
/// nothing in a response identifying which request it answers. `Cas::open` and
/// `CasObject::read` both take `&self`, and `SQLite` may hold several files
/// open on one connection, so two callers sharing this client could otherwise
/// interleave frames and each read the other's answer. The mutex is the
/// smallest thing that makes that impossible.
///
/// It is also a bottleneck, and a deliberate one for now: the shell is
/// single-threaded, so it costs nothing here. Removing it means either request
/// identifiers plus a demultiplexing reader, or one connection per object —
/// and neither is worth building before something concurrent needs it. A
/// stateless request-per-read transport such as ranged HTTP would not need it
/// at all, at the cost of the handle guarantee this protocol exists to carry.
pub struct RemoteCas<R, W> {
    transport: Arc<Mutex<Transport<R, W>>>,
}

impl<R: Read, W: Write> RemoteCas<R, W> {
    /// Wraps a transport.
    pub fn new(transport: Transport<R, W>) -> Self {
        Self {
            transport: Arc::new(Mutex::new(transport)),
        }
    }

    fn exchange(&self, request: &Request) -> Result<Response, RemoteError> {
        let mut transport = self
            .transport
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        transport.exchange(request).map_err(RemoteError::Transport)
    }
}

/// Failure to obtain bytes from a remote store.
#[derive(Debug)]
pub enum RemoteError {
    /// The transport failed.
    Transport(io::Error),
    /// The server refused. Diagnostic only.
    Refused(String),
    /// The server answered something the protocol does not allow here.
    Unexpected,
}

impl std::fmt::Display for RemoteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Transport(error) => write!(formatter, "CAS transport failed: {error}"),
            Self::Refused(message) => write!(formatter, "CAS server refused: {message}"),
            Self::Unexpected => formatter.write_str("CAS server broke protocol"),
        }
    }
}

impl std::error::Error for RemoteError {}

/// An object held open by the server.
///
/// Dropping it tells the server to release its handle. Until then the server
/// holds the object, so reads keep working even if the address is dropped from
/// the store — the guarantee survives the process boundary.
pub struct RemoteObject<R: Read, W: Write> {
    transport: Arc<Mutex<Transport<R, W>>>,
    handle: Handle,
    len: u64,
}

impl<R: Read, W: Write> Cas for RemoteCas<R, W>
where
    R: Send + Sync,
    W: Send + Sync,
{
    type Error = RemoteError;
    type Object = RemoteObject<R, W>;

    fn open(&self, address: O256) -> Result<Option<Self::Object>, Self::Error> {
        match self.exchange(&Request::Open(address))? {
            Response::Opened { handle, len } => Ok(Some(RemoteObject {
                transport: Arc::clone(&self.transport),
                handle,
                len,
            })),
            Response::Absent => Ok(None),
            Response::Failed(message) => Err(RemoteError::Refused(message)),
            _ => Err(RemoteError::Unexpected),
        }
    }
}

impl<R: Read, W: Write> CasObject for RemoteObject<R, W>
where
    R: Send + Sync,
    W: Send + Sync,
{
    type Error = RemoteError;

    fn len(&self) -> u64 {
        self.len
    }

    fn read(&self, range: Range<u64>) -> Result<Bytes, Self::Error> {
        let expected = range.end.saturating_sub(range.start);
        let response = {
            let mut transport = self
                .transport
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            transport
                .exchange(&Request::Read {
                    handle: self.handle,
                    start: range.start,
                    end: range.end,
                })
                .map_err(RemoteError::Transport)?
        };
        match response {
            Response::Data(bytes) => {
                // The server is not trusted to answer the question that was
                // asked; a short read must not become a silently short page.
                if bytes.len() as u64 != expected {
                    return Err(RemoteError::Unexpected);
                }
                Ok(Bytes::from(bytes))
            }
            Response::Failed(message) => Err(RemoteError::Refused(message)),
            _ => Err(RemoteError::Unexpected),
        }
    }
}

impl<R: Read, W: Write> Drop for RemoteObject<R, W> {
    fn drop(&mut self) {
        let mut transport = self
            .transport
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Nothing useful to do on failure: the server releases everything when
        // the connection ends anyway.
        let _ = transport.exchange(&Request::Close(self.handle));
    }
}

#[cfg(test)]
mod tests {
    use covalence_data_cas::MemoryCas;

    use super::*;
    use crate::server::serve;

    /// Runs a server on one thread and gives the caller a client.
    fn connected(cas: MemoryCas) -> RemoteCas<os_pipe::PipeReader, os_pipe::PipeWriter> {
        let (to_server_reader, mut to_server_writer) = os_pipe::pipe().unwrap();
        let (from_server_reader, mut from_server_writer) = os_pipe::pipe().unwrap();
        std::thread::spawn(move || {
            let mut reader = to_server_reader;
            let _ = serve(&cas, &mut reader, &mut from_server_writer);
        });
        let _ = &mut to_server_writer;
        RemoteCas::new(Transport::new(from_server_reader, to_server_writer))
    }

    #[test]
    fn reads_through_the_transport() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello world"[..]).unwrap();
        let client = connected(cas);

        let object = client.open(address).unwrap().unwrap();
        assert_eq!(object.len(), 11);
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
        assert_eq!(object.read(6..11).unwrap(), Bytes::from_static(b"world"));
    }

    #[test]
    fn an_absent_address_is_none() {
        let cas = MemoryCas::new();
        let client = connected(cas);
        assert!(client.open(O256::from_bytes(b"absent")).unwrap().is_none());
    }

    #[test]
    fn an_object_held_by_the_client_survives_removal_in_the_server() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello world"[..]).unwrap();
        // The server keeps its own handle on the store, so removal here is
        // exactly what a REPL's `.forget` does while a shell is attached.
        let store = std::sync::Arc::new(cas);

        let (to_server_reader, to_server_writer) = os_pipe::pipe().unwrap();
        let (from_server_reader, mut from_server_writer) = os_pipe::pipe().unwrap();
        let served = std::sync::Arc::clone(&store);
        std::thread::spawn(move || {
            let mut reader = to_server_reader;
            let _ = serve(served.as_ref(), &mut reader, &mut from_server_writer);
        });
        let client = RemoteCas::new(Transport::new(from_server_reader, to_server_writer));

        let object = client.open(address).unwrap().unwrap();
        assert!(store.remove(address));

        // The handle still reads. This is the property the handle protocol
        // exists for, now demonstrated across a real pipe.
        assert_eq!(object.read(0..5).unwrap(), Bytes::from_static(b"hello"));
        // A fresh open does not resolve.
        assert!(client.open(address).unwrap().is_none());
    }

    #[test]
    fn a_refused_read_is_an_error_not_short_data() {
        let cas = MemoryCas::new();
        let address = cas.insert(&b"hello"[..]).unwrap();
        let client = connected(cas);
        let object = client.open(address).unwrap().unwrap();
        assert!(object.read(0..6).is_err());
    }
}
