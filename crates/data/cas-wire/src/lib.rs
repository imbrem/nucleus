//! Handle-based CAS access over a byte stream.

mod client;
mod server;

pub use client::{RemoteCas, RemoteError, RemoteObject, Transport};
pub use server::serve;

use std::io::{self, Read, Write};

use covalence_lib_hash::{O256, Obj};

/// Largest range accepted by [`Request::Read`].
pub const MAX_READ_BYTES: u64 = 1 << 20;

/// Largest diagnostic message carried by [`Response::Failed`].
pub const MAX_MESSAGE_BYTES: u32 = 4096;

/// A handle to an object the server holds open.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Handle(pub u64);

/// What a client asks for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Request {
    /// Resolve an address, opening it.
    Open(O256),
    /// Read exactly `start..end` from an open handle.
    Read {
        /// The handle to read from.
        handle: Handle,
        /// Inclusive start offset.
        start: u64,
        /// Exclusive end offset.
        end: u64,
    },
    /// Release a handle. The server may then drop the object.
    Close(Handle),
}

/// What a server answers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Response {
    /// The address resolved; the object is open under this handle.
    Opened {
        /// Handle naming the open object.
        handle: Handle,
        /// The object's total length.
        len: u64,
    },
    /// The address did not resolve here.
    Absent,
    /// Requested bytes, exactly as asked for.
    Data(Vec<u8>),
    /// The request was accepted and had no result.
    Done,
    /// The request could not be answered. Diagnostic only.
    Failed(String),
}

const OP_OPEN: u8 = 1;
const OP_READ: u8 = 2;
const OP_CLOSE: u8 = 3;

const TAG_OPENED: u8 = 1;
const TAG_ABSENT: u8 = 2;
const TAG_DATA: u8 = 3;
const TAG_DONE: u8 = 4;
const TAG_FAILED: u8 = 5;

fn write_u64(writer: &mut impl Write, value: u64) -> io::Result<()> {
    writer.write_all(&value.to_le_bytes())
}

fn read_u64(reader: &mut impl Read) -> io::Result<u64> {
    let mut bytes = [0u8; 8];
    reader.read_exact(&mut bytes)?;
    Ok(u64::from_le_bytes(bytes))
}

fn read_u8(reader: &mut impl Read) -> io::Result<u8> {
    let mut byte = [0u8; 1];
    reader.read_exact(&mut byte)?;
    Ok(byte[0])
}

fn malformed(what: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("malformed {what}"))
}

impl Request {
    /// Writes this request.
    ///
    /// # Errors
    ///
    /// Returns an error when the transport fails.
    pub fn write(&self, writer: &mut impl Write) -> io::Result<()> {
        match *self {
            Self::Open(address) => {
                writer.write_all(&[OP_OPEN])?;
                writer.write_all(address.as_bytes())?;
            }
            Self::Read { handle, start, end } => {
                writer.write_all(&[OP_READ])?;
                write_u64(writer, handle.0)?;
                write_u64(writer, start)?;
                write_u64(writer, end)?;
            }
            Self::Close(handle) => {
                writer.write_all(&[OP_CLOSE])?;
                write_u64(writer, handle.0)?;
            }
        }
        writer.flush()
    }

    /// Reads one request, or `None` at a clean end of stream.
    ///
    /// # Errors
    ///
    /// Returns an error when the transport fails or the framing is malformed.
    pub fn read(reader: &mut impl Read) -> io::Result<Option<Self>> {
        let mut opcode = [0u8; 1];
        match reader.read_exact(&mut opcode) {
            Ok(()) => {}
            // A client which closed between requests is an ordinary shutdown.
            Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(error) => return Err(error),
        }
        match opcode[0] {
            OP_OPEN => {
                let mut address = [0u8; 32];
                reader.read_exact(&mut address)?;
                Ok(Some(Self::Open(Obj::from_array(address))))
            }
            OP_READ => Ok(Some(Self::Read {
                handle: Handle(read_u64(reader)?),
                start: read_u64(reader)?,
                end: read_u64(reader)?,
            })),
            OP_CLOSE => Ok(Some(Self::Close(Handle(read_u64(reader)?)))),
            _ => Err(malformed("request opcode")),
        }
    }
}

impl Response {
    /// Writes this response.
    ///
    /// # Errors
    ///
    /// Returns an error when the transport fails.
    pub fn write(&self, writer: &mut impl Write) -> io::Result<()> {
        match self {
            Self::Opened { handle, len } => {
                writer.write_all(&[TAG_OPENED])?;
                write_u64(writer, handle.0)?;
                write_u64(writer, *len)?;
            }
            Self::Absent => writer.write_all(&[TAG_ABSENT])?,
            Self::Data(bytes) => {
                writer.write_all(&[TAG_DATA])?;
                write_u64(writer, bytes.len() as u64)?;
                writer.write_all(bytes)?;
            }
            Self::Done => writer.write_all(&[TAG_DONE])?,
            Self::Failed(message) => {
                writer.write_all(&[TAG_FAILED])?;
                // Truncate on a character boundary so the wire stays UTF-8.
                let mut end = message.len().min(MAX_MESSAGE_BYTES as usize);
                while end > 0 && !message.is_char_boundary(end) {
                    end -= 1;
                }
                let message = &message[..end];
                writer.write_all(&u32::try_from(message.len()).unwrap_or(0).to_le_bytes())?;
                writer.write_all(message.as_bytes())?;
            }
        }
        writer.flush()
    }

    /// Reads one response.
    ///
    /// # Errors
    ///
    /// Returns an error when the transport fails or the framing is malformed.
    pub fn read(reader: &mut impl Read) -> io::Result<Self> {
        match read_u8(reader)? {
            TAG_OPENED => Ok(Self::Opened {
                handle: Handle(read_u64(reader)?),
                len: read_u64(reader)?,
            }),
            TAG_ABSENT => Ok(Self::Absent),
            TAG_DATA => {
                let len = read_u64(reader)?;
                if len > MAX_READ_BYTES {
                    return Err(malformed("oversized data frame"));
                }
                // `len` is bounded above, so this allocation is bounded.
                let mut bytes = vec![0u8; usize::try_from(len).unwrap_or(0)];
                reader.read_exact(&mut bytes)?;
                Ok(Self::Data(bytes))
            }
            TAG_DONE => Ok(Self::Done),
            TAG_FAILED => {
                let mut length = [0u8; 4];
                reader.read_exact(&mut length)?;
                let length = u32::from_le_bytes(length);
                if length > MAX_MESSAGE_BYTES {
                    return Err(malformed("oversized message frame"));
                }
                let mut bytes = vec![0u8; length as usize];
                reader.read_exact(&mut bytes)?;
                String::from_utf8(bytes)
                    .map(Self::Failed)
                    .map_err(|_| malformed("message encoding"))
            }
            _ => Err(malformed("response tag")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip_request(request: Request) {
        let mut buffer = Vec::new();
        request.write(&mut buffer).unwrap();
        let decoded = Request::read(&mut buffer.as_slice()).unwrap().unwrap();
        assert_eq!(decoded, request);
    }

    fn round_trip_response(response: &Response) {
        let mut buffer = Vec::new();
        response.write(&mut buffer).unwrap();
        let decoded = Response::read(&mut buffer.as_slice()).unwrap();
        assert_eq!(&decoded, response);
    }

    #[test]
    fn requests_round_trip() {
        round_trip_request(Request::Open(O256::from_bytes(b"object")));
        round_trip_request(Request::Read {
            handle: Handle(7),
            start: 4096,
            end: 8192,
        });
        round_trip_request(Request::Close(Handle(7)));
    }

    #[test]
    fn responses_round_trip() {
        round_trip_response(&Response::Opened {
            handle: Handle(1),
            len: 8192,
        });
        round_trip_response(&Response::Absent);
        round_trip_response(&Response::Data(vec![1, 2, 3]));
        round_trip_response(&Response::Data(Vec::new()));
        round_trip_response(&Response::Done);
        round_trip_response(&Response::Failed("nope".to_owned()));
    }

    #[test]
    fn a_clean_end_of_stream_is_not_an_error() {
        assert_eq!(Request::read(&mut [].as_slice()).unwrap(), None);
    }

    #[test]
    fn a_truncated_request_is_an_error() {
        // An opcode with no address behind it.
        assert!(Request::read(&mut [OP_OPEN].as_slice()).is_err());
    }

    #[test]
    fn an_unknown_opcode_is_rejected() {
        assert!(Request::read(&mut [0xff].as_slice()).is_err());
    }

    #[test]
    fn an_oversized_data_frame_is_refused_before_allocating() {
        let mut frame = vec![TAG_DATA];
        frame.extend_from_slice(&u64::MAX.to_le_bytes());
        assert!(Response::read(&mut frame.as_slice()).is_err());
    }

    #[test]
    fn an_oversized_message_frame_is_refused() {
        let mut frame = vec![TAG_FAILED];
        frame.extend_from_slice(&u32::MAX.to_le_bytes());
        assert!(Response::read(&mut frame.as_slice()).is_err());
    }

    #[test]
    fn a_long_message_is_truncated_on_a_character_boundary() {
        // A multi-byte character straddling the limit must not be split.
        let message = "é".repeat(MAX_MESSAGE_BYTES as usize);
        let mut buffer = Vec::new();
        Response::Failed(message).write(&mut buffer).unwrap();
        let Response::Failed(decoded) = Response::read(&mut buffer.as_slice()).unwrap() else {
            panic!("expected a failure response");
        };
        assert!(decoded.len() <= MAX_MESSAGE_BYTES as usize);
        assert!(decoded.chars().all(|character| character == 'é'));
    }
}
