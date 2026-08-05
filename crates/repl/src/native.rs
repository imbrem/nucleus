//! Length-framed native adapter for the signed kernel service contract.
//!
//! Only physical framing and child lifecycle live here. Canonical message
//! encoding and every authenticated semantic check are shared with other
//! transports.

use std::error::Error as StdError;
use std::fmt;
use std::io::{self, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio};

use super::{
    EndpointDescription, MAX_SIGNED_MESSAGE_BYTES, ServiceOperation, SessionAccepted,
    SessionRequest, SignedKernelService, SignedMessageError, SignedMessageRequest,
    SignedMessageResponse, SignedServiceCommand, SignedServiceReply, decode_signed_request,
    decode_signed_response, encode_signed_request, encode_signed_response,
};

const MAX_FRAME_BYTES: usize = MAX_SIGNED_MESSAGE_BYTES;

/// Serves signed kernel messages until EOF or an authenticated shutdown.
///
/// Malformed framing and invalid session handshakes terminate the pipe rather
/// than creating an unsigned error channel. Command-level rejections are
/// endpoint-signed [`super::ServiceResult::Rejected`] replies.
///
/// # Errors
///
/// Returns an error for malformed framing, failed standard I/O, an invalid
/// session handshake, or a signing failure.
pub fn serve_kernel_stdio(
    mut input: impl Read,
    mut output: impl Write,
) -> Result<(), NativeTransportError> {
    let mut service = SignedKernelService::new().map_err(service_error)?;
    loop {
        let Some(payload) = read_frame(&mut input)? else {
            return Ok(());
        };
        let response = match decode_signed_request(&payload)? {
            SignedMessageRequest::Describe => {
                SignedMessageResponse::Description(service.description().clone())
            }
            SignedMessageRequest::OpenSession(request) => SignedMessageResponse::SessionAccepted(
                service.open_session(&request).map_err(service_error)?,
            ),
            SignedMessageRequest::Execute(command) => {
                let reply = service.execute(&command).map_err(service_error)?;
                let shutdown =
                    matches!(command.operation(), ServiceOperation::Shutdown) && reply.is_goodbye();
                write_frame(
                    &mut output,
                    &encode_signed_response(&SignedMessageResponse::Reply(reply))?,
                )?;
                output.flush()?;
                if shutdown {
                    return Ok(());
                }
                continue;
            }
        };
        write_frame(&mut output, &encode_signed_response(&response)?)?;
        output.flush()?;
    }
}

/// A directly spawned kernel child carrying signed service messages over pipes.
pub struct NativeKernelProcess {
    child: Child,
    input: Option<ChildStdin>,
    output: ChildStdout,
}

impl NativeKernelProcess {
    /// Starts `program --kernel-stdio` with isolated framing streams.
    ///
    /// The operating system binds these pipes to the exact spawned child.
    /// Callers still verify its self-signed description against the directory
    /// identity they choose for the session.
    ///
    /// # Errors
    ///
    /// Returns an error when the child or its pipes cannot be opened.
    pub fn spawn(program: impl AsRef<Path>) -> Result<Self, NativeTransportError> {
        let mut child = Command::new(program.as_ref())
            .arg("--kernel-stdio")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let input = child
            .stdin
            .take()
            .ok_or(NativeTransportError::Protocol("child stdin is unavailable"))?;
        let output = child.stdout.take().ok_or(NativeTransportError::Protocol(
            "child stdout is unavailable",
        ))?;
        Ok(Self {
            child,
            input: Some(input),
            output,
        })
    }

    /// Fetches the endpoint's signed metadata and fresh session challenge.
    ///
    /// # Errors
    ///
    /// Returns an error for failed framing or an unexpected response.
    pub fn describe(&mut self) -> Result<EndpointDescription, NativeTransportError> {
        match self.exchange(&SignedMessageRequest::Describe)? {
            SignedMessageResponse::Description(description) => Ok(description),
            _ => Err(NativeTransportError::Protocol(
                "unexpected description response",
            )),
        }
    }

    /// Sends a requester-signed handshake and returns endpoint-signed acceptance.
    ///
    /// # Errors
    ///
    /// Returns an error for failed framing or an unexpected response. The
    /// caller must verify the acceptance with [`super::SessionInitiator`].
    pub fn open_session(
        &mut self,
        request: &SessionRequest,
    ) -> Result<SessionAccepted, NativeTransportError> {
        match self.exchange(&SignedMessageRequest::OpenSession(request.clone()))? {
            SignedMessageResponse::SessionAccepted(accepted) => Ok(accepted),
            _ => Err(NativeTransportError::Protocol(
                "unexpected session response",
            )),
        }
    }

    /// Sends one signed command and returns its endpoint-signed response.
    ///
    /// # Errors
    ///
    /// Returns an error for failed framing or an unexpected response. The
    /// caller must verify request/result binding with its signed session.
    pub fn execute(
        &mut self,
        command: &SignedServiceCommand,
    ) -> Result<SignedServiceReply, NativeTransportError> {
        match self.exchange(&SignedMessageRequest::Execute(command.clone()))? {
            SignedMessageResponse::Reply(reply) => Ok(reply),
            _ => Err(NativeTransportError::Protocol(
                "unexpected command response",
            )),
        }
    }

    /// Forces the spawned child to exit while retaining this transport handle.
    ///
    /// This is a coordinator lifecycle primitive, not a signed service
    /// operation. Normal shutdown must use [`ServiceOperation::Shutdown`].
    ///
    /// # Errors
    ///
    /// Returns an error if the process cannot be killed or reaped.
    pub fn kill(&mut self) -> Result<ExitStatus, NativeTransportError> {
        self.child.kill()?;
        Ok(self.child.wait()?)
    }

    /// Closes stdin and waits after a verified signed shutdown response.
    ///
    /// # Errors
    ///
    /// Returns an error if the child exits unsuccessfully.
    pub fn wait_for_exit(mut self) -> Result<ExitStatus, NativeTransportError> {
        drop(self.input.take());
        let status = self.child.wait()?;
        if status.success() {
            Ok(status)
        } else {
            Err(NativeTransportError::Exit(status))
        }
    }

    fn exchange(
        &mut self,
        request: &SignedMessageRequest,
    ) -> Result<SignedMessageResponse, NativeTransportError> {
        let payload = encode_signed_request(request)?;
        let input = self
            .input
            .as_mut()
            .ok_or(NativeTransportError::Protocol("kernel stdin is closed"))?;
        write_frame(input, &payload)?;
        input.flush()?;
        let payload = read_frame(&mut self.output)?.ok_or(NativeTransportError::Protocol(
            "kernel closed stdout before replying",
        ))?;
        decode_signed_response(&payload).map_err(Into::into)
    }
}

impl Drop for NativeKernelProcess {
    fn drop(&mut self) {
        drop(self.input.take());
        if matches!(self.child.try_wait(), Ok(None)) {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

/// Failure in the above-TCB native framing adapter.
#[derive(Debug)]
pub enum NativeTransportError {
    /// Standard I/O or process creation failed.
    Io(io::Error),
    /// A malformed frame or unexpected response was encountered.
    Protocol(&'static str),
    /// A frame exceeded its transport-independent message bound.
    Invalid(String),
    /// Canonical signed-message decoding failed.
    Message(SignedMessageError),
    /// The signed service rejected a handshake or could not sign.
    Service(String),
    /// The child exited unsuccessfully.
    Exit(ExitStatus),
}

impl fmt::Display for NativeTransportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "native kernel I/O failed: {error}"),
            Self::Protocol(message) => write!(formatter, "native kernel protocol error: {message}"),
            Self::Invalid(message) => write!(formatter, "invalid native kernel frame: {message}"),
            Self::Message(error) => error.fmt(formatter),
            Self::Service(message) => write!(formatter, "signed kernel service failed: {message}"),
            Self::Exit(status) => write!(formatter, "native kernel exited with {status}"),
        }
    }
}

impl StdError for NativeTransportError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Message(error) => Some(error),
            Self::Protocol(_) | Self::Invalid(_) | Self::Service(_) | Self::Exit(_) => None,
        }
    }
}

impl From<io::Error> for NativeTransportError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<SignedMessageError> for NativeTransportError {
    fn from(error: SignedMessageError) -> Self {
        Self::Message(error)
    }
}

fn service_error(error: impl fmt::Display) -> NativeTransportError {
    NativeTransportError::Service(error.to_string())
}

fn write_frame(output: &mut impl Write, payload: &[u8]) -> Result<(), NativeTransportError> {
    if payload.len() > MAX_FRAME_BYTES {
        return Err(NativeTransportError::Invalid(format!(
            "frame is {} bytes; limit is {MAX_FRAME_BYTES}",
            payload.len()
        )));
    }
    let length = u32::try_from(payload.len())
        .map_err(|_| NativeTransportError::Protocol("frame length does not fit u32"))?;
    output.write_all(&length.to_be_bytes())?;
    output.write_all(payload)?;
    Ok(())
}

fn read_frame(input: &mut impl Read) -> Result<Option<Vec<u8>>, NativeTransportError> {
    let mut length = [0; 4];
    let mut read = 0;
    while read < length.len() {
        match input.read(&mut length[read..])? {
            0 if read == 0 => return Ok(None),
            0 => return Err(NativeTransportError::Protocol("truncated frame length")),
            count => read += count,
        }
    }
    let length = u32::from_be_bytes(length) as usize;
    if length > MAX_FRAME_BYTES {
        return Err(NativeTransportError::Invalid(format!(
            "frame claims {length} bytes; limit is {MAX_FRAME_BYTES}"
        )));
    }
    let mut payload = vec![0; length];
    input.read_exact(&mut payload)?;
    Ok(Some(payload))
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;

    #[test]
    fn rejects_oversized_frames_before_allocating_the_claimed_body() {
        let claimed = u32::try_from(MAX_FRAME_BYTES + 1).unwrap().to_be_bytes();
        let error = read_frame(&mut Cursor::new(claimed)).unwrap_err();
        assert!(error.to_string().contains("frame claims"));
    }

    #[test]
    fn rejects_truncated_frame_lengths_and_bodies() {
        let error = read_frame(&mut Cursor::new([0, 0])).unwrap_err();
        assert!(error.to_string().contains("truncated frame length"));

        let mut body = 3_u32.to_be_bytes().to_vec();
        body.extend_from_slice(&[1, 2]);
        let error = read_frame(&mut Cursor::new(body)).unwrap_err();
        assert!(error.to_string().contains("failed to fill whole buffer"));
    }
}
