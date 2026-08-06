//! A shareable in-memory sink, so a caller can read back what the shell wrote.

use std::io::{self, Write};
use std::sync::{Arc, Mutex};

/// An in-memory [`Write`] whose contents survive being handed to a
/// [`Shell`](crate::Shell).
///
/// [`Shell`](crate::Shell) takes ownership of its output, which is right for a
/// terminal and awkward for a test. Cloning one of these shares the same
/// buffer, so the caller keeps a handle to whatever the shell prints.
#[derive(Clone, Debug, Default)]
pub struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl SharedBuffer {
    /// Constructs an empty buffer.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Removes and returns everything written so far.
    #[must_use]
    pub fn take(&self) -> Vec<u8> {
        std::mem::take(&mut self.locked())
    }

    /// Removes and returns everything written so far, lossily as text.
    #[must_use]
    pub fn take_string(&self) -> String {
        String::from_utf8_lossy(&self.take()).into_owned()
    }

    /// Whether nothing has been written.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.locked().is_empty()
    }

    fn locked(&self) -> std::sync::MutexGuard<'_, Vec<u8>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

impl Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.locked().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_clone_shares_the_buffer() {
        let buffer = SharedBuffer::new();
        let mut writer = buffer.clone();
        assert!(buffer.is_empty());
        write!(writer, "hello").unwrap();
        assert_eq!(buffer.take_string(), "hello");
        assert!(buffer.is_empty());
    }
}
