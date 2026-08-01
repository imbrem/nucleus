use std::{
    cell::Cell,
    fs::{self, File, OpenOptions},
    io::{self, Cursor, Read, Write},
    path::PathBuf,
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

use covalence_data_file::{Blake3Mmap, LoadError, load_blake3_path, load_blake3_reader};
use covalence_lib_hash::Blake3Hash;

static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

fn create_file(data: &[u8]) -> PathBuf {
    loop {
        let path = std::env::temp_dir().join(format!(
            "nucleus-blake3-loader-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(mut file) => {
                file.write_all(data).expect("write test file");
                return path;
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
            Err(error) => panic!("create test file: {error}"),
        }
    }
}

#[test]
fn reader_returns_owned_bytes_only_after_exact_verification() {
    let bytes = b"complete object";
    let root = Blake3Hash::from_bytes(bytes);
    let loaded =
        load_blake3_reader(Cursor::new(bytes), bytes.len() as u64, root).expect("checked bytes");

    assert_eq!(loaded.root(), root);
    assert_eq!(loaded.size(), bytes.len() as u64);
    assert_eq!(loaded.as_bytes(), bytes);

    let mut mapped = Blake3Mmap::new(bytes.len() as u64, root).expect("mapping");
    mapped
        .install(loaded.into_verified_range())
        .expect("install complete checked object");
    assert_eq!(
        mapped
            .read_verified(0..bytes.len() as u64)
            .expect("verified mapping"),
        bytes
    );
}

#[test]
fn empty_object_is_checked_without_a_special_transport_path() {
    let root = Blake3Hash::from_bytes([]);
    let loaded = load_blake3_reader(Cursor::new([]), 0, root).expect("empty object");

    assert_eq!(loaded.size(), 0);
    assert!(loaded.as_bytes().is_empty());
}

#[test]
fn size_errors_precede_hash_comparison() {
    let root = Blake3Hash::from_bytes(b"abc");

    assert!(matches!(
        load_blake3_reader(Cursor::new(b"ab"), 3, root),
        Err(LoadError::Short {
            expected: 3,
            actual: 2,
        })
    ));
    assert!(matches!(
        load_blake3_reader(Cursor::new(b"abcd"), 3, root),
        Err(LoadError::Long { expected: 3 })
    ));
}

#[test]
fn long_input_is_bounded_after_the_first_extra_byte() {
    struct Counted {
        remaining: usize,
        read: Rc<Cell<usize>>,
    }

    impl Read for Counted {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            let length = output.len().min(self.remaining);
            output[..length].fill(7);
            self.remaining -= length;
            self.read.set(self.read.get() + length);
            Ok(length)
        }
    }

    let read = Rc::new(Cell::new(0));
    let reader = Counted {
        remaining: 1_000_000,
        read: Rc::clone(&read),
    };
    let result = load_blake3_reader(reader, 8, Blake3Hash::from_bytes([7; 8]));

    assert!(matches!(result, Err(LoadError::Long { expected: 8 })));
    assert_eq!(read.get(), 9);
}

#[test]
fn exact_size_with_the_wrong_root_is_rejected() {
    let bytes = b"candidate";
    let expected = Blake3Hash::from_bytes(b"different");

    assert!(matches!(
        load_blake3_reader(Cursor::new(bytes), bytes.len() as u64, expected),
        Err(LoadError::HashMismatch { expected: seen, actual })
            if seen == expected && actual == Blake3Hash::from_bytes(bytes)
    ));
}

#[test]
fn response_reader_errors_remain_transport_errors() {
    struct Failing;

    impl Read for Failing {
        fn read(&mut self, _output: &mut [u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::ConnectionReset, "test reset"))
        }
    }

    assert!(matches!(
        load_blake3_reader(Failing, 5, Blake3Hash::default()),
        Err(LoadError::Read(error)) if error.kind() == io::ErrorKind::ConnectionReset
    ));
}

#[test]
fn contract_violating_reader_is_rejected_without_panicking() {
    struct Overreporting;

    impl Read for Overreporting {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            Ok(output.len() + 1)
        }
    }

    assert!(matches!(
        load_blake3_reader(Overreporting, 5, Blake3Hash::default()),
        Err(LoadError::Read(error)) if error.kind() == io::ErrorKind::InvalidData
    ));
}

#[test]
fn path_loader_streams_the_opened_handle() {
    let bytes = b"path-backed object";
    let root = Blake3Hash::from_bytes(bytes);
    let path = create_file(bytes);

    let loaded = load_blake3_path(&path, bytes.len() as u64, root).expect("checked path");
    assert_eq!(loaded.as_bytes(), bytes);

    fs::remove_file(path).expect("remove test file");
}

#[test]
fn missing_path_is_distinct_from_stream_failure() {
    let path = std::env::temp_dir().join(format!(
        "nucleus-missing-loader-{}-{}",
        std::process::id(),
        NEXT_FILE.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_file(&path);

    assert!(matches!(
        load_blake3_path(&path, 0, Blake3Hash::from_bytes([])),
        Err(LoadError::Open { path: seen, .. }) if seen == path
    ));
}

#[test]
fn small_response_chunks_are_streamed_normally() {
    struct OneByte<R>(R);

    impl<R: Read> Read for OneByte<R> {
        fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
            let selected = output.len().min(1);
            self.0.read(&mut output[..selected])
        }
    }

    let bytes = b"synchronous response body";
    let loaded = load_blake3_reader(
        OneByte(Cursor::new(bytes)),
        bytes.len() as u64,
        Blake3Hash::from_bytes(bytes),
    )
    .expect("chunked response");
    assert_eq!(loaded.as_bytes(), bytes);
}

#[test]
fn path_loader_does_not_depend_on_metadata_length() {
    let bytes = b"exact bytes";
    let path = create_file(bytes);
    let file = File::open(&path).expect("open for metadata");
    assert_eq!(file.metadata().expect("metadata").len(), bytes.len() as u64);
    drop(file);

    assert!(matches!(
        load_blake3_path(&path, bytes.len() as u64 - 1, Blake3Hash::default()),
        Err(LoadError::Long { .. })
    ));

    fs::remove_file(path).expect("remove test file");
}
