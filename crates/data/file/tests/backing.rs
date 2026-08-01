use std::{
    fs::{self, File, OpenOptions},
    io::{Seek, SeekFrom, Write},
    ops::Range,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use covalence_data_file::{
    Blake3File, Blake3Mmap, FileProofError, RangeError, RangeRequirement, RangeState,
};
use covalence_lib_hash::{
    Blake3Hash,
    blake3::{Blake3ProofNode, Blake3ProofState},
};

static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

fn bytes(size: usize) -> Vec<u8> {
    (0..size)
        .map(|index| u8::try_from(index % 251).expect("bounded byte"))
        .collect()
}

fn create_file(data: &[u8]) -> (PathBuf, File) {
    loop {
        let path = std::env::temp_dir().join(format!(
            "nucleus-blake3-file-{}-{}",
            std::process::id(),
            NEXT_FILE.fetch_add(1, Ordering::Relaxed)
        ));
        let result = OpenOptions::new().write(true).create_new(true).open(&path);
        match result {
            Ok(mut output) => {
                output.write_all(data).expect("write test file");
                drop(output);
                return (path.clone(), File::open(path).expect("open test file"));
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => panic!("create test file: {error}"),
        }
    }
}

fn proof_nodes(data: &[u8], range: Range<u64>) -> Vec<Blake3ProofNode> {
    let mut complete =
        Blake3ProofState::new(data.len() as u64, None).expect("complete proof geometry");
    complete
        .insert_aligned(0, data)
        .expect("insert complete bytes");
    complete.proof(range).expect("range proof").nodes
}

#[test]
fn authenticated_file_range_installs_into_matching_mapping() {
    let data = bytes(2_177);
    let root = Blake3Hash::from_bytes(&data);
    let request = 1_111..1_999;
    let (path, file) = create_file(&data);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");
    source
        .insert_nodes(proof_nodes(&data, request.clone()))
        .expect("outside evidence");

    let verified = source
        .read_verified(request.clone())
        .expect("authenticated range");
    assert_eq!(verified.root(), root);
    assert_eq!(verified.size(), data.len() as u64);
    assert_eq!(verified.range(), &request);
    assert_eq!(verified.as_bytes(), &data[1_111..1_999]);

    let mut mapped = Blake3Mmap::new(data.len() as u64, root).expect("mapping");
    mapped.install(verified).expect("matching object");
    assert_eq!(
        mapped
            .read_verified(request.clone())
            .expect("verified mapped bytes"),
        &data[1_111..1_999]
    );
    assert!(matches!(
        mapped.read_known(0..1),
        Err(RangeError::Unavailable {
            state: RangeState::Unknown,
            requirement: RangeRequirement::Known,
            ..
        })
    ));

    drop(source);
    fs::remove_file(path).expect("remove test file");
}

#[test]
fn local_writes_are_known_but_not_verified_and_block_installation() {
    let data = bytes(2_048);
    let root = Blake3Hash::from_bytes(&data);
    let (path, file) = create_file(&data);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");
    let verified = source.read_verified(0..2_048).expect("complete read");
    let mut mapped = Blake3Mmap::new(data.len() as u64, root).expect("mapping");
    mapped.install(verified).expect("install complete object");

    mapped.write(100, b"local").expect("local write");
    assert_eq!(mapped.read_known(100..105).expect("known bytes"), b"local");
    assert!(matches!(
        mapped.read_verified(100..105),
        Err(RangeError::Unavailable {
            state: RangeState::Dirty,
            requirement: RangeRequirement::Verified,
            ..
        })
    ));

    let again = source.read_verified(0..2_048).expect("fresh complete read");
    assert!(matches!(
        mapped.install(again),
        Err(RangeError::DirtyOverlap { range }) if range == (100..105)
    ));

    drop(source);
    fs::remove_file(path).expect("remove test file");
}

#[test]
fn installation_rejects_another_object_identity() {
    let data = bytes(64);
    let root = Blake3Hash::from_bytes(&data);
    let (path, file) = create_file(&data);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");
    let verified = source.read_verified(0..64).expect("complete read");
    let other_root = Blake3Hash::from_bytes(b"another object");
    let mut mapped = Blake3Mmap::new(data.len() as u64, other_root).expect("mapping");

    assert!(matches!(
        mapped.install(verified),
        Err(RangeError::ObjectMismatch {
            expected_root,
            actual_root,
            ..
        }) if expected_root == other_root && actual_root == root
    ));

    drop(source);
    fs::remove_file(path).expect("remove test file");
}

#[test]
fn partial_read_waits_for_outside_evidence() {
    let data = bytes(3_041);
    let root = Blake3Hash::from_bytes(&data);
    let request = 1_050..1_400;
    let nodes = proof_nodes(&data, request.clone());
    let (path, file) = create_file(&data);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");

    assert!(matches!(
        source.read_verified(request.clone()),
        Err(FileProofError::MissingEvidence)
    ));
    source.insert_nodes(nodes).expect("outside evidence");
    assert_eq!(
        source
            .read_verified(request.clone())
            .expect("authenticated after evidence")
            .as_bytes(),
        &data[1_050..1_400]
    );

    drop(source);
    fs::remove_file(path).expect("remove test file");
}

#[test]
fn named_file_is_rechecked_after_an_alias_mutates_it() {
    let data = bytes(2_400);
    let root = Blake3Hash::from_bytes(&data);
    let request = 1_100..1_300;
    let (path, file) = create_file(&data);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");
    source
        .insert_nodes(proof_nodes(&data, request.clone()))
        .expect("outside evidence");
    source
        .read_verified(request.clone())
        .expect("first authenticated read");

    let mut alias = OpenOptions::new()
        .write(true)
        .open(&path)
        .expect("open alias");
    alias
        .seek(SeekFrom::Start(request.start))
        .and_then(|_| alias.write_all(b"changed"))
        .expect("mutate through alias");
    drop(alias);

    assert!(matches!(
        source.read_verified(request),
        Err(FileProofError::Proof(_))
    ));

    drop(source);
    fs::remove_file(path).expect("remove test file");
}

#[test]
fn short_physical_file_is_an_io_error() {
    let data = bytes(2_048);
    let root = Blake3Hash::from_bytes(&data);
    let (path, file) = create_file(&data[..1_024]);
    let mut source = Blake3File::new(file, data.len() as u64, root).expect("proof state");

    assert!(matches!(
        source.read_verified(0..2_048),
        Err(FileProofError::Io(error)) if error.kind() == std::io::ErrorKind::UnexpectedEof
    ));

    drop(source);
    fs::remove_file(path).expect("remove test file");
}
