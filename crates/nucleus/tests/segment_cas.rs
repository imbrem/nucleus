use covalence_data_segment::SegmentRange;
use covalence_lib_hash::{
    Blake3Hash,
    blake3::{Blake3ProofState, ProofStateError},
};
use covalence_nucleus::{Blake3SegmentCas, Connection, ResidentSegment, SegmentCasError};

const CHUNK: usize = 1_024;

fn bytes(size: usize) -> Vec<u8> {
    (0..size)
        .map(|index| {
            index
                .wrapping_mul(37)
                .wrapping_add(index / 11)
                .to_le_bytes()[0]
        })
        .collect()
}

fn resident(lo: usize, hi: usize, data: &[u8]) -> ResidentSegment {
    ResidentSegment {
        range: SegmentRange::new(lo as u64, hi as u64).expect("non-empty resident range"),
        bytes: data[lo..hi].to_vec().into(),
    }
}

#[test]
fn nucleus_connection_creates_segment_cas() {
    let connection = Connection::open_in_memory().expect("open connection");
    let mut cas = connection
        .create_blake3_segment_cas("objects")
        .expect("create segment CAS");
    let file = cas.reserve(None, None).expect("reserve nullable object");
    assert_eq!(
        cas.object(file).expect("load reservation").unwrap().size,
        None
    );
}

#[test]
fn nullable_object_metadata_has_explicit_blake3_semantics() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
    let unknown = cas.reserve(None, None).expect("fully unknown");
    let root = Blake3Hash::from_bytes(b"known identity");
    let identity_only = cas.reserve(Some(root), None).expect("identity only");
    let geometry_only = cas.reserve(None, Some(4_096)).expect("geometry only");

    assert_eq!(
        cas.object(unknown).expect("load unknown").unwrap().blake3,
        None
    );
    let object = cas.object(identity_only).expect("load identity").unwrap();
    assert_eq!(object.blake3, Some(root));
    assert_eq!(object.size, None);
    let object = cas.object(geometry_only).expect("load geometry").unwrap();
    assert_eq!(object.blake3, None);
    assert_eq!(object.size, Some(4_096));
}

#[test]
fn persists_partial_bytes_with_complete_proof_and_reopens() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(5 * CHUNK + 317);
    let root = Blake3Hash::from_bytes(&data);
    let requested = CHUNK as u64 + 19..2 * CHUNK as u64 + 23;
    let mut source = Blake3ProofState::new(data.len() as u64, Some(root)).expect("source state");
    source
        .insert_aligned(0, &data)
        .expect("hash complete source");
    let source_proof = source.proof(requested.clone()).expect("source proof");
    let lo = usize::try_from(source_proof.disclosed.start).expect("small disclosed start");
    let hi = usize::try_from(source_proof.disclosed.end).expect("small disclosed end");
    let requested_lo = usize::try_from(requested.start).expect("small request start");
    let requested_hi = usize::try_from(requested.end).expect("small request end");

    let file;
    {
        let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
        file = cas
            .reserve(Some(root), Some(data.len() as u64))
            .expect("reserve object");
        cas.replace_evidence(file, &[resident(lo, hi, &data)], &source_proof.nodes)
            .expect("persist authenticated segment");

        assert_eq!(
            cas.read_range(file, requested.clone())
                .expect("read range")
                .unwrap()
                .as_ref(),
            &data[requested_lo..requested_hi]
        );
        assert!(
            cas.read_range(file, 0..32)
                .expect("missing range")
                .is_none()
        );

        let served = cas.proof(file, requested.clone()).expect("serve proof");
        assert_eq!(served.blake3, root);
        assert_eq!(served.proof.requested, requested);
        let mut verifier =
            Blake3ProofState::new(served.size, Some(served.blake3)).expect("verifier");
        verifier
            .insert_nodes(served.proof.nodes)
            .expect("insert served frontier");
        verifier
            .insert_aligned(served.proof.disclosed.start, &served.bytes)
            .expect("verify served bytes");
        assert_eq!(verifier.claimed_root(), Some(root));
    }

    let mut reopened = Blake3SegmentCas::open(&neutron, "files").expect("checked reopen");
    assert_eq!(
        reopened
            .read_range(file, requested.clone())
            .expect("read reopened")
            .unwrap()
            .as_ref(),
        &data[requested_lo..requested_hi]
    );
}

#[test]
fn complete_resident_bytes_establish_a_missing_root() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(3 * CHUNK + 41);
    let expected = Blake3Hash::from_bytes(&data);
    let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
    let file = cas
        .reserve(None, Some(data.len() as u64))
        .expect("reserve geometry");
    let actual = cas
        .replace_evidence(
            file,
            &[
                resident(0, 2 * CHUNK, &data),
                resident(2 * CHUNK, data.len(), &data),
            ],
            &[],
        )
        .expect("derive and persist root");

    assert_eq!(actual, expected);
    assert_eq!(
        cas.object(file).expect("load object").unwrap().blake3,
        Some(expected)
    );
    assert_eq!(
        cas.read_range(file, 17..data.len() as u64 - 13)
            .expect("read across adjacent segments")
            .unwrap()
            .as_ref(),
        &data[17..data.len() - 13]
    );
}

#[test]
fn invalid_replacement_is_rejected_without_losing_old_evidence() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(2 * CHUNK + 7);
    let root = Blake3Hash::from_bytes(&data);
    let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
    let file = cas
        .reserve(Some(root), Some(data.len() as u64))
        .expect("reserve object");
    cas.replace_evidence(file, &[resident(0, data.len(), &data)], &[])
        .expect("install original evidence");

    assert!(matches!(
        cas.replace_evidence(file, &[resident(0, CHUNK, &data)], &[]),
        Err(SegmentCasError::IncompleteEvidence)
    ));
    assert_eq!(
        cas.read_range(file, 0..data.len() as u64)
            .expect("read preserved evidence")
            .unwrap()
            .as_ref(),
        data
    );
}

#[test]
fn database_failure_rolls_back_the_whole_replacement() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(2 * CHUNK + 7);
    let root = Blake3Hash::from_bytes(&data);
    let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
    let target = cas
        .reserve(None, Some(data.len() as u64))
        .expect("reserve target geometry");
    cas.reserve(Some(root), None)
        .expect("reserve conflicting identity");

    assert!(matches!(
        cas.replace_evidence(target, &[resident(0, data.len(), &data)], &[]),
        Err(SegmentCasError::Sqlite { .. })
    ));
    assert_eq!(
        cas.object(target)
            .expect("load rolled-back object")
            .unwrap()
            .blake3,
        None
    );
    assert!(matches!(
        cas.read_range(target, 0..data.len() as u64),
        Err(SegmentCasError::UnknownBlake3 { .. })
    ));
    drop(cas);
    assert_eq!(
        neutron
            .sqlite()
            .query_row("SELECT count(*) FROM files_segments", (), |row| {
                row.get::<_, i64>(0)
            })
            .expect("count rolled-back segments"),
        0
    );
}

#[test]
fn checked_open_rejects_semantically_corrupt_resident_bytes() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(2 * CHUNK + 23);
    let root = Blake3Hash::from_bytes(&data);
    {
        let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
        let file = cas
            .reserve(Some(root), Some(data.len() as u64))
            .expect("reserve object");
        cas.replace_evidence(file, &[resident(0, data.len(), &data)], &[])
            .expect("persist evidence");
    }

    let mut corrupted = data;
    corrupted[CHUNK + 3] ^= 0x80;
    neutron
        .sqlite()
        .execute(
            "UPDATE files_segments SET value = ?1",
            [corrupted.as_slice()],
        )
        .expect("physically valid corruption");

    assert!(matches!(
        Blake3SegmentCas::open(&neutron, "files"),
        Err(SegmentCasError::ProofState(
            ProofStateError::RootMismatch { .. }
        ))
    ));
}

#[test]
fn single_chunk_objects_require_bytes_not_only_a_cv() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    let data = bytes(317);
    let root = Blake3Hash::from_bytes(&data);
    let mut cas = Blake3SegmentCas::create(&neutron, "files").expect("create segment CAS");
    let file = cas
        .reserve(Some(root), Some(data.len() as u64))
        .expect("reserve object");
    let mut source = Blake3ProofState::new(data.len() as u64, Some(root)).expect("source state");
    source.insert_aligned(0, &data).expect("hash source");
    let leaf = covalence_lib_hash::blake3::Blake3ProofNode {
        node: covalence_lib_hash::blake3::Blake3Node::new(0, 1).expect("leaf geometry"),
        cv: covalence_lib_hash::blake3::Blake3Cv::from_subtree(0, &data),
    };

    assert!(matches!(
        cas.replace_evidence(file, &[], &[leaf]),
        Err(SegmentCasError::IncompleteEvidence)
    ));
    cas.replace_evidence(file, &[resident(0, data.len(), &data)], &[])
        .expect("full final chunk authenticates root output");
}
