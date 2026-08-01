//! Checked persistence and serving for segmented unkeyed BLAKE3 objects.

use std::{collections::BTreeSet, error::Error, fmt, ops::Range};

use bytes::Bytes;
use covalence_data_segment::SegmentRange;
use covalence_lib_hash::{
    Blake3Hash,
    blake3::{
        Blake3Cv, Blake3Node, Blake3Proof, Blake3ProofNode, Blake3ProofState, ProofStateError,
    },
};
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

use crate::{SegmentMap, SegmentMapError, SegmentTableName};

const CHUNK_BYTES: u64 = 1_024;
const CREATE_OBJECTS_SQL: &str = include_str!("../sql/create_segment_cas_objects.sql");
const CREATE_PROOFS_SQL: &str = include_str!("../sql/create_segment_cas_proofs.sql");
const RESERVE_SQL: &str = include_str!("../sql/reserve_segment_cas_object.sql");
const GET_OBJECT_SQL: &str = include_str!("../sql/get_segment_cas_object.sql");
const UPDATE_BLAKE3_SQL: &str = include_str!("../sql/update_segment_cas_blake3.sql");
const DELETE_SEGMENTS_SQL: &str = include_str!("../sql/delete_segment_cas_segments.sql");
const DELETE_PROOFS_SQL: &str = include_str!("../sql/delete_segment_cas_proofs.sql");
const INSERT_PROOF_SQL: &str = include_str!("../sql/insert_segment_cas_proof.sql");
const LOAD_PROOFS_SQL: &str = include_str!("../sql/load_segment_cas_proofs.sql");

/// Persistent identity of one segmented object.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileId(i64);

impl FileId {
    /// Returns the positive `SQLite` row identity.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// Nullable identity and geometry state for one object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SegmentCasObject {
    /// Persistent row identity.
    pub file_id: FileId,
    /// Explicit pure, unkeyed BLAKE3 address when known.
    pub blake3: Option<Blake3Hash>,
    /// Complete byte length when known.
    pub size: Option<u64>,
}

/// Resident bytes occupying one non-empty range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResidentSegment {
    /// Half-open byte range occupied by `bytes`.
    pub range: SegmentRange,
    /// Exact resident bytes for `range`.
    pub bytes: Bytes,
}

/// An authenticated range response.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SegmentCasProof {
    /// Explicit pure, unkeyed BLAKE3 object address.
    pub blake3: Blake3Hash,
    /// Complete object size used to fix BLAKE3 tree geometry.
    pub size: u64,
    /// Requested/disclosed geometry and outside CV frontier.
    pub proof: Blake3Proof,
    /// Bytes for the proof's complete `disclosed` range.
    pub bytes: Bytes,
}

/// Prepared handle for one caller-selected persistent segment-CAS table family.
///
/// The selected name identifies the object table. The adapter derives
/// `<name>_segments` and `<name>_blake3_proofs`; all three live in `main`.
/// Object `blake3` and `size` columns are independently nullable so callers can
/// reserve incomplete metadata. Evidence can only be persisted through
/// [`replace_evidence`](Self::replace_evidence), which atomically installs a
/// complete non-overlapping partition of resident chunk-aligned bytes and
/// canonical outside CVs and records the one root it derives.
///
/// Opening first runs `PRAGMA main.integrity_check`, then validates exact table
/// schemas, the segment map's database-enforced non-overlap invariant, all
/// foreign identities, and every evidence partition against its explicit pure
/// unkeyed BLAKE3 root. No keyed or context-keyed mode is accepted.
///
/// This remains a design experiment: opening and serving load and validate a
/// whole object's resident bytes and proof frontier. It establishes the trust
/// boundary but is not yet suitable for objects whose full evidence cannot fit
/// in memory.
pub struct Blake3SegmentCas<'conn> {
    connection: &'conn covalence_neutron::Connection,
    objects: SegmentTableName,
    proofs: SegmentTableName,
    segments: SegmentMap<'conn>,
    reserve: sqlite::Statement<'conn>,
    get_object: sqlite::Statement<'conn>,
    update_blake3: sqlite::Statement<'conn>,
    delete_segments: sqlite::Statement<'conn>,
    delete_proofs: sqlite::Statement<'conn>,
    insert_proof: sqlite::Statement<'conn>,
}

impl fmt::Debug for Blake3SegmentCas<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Blake3SegmentCas")
            .field("objects", &self.objects)
            .field("segments", self.segments.table())
            .field("proofs", &self.proofs)
            .finish_non_exhaustive()
    }
}

impl<'conn> Blake3SegmentCas<'conn> {
    /// Creates a new segment-CAS table family atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsafe or existing name or any schema,
    /// integrity, or preparation failure.
    pub fn create(
        connection: &'conn covalence_neutron::Connection,
        table: &str,
    ) -> Result<Self, SegmentCasError> {
        let names = TableNames::new(table)?;
        enable_foreign_keys(connection.sqlite())?;
        connection
            .sqlite()
            .execute_batch("SAVEPOINT cov_nucleus_create_segment_cas")
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "begin segment-CAS creation",
                source,
            })?;
        let result = (|| {
            connection
                .sqlite()
                .execute_batch(&create_objects_sql(&names))
                .map_err(|source| SegmentCasError::Sqlite {
                    operation: "create segment-CAS object table",
                    source,
                })?;
            drop(SegmentMap::create(connection, names.segments.as_str())?);
            connection
                .sqlite()
                .execute_batch(&create_proofs_sql(&names))
                .map_err(|source| SegmentCasError::Sqlite {
                    operation: "create segment-CAS proof table",
                    source,
                })?;
            connection
                .sqlite()
                .execute_batch("RELEASE cov_nucleus_create_segment_cas")
                .map_err(|source| SegmentCasError::Sqlite {
                    operation: "commit segment-CAS creation",
                    source,
                })
        })();
        if let Err(error) = result {
            rollback_savepoint(connection, "cov_nucleus_create_segment_cas");
            return Err(error);
        }
        Self::open_named(connection, names)
    }

    /// Opens an existing segment-CAS after physical and semantic validation.
    ///
    /// # Errors
    ///
    /// Returns an error when integrity checking fails, schemas or rows are
    /// malformed, or persisted evidence does not derive its recorded BLAKE3
    /// address.
    pub fn open(
        connection: &'conn covalence_neutron::Connection,
        table: &str,
    ) -> Result<Self, SegmentCasError> {
        Self::open_named(connection, TableNames::new(table)?)
    }

    fn open_named(
        connection: &'conn covalence_neutron::Connection,
        names: TableNames,
    ) -> Result<Self, SegmentCasError> {
        enable_foreign_keys(connection.sqlite())?;
        validate_integrity(connection.sqlite())?;
        validate_schema(connection.sqlite(), &names)?;
        let segments = SegmentMap::open(connection, names.segments.as_str())?;
        validate_stored_evidence(connection.sqlite(), &names)?;
        let prepare = |template: &str, operation| {
            connection
                .sqlite()
                .prepare(&instantiate(template, &names))
                .map_err(|source| SegmentCasError::Sqlite { operation, source })
        };
        Ok(Self {
            connection,
            reserve: prepare(RESERVE_SQL, "prepare object reservation")?,
            get_object: prepare(GET_OBJECT_SQL, "prepare object lookup")?,
            update_blake3: prepare(UPDATE_BLAKE3_SQL, "prepare BLAKE3 update")?,
            delete_segments: prepare(DELETE_SEGMENTS_SQL, "prepare segment replacement")?,
            delete_proofs: prepare(DELETE_PROOFS_SQL, "prepare proof replacement")?,
            insert_proof: prepare(INSERT_PROOF_SQL, "prepare proof insertion")?,
            objects: names.objects,
            proofs: names.proofs,
            segments,
        })
    }

    /// Reserves nullable object metadata and returns its persistent identity.
    ///
    /// A hash without a size is an identity-only reservation. A size without a
    /// hash reserves fixed geometry. No evidence is claimed resident.
    ///
    /// # Errors
    ///
    /// Returns an error for a size outside signed `SQLite` `INTEGER`, a wrong
    /// empty-object root, a duplicate BLAKE3 address, or a database failure.
    pub fn reserve(
        &mut self,
        blake3: Option<Blake3Hash>,
        size: Option<u64>,
    ) -> Result<FileId, SegmentCasError> {
        require_foreign_keys(self.connection.sqlite())?;
        let sqlite_size = size
            .map(|size| i64::try_from(size).map_err(|_| SegmentCasError::SizeTooLarge { size }))
            .transpose()?;
        if size == Some(0) {
            Blake3ProofState::new(0, blake3).map_err(SegmentCasError::ProofState)?;
        }
        let blake3_bytes = blake3.map(|hash| *hash.as_bytes());
        self.reserve
            .query_row(
                (blake3_bytes.as_ref().map(<[u8; 32]>::as_slice), sqlite_size),
                |row| row.get::<_, i64>(0).map(FileId),
            )
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "reserve segment-CAS object",
                source,
            })
    }

    /// Loads nullable metadata for an object identity.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored metadata or a database failure.
    pub fn object(&mut self, file_id: FileId) -> Result<Option<SegmentCasObject>, SegmentCasError> {
        self.get_object
            .query_row([file_id.0], |row| {
                Ok((
                    row.get::<_, Option<Vec<u8>>>(0)?,
                    row.get::<_, Option<i64>>(1)?,
                ))
            })
            .optional()
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "load segment-CAS object",
                source,
            })?
            .map(|(blake3, size)| decode_object(file_id, blake3, size))
            .transpose()
    }

    /// Atomically replaces all resident bytes and proof evidence for an object.
    ///
    /// The supplied ranges and canonical proof nodes must partition the whole
    /// BLAKE3 chunk space exactly once. Resident ranges are chunk-aligned except
    /// that the final range may end at an unaligned object end. The complete
    /// partition must derive the existing address, or establishes it when the
    /// object previously had only a size.
    ///
    /// # Errors
    ///
    /// Returns an error before persistence for incomplete, overlapping,
    /// malformed, or contradictory evidence. Database failures roll back the
    /// entire replacement.
    pub fn replace_evidence(
        &mut self,
        file_id: FileId,
        resident: &[ResidentSegment],
        proofs: &[Blake3ProofNode],
    ) -> Result<Blake3Hash, SegmentCasError> {
        require_foreign_keys(self.connection.sqlite())?;
        self.connection
            .sqlite()
            .execute_batch("SAVEPOINT cov_nucleus_replace_segment_evidence")
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "begin evidence replacement",
                source,
            })?;
        let result = (|| {
            let object = self
                .object(file_id)?
                .ok_or(SegmentCasError::MissingObject { file_id })?;
            let size = object
                .size
                .ok_or(SegmentCasError::UnknownSize { file_id })?;
            let derived = validate_evidence(size, object.blake3, resident, proofs)?;
            self.persist_replacement(file_id, size, object.blake3, derived, resident, proofs)?;
            Ok(derived)
        })();
        finish_savepoint(
            self.connection,
            "cov_nucleus_replace_segment_evidence",
            "commit evidence replacement",
            result,
        )
    }

    fn persist_replacement(
        &mut self,
        file_id: FileId,
        size: u64,
        previous_blake3: Option<Blake3Hash>,
        blake3: Blake3Hash,
        resident: &[ResidentSegment],
        proofs: &[Blake3ProofNode],
    ) -> Result<(), SegmentCasError> {
        self.delete_segments
            .execute([file_key(file_id).as_slice()])
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "delete old resident segments",
                source,
            })?;
        self.delete_proofs
            .execute([file_id.0])
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "delete old proof evidence",
                source,
            })?;
        for segment in resident {
            self.segments
                .insert(&file_key(file_id), segment.range, &segment.bytes)?;
        }
        for proof in proofs {
            let first_chunk = sqlite_u64(proof.node.first_chunk())?;
            let chunks = sqlite_u64(proof.node.chunks())?;
            self.insert_proof
                .execute((
                    file_id.0,
                    first_chunk,
                    chunks,
                    proof.cv.as_bytes().as_slice(),
                ))
                .map_err(|source| SegmentCasError::Sqlite {
                    operation: "insert proof evidence",
                    source,
                })?;
        }
        let previous_blake3 = previous_blake3.map(|hash| *hash.as_bytes());
        let sqlite_size =
            i64::try_from(size).map_err(|_| SegmentCasError::SizeTooLarge { size })?;
        let changed = self
            .update_blake3
            .execute((
                file_id.0,
                blake3.as_bytes().as_slice(),
                previous_blake3.as_ref().map(<[u8; 32]>::as_slice),
                sqlite_size,
            ))
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "record derived BLAKE3 address",
                source,
            })?;
        if changed != 1 {
            return Err(SegmentCasError::ObjectChanged { file_id });
        }
        Ok(())
    }

    /// Reads an exact byte range when resident segments cover it without gaps.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing object, unknown size, invalid range, or
    /// malformed/database state.
    pub fn read_range(
        &mut self,
        file_id: FileId,
        requested: Range<u64>,
    ) -> Result<Option<Bytes>, SegmentCasError> {
        begin_savepoint(
            self.connection,
            "cov_nucleus_read_segment_range",
            "begin authenticated range read",
        )?;
        let result = (|| {
            let object = self
                .object(file_id)?
                .ok_or(SegmentCasError::MissingObject { file_id })?;
            let size = object
                .size
                .ok_or(SegmentCasError::UnknownSize { file_id })?;
            let blake3 = object
                .blake3
                .ok_or(SegmentCasError::UnknownBlake3 { file_id })?;
            let (resident, proofs) =
                load_evidence(self.connection.sqlite(), &self.names(), file_id)?;
            validated_state(size, Some(blake3), &resident, &proofs)?;
            read_resident_range(&resident, requested, size)
        })();
        finish_savepoint(
            self.connection,
            "cov_nucleus_read_segment_range",
            "finish authenticated range read",
            result,
        )
    }

    /// Returns resident chunk-rounded bytes and their minimal BLAKE3 frontier.
    ///
    /// # Errors
    ///
    /// Returns an error unless identity, size, checked evidence, and all bytes
    /// in the chunk-rounded disclosure are available.
    pub fn proof(
        &mut self,
        file_id: FileId,
        requested: Range<u64>,
    ) -> Result<SegmentCasProof, SegmentCasError> {
        begin_savepoint(
            self.connection,
            "cov_nucleus_read_segment_proof",
            "begin authenticated proof read",
        )?;
        let result = (|| {
            let object = self
                .object(file_id)?
                .ok_or(SegmentCasError::MissingObject { file_id })?;
            let size = object
                .size
                .ok_or(SegmentCasError::UnknownSize { file_id })?;
            let blake3 = object
                .blake3
                .ok_or(SegmentCasError::UnknownBlake3 { file_id })?;
            let (resident, nodes) =
                load_evidence(self.connection.sqlite(), &self.names(), file_id)?;
            let state = validated_state(size, Some(blake3), &resident, &nodes)?;
            let proof = state
                .proof(requested)
                .map_err(SegmentCasError::ProofState)?;
            let bytes = read_resident_range(&resident, proof.disclosed.clone(), size)?.ok_or_else(
                || SegmentCasError::RangeUnavailable {
                    file_id,
                    requested: proof.disclosed.clone(),
                },
            )?;
            Ok(SegmentCasProof {
                blake3,
                size,
                proof,
                bytes,
            })
        })();
        finish_savepoint(
            self.connection,
            "cov_nucleus_read_segment_proof",
            "finish authenticated proof read",
            result,
        )
    }

    fn names(&self) -> TableNames {
        TableNames {
            objects: self.objects.clone(),
            segments: self.segments.table().clone(),
            proofs: self.proofs.clone(),
        }
    }
}

#[derive(Clone, Debug)]
struct TableNames {
    objects: SegmentTableName,
    segments: SegmentTableName,
    proofs: SegmentTableName,
}

impl TableNames {
    fn new(table: &str) -> Result<Self, SegmentCasError> {
        let objects = SegmentTableName::new(table)?;
        let segments = SegmentTableName::new(format!("{table}_segments"))?;
        let proofs = SegmentTableName::new(format!("{table}_blake3_proofs"))?;
        Ok(Self {
            objects,
            segments,
            proofs,
        })
    }
}

fn quote(name: &SegmentTableName) -> String {
    format!("\"{}\"", name.as_str())
}

fn instantiate(template: &str, names: &TableNames) -> String {
    template
        .replace("{objects}", &quote(&names.objects))
        .replace("{segments}", &quote(&names.segments))
        .replace("{proofs}", &quote(&names.proofs))
}

fn create_objects_sql(names: &TableNames) -> String {
    instantiate(CREATE_OBJECTS_SQL, names)
}

fn create_proofs_sql(names: &TableNames) -> String {
    instantiate(CREATE_PROOFS_SQL, names)
}

fn enable_foreign_keys(connection: &sqlite::Connection) -> Result<(), SegmentCasError> {
    connection
        .execute_batch("PRAGMA foreign_keys = ON")
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "enable SQLite foreign keys",
            source,
        })?;
    require_foreign_keys(connection)
}

fn require_foreign_keys(connection: &sqlite::Connection) -> Result<(), SegmentCasError> {
    let enabled = connection
        .query_row("PRAGMA foreign_keys", (), |row| row.get::<_, bool>(0))
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "check SQLite foreign keys",
            source,
        })?;
    if enabled {
        Ok(())
    } else {
        Err(SegmentCasError::ForeignKeysDisabled)
    }
}

fn begin_savepoint(
    connection: &covalence_neutron::Connection,
    name: &str,
    operation: &'static str,
) -> Result<(), SegmentCasError> {
    connection
        .sqlite()
        .execute_batch(&format!("SAVEPOINT {name}"))
        .map_err(|source| SegmentCasError::Sqlite { operation, source })
}

fn finish_savepoint<T>(
    connection: &covalence_neutron::Connection,
    name: &str,
    operation: &'static str,
    result: Result<T, SegmentCasError>,
) -> Result<T, SegmentCasError> {
    match result {
        Ok(value) => {
            if let Err(source) = connection
                .sqlite()
                .execute_batch(&format!("RELEASE {name}"))
            {
                rollback_savepoint(connection, name);
                Err(SegmentCasError::Sqlite { operation, source })
            } else {
                Ok(value)
            }
        }
        Err(error) => {
            rollback_savepoint(connection, name);
            Err(error)
        }
    }
}

fn read_resident_range(
    resident: &[ResidentSegment],
    requested: Range<u64>,
    size: u64,
) -> Result<Option<Bytes>, SegmentCasError> {
    if requested.start > requested.end || requested.end > size {
        return Err(SegmentCasError::InvalidRange { requested, size });
    }
    if requested.is_empty() {
        return Ok(Some(Bytes::new()));
    }

    let mut cursor = requested.start;
    for segment in resident {
        if segment.range.hi() <= cursor {
            continue;
        }
        if segment.range.lo() >= requested.end {
            break;
        }
        if segment.range.lo() > cursor {
            return Ok(None);
        }
        let stored_width = usize::try_from(segment.range.width())
            .map_err(|_| SegmentCasError::SizeTooLarge { size })?;
        if segment.bytes.len() != stored_width {
            return Err(SegmentCasError::MalformedEvidence {
                reason: format!(
                    "resident range {}..{} has {} bytes, expected {stored_width}",
                    segment.range.lo(),
                    segment.range.hi(),
                    segment.bytes.len()
                ),
            });
        }
        cursor = requested.end.min(segment.range.hi());
        if cursor == requested.end {
            break;
        }
    }
    if cursor != requested.end {
        return Ok(None);
    }

    let mut output = allocate_range_buffer(requested.end - requested.start, size)?;
    let mut cursor = requested.start;
    for segment in resident {
        if segment.range.hi() <= cursor {
            continue;
        }
        if segment.range.lo() >= requested.end {
            break;
        }
        let copy_start = cursor.max(segment.range.lo());
        let copy_end = requested.end.min(segment.range.hi());
        let start = usize::try_from(copy_start - segment.range.lo())
            .map_err(|_| SegmentCasError::SizeTooLarge { size })?;
        let end = usize::try_from(copy_end - segment.range.lo())
            .map_err(|_| SegmentCasError::SizeTooLarge { size })?;
        output.extend_from_slice(&segment.bytes[start..end]);
        cursor = copy_end;
    }
    debug_assert_eq!(cursor, requested.end, "coverage was checked before copying");
    Ok(Some(Bytes::from(output)))
}

fn allocate_range_buffer(bytes: u64, object_size: u64) -> Result<Vec<u8>, SegmentCasError> {
    let capacity =
        usize::try_from(bytes).map_err(|_| SegmentCasError::SizeTooLarge { size: object_size })?;
    let mut output = Vec::new();
    output
        .try_reserve_exact(capacity)
        .map_err(|_| SegmentCasError::AllocationFailed { bytes })?;
    Ok(output)
}

fn validate_integrity(connection: &sqlite::Connection) -> Result<(), SegmentCasError> {
    let mut statement = connection
        .prepare("PRAGMA main.integrity_check")
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "prepare SQLite integrity check",
            source,
        })?;
    let results = statement
        .query_map((), |row| row.get::<_, String>(0))
        .and_then(Iterator::collect)
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "run SQLite integrity check",
            source,
        })?;
    if results == ["ok"] {
        Ok(())
    } else {
        Err(SegmentCasError::IntegrityCheck { results })
    }
}

fn validate_schema(
    connection: &sqlite::Connection,
    names: &TableNames,
) -> Result<(), SegmentCasError> {
    for (kind, name, expected) in [
        (
            "object",
            &names.objects,
            normalize_sql(&create_objects_sql(names)),
        ),
        (
            "proof",
            &names.proofs,
            normalize_sql(&create_proofs_sql(names)),
        ),
    ] {
        let actual = connection
            .query_row(
                "SELECT sql FROM main.sqlite_schema WHERE type = 'table' AND name = ?1",
                [name.as_str()],
                |row| row.get::<_, String>(0),
            )
            .optional()
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "inspect segment-CAS schema",
                source,
            })?;
        if actual.as_deref().map(normalize_sql).as_deref() != Some(expected.as_str()) {
            return Err(SegmentCasError::InvalidSchema {
                table: name.as_str().to_owned(),
                reason: format!(
                    "missing or altered {kind} table: expected {expected:?}, found {:?}",
                    actual.as_deref().map(normalize_sql)
                ),
            });
        }
    }
    Ok(())
}

fn normalize_sql(sql: &str) -> String {
    sql.trim()
        .trim_end_matches(';')
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn validate_stored_evidence(
    connection: &sqlite::Connection,
    names: &TableNames,
) -> Result<(), SegmentCasError> {
    let objects_sql = format!(
        "SELECT file_id, blake3, size FROM {} ORDER BY file_id",
        quote(&names.objects)
    );
    let mut statement =
        connection
            .prepare(&objects_sql)
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "prepare stored object validation",
                source,
            })?;
    let objects = statement
        .query_map((), |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, Option<Vec<u8>>>(1)?,
                row.get::<_, Option<i64>>(2)?,
            ))
        })
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "query stored objects",
            source,
        })?
        .collect::<sqlite::Result<Vec<_>>>()
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "read stored objects",
            source,
        })?;
    let mut known = BTreeSet::new();
    for (raw_id, blake3, size) in objects {
        let file_id = checked_file_id(raw_id)?;
        known.insert(file_id);
        let object = decode_object(file_id, blake3, size)?;
        let (resident, proofs) = load_evidence(connection, names, file_id)?;
        if resident.is_empty() && proofs.is_empty() {
            if object.size == Some(0) {
                Blake3ProofState::new(0, object.blake3).map_err(SegmentCasError::ProofState)?;
            }
            continue;
        }
        let size = object
            .size
            .ok_or(SegmentCasError::UnknownSize { file_id })?;
        let expected = object
            .blake3
            .ok_or(SegmentCasError::UnknownBlake3 { file_id })?;
        validate_evidence(size, Some(expected), &resident, &proofs)?;
    }
    validate_foreign_evidence(connection, names, &known)
}

fn validate_foreign_evidence(
    connection: &sqlite::Connection,
    names: &TableNames,
    known: &BTreeSet<FileId>,
) -> Result<(), SegmentCasError> {
    let segment_sql = format!(
        "SELECT DISTINCT segment_key FROM {}",
        quote(&names.segments)
    );
    let mut statement =
        connection
            .prepare(&segment_sql)
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "prepare segment ownership validation",
                source,
            })?;
    let keys = statement
        .query_map((), |row| row.get::<_, Vec<u8>>(0))
        .and_then(Iterator::collect::<sqlite::Result<Vec<_>>>)
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "validate segment ownership",
            source,
        })?;
    for key in keys {
        let file_id = decode_file_key(&key)?;
        if !known.contains(&file_id) {
            return Err(SegmentCasError::OrphanEvidence { file_id });
        }
    }

    let proof_sql = format!("SELECT DISTINCT file_id FROM {}", quote(&names.proofs));
    let mut statement =
        connection
            .prepare(&proof_sql)
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "prepare proof ownership validation",
                source,
            })?;
    let ids = statement
        .query_map((), |row| row.get::<_, i64>(0))
        .and_then(Iterator::collect::<sqlite::Result<Vec<_>>>)
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "validate proof ownership",
            source,
        })?;
    for id in ids {
        let file_id = checked_file_id(id)?;
        if !known.contains(&file_id) {
            return Err(SegmentCasError::OrphanEvidence { file_id });
        }
    }
    Ok(())
}

fn load_evidence(
    connection: &sqlite::Connection,
    names: &TableNames,
    file_id: FileId,
) -> Result<(Vec<ResidentSegment>, Vec<Blake3ProofNode>), SegmentCasError> {
    let segment_sql = format!(
        "SELECT lo, hi, value FROM {} WHERE segment_key = ?1 ORDER BY lo",
        quote(&names.segments)
    );
    let mut statement =
        connection
            .prepare(&segment_sql)
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "prepare resident segment loading",
                source,
            })?;
    let raw_segments = statement
        .query_map([file_key(file_id).as_slice()], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, Vec<u8>>(2)?,
            ))
        })
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "query resident segments",
            source,
        })?
        .collect::<sqlite::Result<Vec<_>>>()
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "read resident segments",
            source,
        })?;
    let resident = raw_segments
        .into_iter()
        .map(|(lo, hi, bytes)| {
            let lo = u64::try_from(lo).map_err(|_| SegmentCasError::MalformedEvidence {
                reason: "negative resident segment lower bound".into(),
            })?;
            let hi = u64::try_from(hi).map_err(|_| SegmentCasError::MalformedEvidence {
                reason: "negative resident segment upper bound".into(),
            })?;
            let range =
                SegmentRange::new(lo, hi).map_err(|error| SegmentCasError::MalformedEvidence {
                    reason: error.to_string(),
                })?;
            Ok(ResidentSegment {
                range,
                bytes: Bytes::from(bytes),
            })
        })
        .collect::<Result<Vec<_>, SegmentCasError>>()?;

    let proof_sql = instantiate(LOAD_PROOFS_SQL, names);
    let mut statement =
        connection
            .prepare(&proof_sql)
            .map_err(|source| SegmentCasError::Sqlite {
                operation: "prepare proof evidence loading",
                source,
            })?;
    let raw_proofs = statement
        .query_map([file_id.0], |row| {
            Ok((
                row.get::<_, i64>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, Vec<u8>>(2)?,
            ))
        })
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "query proof evidence",
            source,
        })?
        .collect::<sqlite::Result<Vec<_>>>()
        .map_err(|source| SegmentCasError::Sqlite {
            operation: "read proof evidence",
            source,
        })?;
    let proofs = raw_proofs
        .into_iter()
        .map(|(first_chunk, chunks, cv)| {
            let first_chunk =
                u64::try_from(first_chunk).map_err(|_| SegmentCasError::MalformedEvidence {
                    reason: "negative proof-node position".into(),
                })?;
            let chunks = u64::try_from(chunks).map_err(|_| SegmentCasError::MalformedEvidence {
                reason: "negative proof-node width".into(),
            })?;
            let cv = <[u8; 32]>::try_from(cv).map_err(|_| SegmentCasError::MalformedEvidence {
                reason: "BLAKE3 CV is not 32 bytes".into(),
            })?;
            Ok(Blake3ProofNode {
                node: Blake3Node::new(first_chunk, chunks).map_err(SegmentCasError::ProofState)?,
                cv: Blake3Cv::from_array(cv),
            })
        })
        .collect::<Result<Vec<_>, SegmentCasError>>()?;
    Ok((resident, proofs))
}

fn validate_evidence(
    size: u64,
    expected: Option<Blake3Hash>,
    resident: &[ResidentSegment],
    proofs: &[Blake3ProofNode],
) -> Result<Blake3Hash, SegmentCasError> {
    let state = validated_state(size, expected, resident, proofs)?;
    state
        .claimed_root()
        .ok_or(SegmentCasError::IncompleteEvidence)
}

fn validated_state(
    size: u64,
    expected: Option<Blake3Hash>,
    resident: &[ResidentSegment],
    proofs: &[Blake3ProofNode],
) -> Result<Blake3ProofState, SegmentCasError> {
    let state = proof_state(size, expected, resident, proofs)?;
    validate_partition(size, resident, proofs)?;
    if state.claimed_root().is_none() {
        return Err(SegmentCasError::IncompleteEvidence);
    }
    Ok(state)
}

fn proof_state(
    size: u64,
    expected: Option<Blake3Hash>,
    resident: &[ResidentSegment],
    proofs: &[Blake3ProofNode],
) -> Result<Blake3ProofState, SegmentCasError> {
    let mut state = Blake3ProofState::new(size, expected).map_err(SegmentCasError::ProofState)?;
    for segment in resident {
        let width = usize::try_from(segment.range.width())
            .map_err(|_| SegmentCasError::SizeTooLarge { size })?;
        if segment.bytes.len() != width {
            return Err(SegmentCasError::MalformedEvidence {
                reason: format!(
                    "resident range {}..{} has {} bytes, expected {width}",
                    segment.range.lo(),
                    segment.range.hi(),
                    segment.bytes.len()
                ),
            });
        }
        state
            .insert_aligned(segment.range.lo(), &segment.bytes)
            .map_err(SegmentCasError::ProofState)?;
    }
    state
        .insert_nodes(proofs.iter().copied())
        .map_err(SegmentCasError::ProofState)?;
    Ok(state)
}

fn validate_partition(
    size: u64,
    resident: &[ResidentSegment],
    proofs: &[Blake3ProofNode],
) -> Result<(), SegmentCasError> {
    let total_chunks = size.div_ceil(CHUNK_BYTES);
    let mut coverage = Vec::with_capacity(resident.len() + proofs.len());
    for segment in resident {
        let valid = segment.range.lo().is_multiple_of(CHUNK_BYTES)
            && segment.range.hi() <= size
            && (segment.range.hi() == size || segment.range.hi().is_multiple_of(CHUNK_BYTES));
        if !valid {
            return Err(SegmentCasError::MalformedEvidence {
                reason: format!(
                    "resident range {}..{} is not canonical for size {size}",
                    segment.range.lo(),
                    segment.range.hi()
                ),
            });
        }
        coverage.push((
            segment.range.lo() / CHUNK_BYTES,
            segment.range.hi().div_ceil(CHUNK_BYTES),
        ));
    }
    for proof in proofs {
        coverage.push((
            proof.node.first_chunk(),
            proof.node.first_chunk() + proof.node.chunks(),
        ));
    }
    coverage.sort_unstable();
    let mut cursor = 0;
    for (lo, hi) in coverage {
        if lo != cursor {
            return Err(SegmentCasError::IncompleteEvidence);
        }
        cursor = hi;
    }
    if cursor == total_chunks {
        Ok(())
    } else {
        Err(SegmentCasError::IncompleteEvidence)
    }
}

fn decode_object(
    file_id: FileId,
    blake3: Option<Vec<u8>>,
    size: Option<i64>,
) -> Result<SegmentCasObject, SegmentCasError> {
    let blake3 = blake3
        .map(|bytes| {
            <[u8; 32]>::try_from(bytes)
                .map(Blake3Hash::from_array)
                .map_err(|_| SegmentCasError::MalformedObject { file_id })
        })
        .transpose()?;
    let size = size
        .map(|size| u64::try_from(size).map_err(|_| SegmentCasError::MalformedObject { file_id }))
        .transpose()?;
    Ok(SegmentCasObject {
        file_id,
        blake3,
        size,
    })
}

fn checked_file_id(raw: i64) -> Result<FileId, SegmentCasError> {
    if raw > 0 {
        Ok(FileId(raw))
    } else {
        Err(SegmentCasError::MalformedEvidence {
            reason: format!("invalid file identity {raw}"),
        })
    }
}

fn file_key(file_id: FileId) -> [u8; 8] {
    file_id.0.to_be_bytes()
}

fn decode_file_key(key: &[u8]) -> Result<FileId, SegmentCasError> {
    let bytes = <[u8; 8]>::try_from(key).map_err(|_| SegmentCasError::MalformedEvidence {
        reason: "segment namespace is not an eight-byte file identity".into(),
    })?;
    checked_file_id(i64::from_be_bytes(bytes))
}

fn sqlite_u64(value: u64) -> Result<i64, SegmentCasError> {
    i64::try_from(value).map_err(|_| SegmentCasError::MalformedEvidence {
        reason: format!("proof coordinate {value} exceeds signed SQLite INTEGER"),
    })
}

fn rollback_savepoint(connection: &covalence_neutron::Connection, name: &str) {
    let sql = format!("ROLLBACK TO {name}; RELEASE {name}");
    let _ = connection.sqlite().execute_batch(&sql);
}

/// Failure to create, validate, mutate, or serve a persistent segment CAS.
#[derive(Debug)]
pub enum SegmentCasError {
    /// The caller-selected table family name is invalid.
    SegmentMap(SegmentMapError),
    /// A `SQLite` operation failed.
    Sqlite {
        /// Stable operation description.
        operation: &'static str,
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
    /// `SQLite` reported physical database corruption.
    IntegrityCheck {
        /// Complete non-`ok` integrity output.
        results: Vec<String>,
    },
    /// Foreign-key enforcement is disabled for this connection.
    ForeignKeysDisabled,
    /// A required table does not have the canonical schema.
    InvalidSchema {
        /// Physical table name.
        table: String,
        /// Validation failure.
        reason: String,
    },
    /// Object metadata is malformed.
    MalformedObject {
        /// Affected identity.
        file_id: FileId,
    },
    /// Segment or proof bytes have invalid persistent semantics.
    MalformedEvidence {
        /// Validation failure.
        reason: String,
    },
    /// Evidence refers to no object row.
    OrphanEvidence {
        /// Unowned file identity.
        file_id: FileId,
    },
    /// The selected object does not exist.
    MissingObject {
        /// Missing identity.
        file_id: FileId,
    },
    /// Object metadata changed during an evidence replacement.
    ObjectChanged {
        /// Concurrently or unexpectedly changed identity.
        file_id: FileId,
    },
    /// Fixed object geometry is not known.
    UnknownSize {
        /// Affected identity.
        file_id: FileId,
    },
    /// The pure BLAKE3 identity is not known.
    UnknownBlake3 {
        /// Affected identity.
        file_id: FileId,
    },
    /// A byte size cannot be represented by this `SQLite` schema.
    SizeTooLarge {
        /// Rejected size.
        size: u64,
    },
    /// A requested output buffer could not be allocated.
    AllocationFailed {
        /// Requested output bytes.
        bytes: u64,
    },
    /// A requested range is reversed or outside the object.
    InvalidRange {
        /// Rejected range.
        requested: Range<u64>,
        /// Complete object size.
        size: u64,
    },
    /// Resident bytes do not cover a requested range.
    RangeUnavailable {
        /// Affected identity.
        file_id: FileId,
        /// Missing range.
        requested: Range<u64>,
    },
    /// Evidence does not partition the complete BLAKE3 chunk space.
    IncompleteEvidence,
    /// BLAKE3 geometry or authentication failed.
    ProofState(ProofStateError),
}

impl From<SegmentMapError> for SegmentCasError {
    fn from(error: SegmentMapError) -> Self {
        Self::SegmentMap(error)
    }
}

impl fmt::Display for SegmentCasError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SegmentMap(error) => error.fmt(formatter),
            Self::Sqlite { operation, source } => {
                write!(formatter, "could not {operation}: {source}")
            }
            Self::IntegrityCheck { results } => {
                write!(
                    formatter,
                    "SQLite integrity check failed: {}",
                    results.join("; ")
                )
            }
            Self::ForeignKeysDisabled => {
                formatter.write_str("SQLite foreign-key enforcement is disabled")
            }
            Self::InvalidSchema { table, reason } => {
                write!(formatter, "invalid segment-CAS table {table}: {reason}")
            }
            Self::MalformedObject { file_id } => {
                write!(formatter, "malformed segment-CAS object {}", file_id.get())
            }
            Self::MalformedEvidence { reason } => {
                write!(formatter, "malformed segment-CAS evidence: {reason}")
            }
            Self::OrphanEvidence { file_id } => {
                write!(
                    formatter,
                    "evidence refers to missing object {}",
                    file_id.get()
                )
            }
            Self::MissingObject { file_id } => {
                write!(
                    formatter,
                    "segment-CAS object {} does not exist",
                    file_id.get()
                )
            }
            Self::ObjectChanged { file_id } => write!(
                formatter,
                "segment-CAS object {} changed during evidence replacement",
                file_id.get()
            ),
            Self::UnknownSize { file_id } => {
                write!(
                    formatter,
                    "segment-CAS object {} has unknown size",
                    file_id.get()
                )
            }
            Self::UnknownBlake3 { file_id } => {
                write!(
                    formatter,
                    "segment-CAS object {} has unknown BLAKE3",
                    file_id.get()
                )
            }
            Self::SizeTooLarge { size } => {
                write!(
                    formatter,
                    "object size {size} exceeds signed SQLite INTEGER"
                )
            }
            Self::AllocationFailed { bytes } => {
                write!(formatter, "could not allocate {bytes} range bytes")
            }
            Self::InvalidRange { requested, size } => write!(
                formatter,
                "range {}..{} is invalid for object size {size}",
                requested.start, requested.end
            ),
            Self::RangeUnavailable { file_id, requested } => write!(
                formatter,
                "object {} has no resident bytes for {}..{}",
                file_id.get(),
                requested.start,
                requested.end
            ),
            Self::IncompleteEvidence => {
                formatter.write_str("evidence does not cover the complete BLAKE3 chunk space")
            }
            Self::ProofState(error) => error.fmt(formatter),
        }
    }
}

impl Error for SegmentCasError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::SegmentMap(error) => Some(error),
            Self::Sqlite { source, .. } => Some(source),
            Self::ProofState(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn oversized_range_allocation_is_fallible() {
        let end = u64::try_from(i64::MAX).unwrap();
        match allocate_range_buffer(end, end).unwrap_err() {
            SegmentCasError::AllocationFailed { bytes } => assert_eq!(bytes, end),
            SegmentCasError::SizeTooLarge { size } => assert_eq!(size, end),
            error => panic!("unexpected range-allocation error: {error}"),
        }
    }
}
