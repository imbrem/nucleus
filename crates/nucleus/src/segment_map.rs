//! A prepared `SQLite` table adapter for non-overlapping segment maps.

use std::{error::Error, fmt};

use covalence_data_segment::SegmentRange;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

/// A validated `SQLite` table name.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentTableName(String);

impl SegmentTableName {
    /// Validates an unqualified `SQLite` identifier.
    ///
    /// Names are deliberately restricted even though all generated SQL also
    /// quotes them. Attached database qualification can be added separately
    /// without making `.` ambiguous here.
    ///
    /// # Errors
    ///
    /// Returns [`SegmentMapError::InvalidTableName`] unless `name` is a short
    /// unqualified ASCII identifier.
    pub fn new(name: impl Into<String>) -> Result<Self, SegmentMapError> {
        let name = name.into();
        let mut chars = name.chars();
        let first_ok = chars
            .next()
            .is_some_and(|character| character == '_' || character.is_ascii_alphabetic());
        if !first_ok
            || !chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
            || name.len() > 128
        {
            return Err(SegmentMapError::InvalidTableName { name });
        }
        Ok(Self(name))
    }

    /// Returns the caller-selected table name.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn quoted(&self) -> String {
        format!("\"{}\"", self.0)
    }

    fn derived_quoted(&self, suffix: &str) -> String {
        format!("\"{}{}\"", self.0, suffix)
    }
}

/// Connection-local identity of one persistent segment row.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentId(i64);

impl SegmentId {
    /// Returns the `SQLite` `INTEGER PRIMARY KEY` value.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One row returned by a persistent segment map.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Segment {
    /// Connection-local row identity.
    pub id: SegmentId,
    /// Namespace key. Equal keys share a non-overlap invariant.
    pub key: Vec<u8>,
    /// Non-empty half-open range.
    pub range: SegmentRange,
    /// Uninterpreted table payload.
    pub value: Vec<u8>,
}

/// A caller-selected `SQLite` segment table represented by prepared operations.
pub struct SegmentMap<'conn> {
    table: SegmentTableName,
    find_overlap: sqlite::Statement<'conn>,
    insert: sqlite::Statement<'conn>,
    point: sqlite::Statement<'conn>,
    overlapping: sqlite::Statement<'conn>,
    remove: sqlite::Statement<'conn>,
}

impl fmt::Debug for SegmentMap<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SegmentMap")
            .field("table", &self.table)
            .finish_non_exhaustive()
    }
}

impl<'conn> SegmentMap<'conn> {
    /// Creates a strict table, its overlap guards, and a prepared adapter.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsafe name, an existing table, or any `SQLite`
    /// schema/preparation failure.
    pub fn create(
        connection: &'conn covalence_neutron::Connection,
        table: &str,
    ) -> Result<Self, SegmentMapError> {
        let table = SegmentTableName::new(table)?;
        let q = table.quoted();
        let key_lo = table.derived_quoted("_key_lo");
        let insert_guard = table.derived_quoted("_no_overlap_insert");
        let update_guard = table.derived_quoted("_no_overlap_update");
        let sql = format!(
            "SAVEPOINT cov_nucleus_create_segment_map;
             {};
             {};
             {};
             {};
             RELEASE cov_nucleus_create_segment_map;",
            create_table_sql(&q),
            create_index_sql(&q, &key_lo),
            create_insert_trigger_sql(&q, &insert_guard),
            create_update_trigger_sql(&q, &update_guard),
        );
        if let Err(source) = connection.sqlite().execute_batch(&sql) {
            // `execute_batch` leaves an explicitly opened savepoint active on
            // error. Clean up only the innermost savepoint with our name.
            let _ = connection.sqlite().execute_batch(
                "ROLLBACK TO cov_nucleus_create_segment_map;
                 RELEASE cov_nucleus_create_segment_map;",
            );
            return Err(SegmentMapError::Sqlite {
                operation: "create segment-map schema",
                source,
            });
        }
        Self::open_named(connection, table)
    }

    /// Opens an existing table after checking its schema and every row.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsafe name, an incompatible schema, invalid or
    /// overlapping stored ranges, missing overlap guards, or `SQLite` failure.
    pub fn open(
        connection: &'conn covalence_neutron::Connection,
        table: &str,
    ) -> Result<Self, SegmentMapError> {
        Self::open_named(connection, SegmentTableName::new(table)?)
    }

    fn open_named(
        connection: &'conn covalence_neutron::Connection,
        table: SegmentTableName,
    ) -> Result<Self, SegmentMapError> {
        validate_schema(connection.sqlite(), &table)?;
        validate_contents(connection.sqlite(), &table)?;
        let q = table.quoted();
        let prepare = |sql: String, operation| {
            connection
                .sqlite()
                .prepare(&sql)
                .map_err(|source| SegmentMapError::Sqlite { operation, source })
        };
        Ok(Self {
            find_overlap: prepare(
                format!(
                    "SELECT segment_id, lo, hi FROM {q}
                     WHERE segment_key = ?1 AND lo < ?3 AND ?2 < hi
                     ORDER BY lo LIMIT 1"
                ),
                "prepare overlap query",
            )?,
            insert: prepare(
                format!(
                    "INSERT INTO {q} (segment_key, lo, hi, value)
                     VALUES (?1, ?2, ?3, ?4) RETURNING segment_id"
                ),
                "prepare insert",
            )?,
            point: prepare(
                format!(
                    "SELECT segment_id, segment_key, lo, hi, value FROM {q}
                     WHERE segment_key = ?1 AND lo <= ?2 AND ?2 < hi
                     ORDER BY lo LIMIT 1"
                ),
                "prepare point query",
            )?,
            overlapping: prepare(
                format!(
                    "SELECT segment_id, segment_key, lo, hi, value FROM {q}
                     WHERE segment_key = ?1 AND lo < ?3 AND ?2 < hi ORDER BY lo"
                ),
                "prepare range query",
            )?,
            remove: prepare(
                format!(
                    "DELETE FROM {q} WHERE segment_id = ?1
                     RETURNING segment_id, segment_key, lo, hi, value"
                ),
                "prepare remove",
            )?,
            table,
        })
    }

    /// Returns the identity of the underlying `SQLite` table.
    #[must_use]
    pub const fn table(&self) -> &SegmentTableName {
        &self.table
    }

    /// Inserts a segment, rejecting overlap within the same key.
    ///
    /// # Errors
    ///
    /// Returns [`SegmentMapError::Overlap`] for intersecting geometry,
    /// [`SegmentMapError::RangeTooLarge`] for an endpoint beyond signed
    /// `SQLite` `INTEGER`, or an error if `SQLite` rejects the write.
    pub fn insert(
        &mut self,
        key: &[u8],
        range: SegmentRange,
        value: &[u8],
    ) -> Result<SegmentId, SegmentMapError> {
        let (lo, hi) = sqlite_range(range)?;
        let existing = self
            .find_overlap
            .query_row((key, lo, hi), |row| {
                Ok((
                    SegmentId(row.get(0)?),
                    row.get::<_, i64>(1)?,
                    row.get::<_, i64>(2)?,
                ))
            })
            .optional()
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "query overlap",
                source,
            })?;
        if let Some((existing, old_lo, old_hi)) = existing {
            return Err(SegmentMapError::Overlap {
                existing,
                range: decode_range(old_lo, old_hi)?,
            });
        }
        self.insert
            .query_row((key, lo, hi, value), |row| row.get(0).map(SegmentId))
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "insert segment",
                source,
            })
    }

    /// Finds the segment for `key` containing `point`.
    ///
    /// # Errors
    ///
    /// Returns an error for a point beyond signed `SQLite` `INTEGER`, malformed
    /// returned data, or a `SQLite` query failure.
    pub fn get(&mut self, key: &[u8], point: u64) -> Result<Option<Segment>, SegmentMapError> {
        let point = i64::try_from(point).map_err(|_| SegmentMapError::PointTooLarge { point })?;
        self.point
            .query_row((key, point), decode_segment)
            .optional()
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "query point",
                source,
            })?
            .map(validate_segment)
            .transpose()
    }

    /// Returns segments for `key` intersecting `range`, ordered by lower bound.
    ///
    /// # Errors
    ///
    /// Returns an error for an endpoint beyond signed `SQLite` `INTEGER`,
    /// malformed returned data, or a `SQLite` query failure.
    pub fn overlapping(
        &mut self,
        key: &[u8],
        range: SegmentRange,
    ) -> Result<Vec<Segment>, SegmentMapError> {
        let (lo, hi) = sqlite_range(range)?;
        let rows = self
            .overlapping
            .query_map((key, lo, hi), decode_segment)
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "query range",
                source,
            })?;
        rows.map(|row| {
            row.map_err(|source| SegmentMapError::Sqlite {
                operation: "read range row",
                source,
            })
            .and_then(validate_segment)
        })
        .collect()
    }

    /// Removes and returns one exact row by connection-local identity.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed returned data or a `SQLite` failure.
    pub fn remove(&mut self, id: SegmentId) -> Result<Option<Segment>, SegmentMapError> {
        self.remove
            .query_row([id.0], decode_segment)
            .optional()
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "remove segment",
                source,
            })?
            .map(validate_segment)
            .transpose()
    }
}

fn validate_schema(
    connection: &sqlite::Connection,
    table: &SegmentTableName,
) -> Result<(), SegmentMapError> {
    let q = table.quoted();
    let columns = connection
        .prepare(&format!("PRAGMA main.table_info({q})"))
        .and_then(|mut statement| {
            statement
                .query_map((), |row| {
                    Ok((
                        row.get::<_, String>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, bool>(3)?,
                        row.get::<_, i64>(5)?,
                    ))
                })?
                .collect::<sqlite::Result<Vec<_>>>()
        })
        .map_err(|source| SegmentMapError::Sqlite {
            operation: "inspect segment-map schema",
            source,
        })?;
    let expected = [
        ("segment_id", "INTEGER", false, 1),
        ("segment_key", "BLOB", true, 0),
        ("lo", "INTEGER", true, 0),
        ("hi", "INTEGER", true, 0),
        ("value", "BLOB", true, 0),
    ];
    if columns.len() != expected.len()
        || columns.iter().zip(expected).any(|(actual, expected)| {
            actual.0 != expected.0
                || !actual.1.eq_ignore_ascii_case(expected.1)
                || actual.2 != expected.2
                || actual.3 != expected.3
        })
    {
        return Err(SegmentMapError::InvalidSchema {
            table: table.clone(),
            reason: "expected exactly segment_id INTEGER PRIMARY KEY, segment_key BLOB NOT NULL, lo INTEGER NOT NULL, hi INTEGER NOT NULL, value BLOB NOT NULL".into(),
        });
    }

    let strict = connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [table.as_str()],
            |row| row.get::<_, bool>(0),
        )
        .optional()
        .map_err(|source| SegmentMapError::Sqlite {
            operation: "inspect table strictness",
            source,
        })?;
    if strict != Some(true) {
        return Err(SegmentMapError::InvalidSchema {
            table: table.clone(),
            reason: "segment table must be STRICT".into(),
        });
    }

    let q = table.quoted();
    let objects = [
        ("table", table.as_str().to_owned(), create_table_sql(&q)),
        (
            "index",
            format!("{}_key_lo", table.as_str()),
            create_index_sql(&q, &table.derived_quoted("_key_lo")),
        ),
        (
            "trigger",
            format!("{}_no_overlap_insert", table.as_str()),
            create_insert_trigger_sql(&q, &table.derived_quoted("_no_overlap_insert")),
        ),
        (
            "trigger",
            format!("{}_no_overlap_update", table.as_str()),
            create_update_trigger_sql(&q, &table.derived_quoted("_no_overlap_update")),
        ),
    ];
    for (kind, name, expected_sql) in objects {
        let actual_sql = connection
            .query_row(
                "SELECT sql FROM main.sqlite_schema
                 WHERE type = ?1 AND name = ?2 AND tbl_name = ?3",
                (kind, &name, table.as_str()),
                |row| row.get::<_, String>(0),
            )
            .optional()
            .map_err(|source| SegmentMapError::Sqlite {
                operation: "inspect segment-map definitions",
                source,
            })?;
        let expected_sql = normalize_sql(&expected_sql);
        if actual_sql.as_deref().map(normalize_sql).as_deref() != Some(expected_sql.as_str()) {
            return Err(SegmentMapError::InvalidSchema {
                table: table.clone(),
                reason: format!("missing or altered required {kind} {name}"),
            });
        }
    }
    Ok(())
}

fn create_table_sql(q: &str) -> String {
    format!(
        "CREATE TABLE {q} (
             segment_id INTEGER PRIMARY KEY,
             segment_key BLOB NOT NULL,
             lo INTEGER NOT NULL CHECK (lo >= 0),
             hi INTEGER NOT NULL CHECK (hi > lo),
             value BLOB NOT NULL
         ) STRICT"
    )
}

fn create_index_sql(q: &str, key_lo: &str) -> String {
    format!("CREATE INDEX {key_lo} ON {q} (segment_key, lo)")
}

fn create_insert_trigger_sql(q: &str, trigger: &str) -> String {
    format!(
        "CREATE TRIGGER {trigger}
         BEFORE INSERT ON {q}
         WHEN EXISTS (
             SELECT 1 FROM {q}
             WHERE segment_key = NEW.segment_key
               AND lo < NEW.hi AND NEW.lo < hi
         )
         BEGIN SELECT RAISE(ABORT, 'segment overlap'); END"
    )
}

fn create_update_trigger_sql(q: &str, trigger: &str) -> String {
    format!(
        "CREATE TRIGGER {trigger}
         BEFORE UPDATE OF segment_key, lo, hi ON {q}
         WHEN EXISTS (
             SELECT 1 FROM {q}
             WHERE segment_key = NEW.segment_key
               AND segment_id <> OLD.segment_id
               AND lo < NEW.hi AND NEW.lo < hi
         )
         BEGIN SELECT RAISE(ABORT, 'segment overlap'); END"
    )
}

fn normalize_sql(sql: &str) -> String {
    sql.trim_end_matches(';')
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn validate_contents(
    connection: &sqlite::Connection,
    table: &SegmentTableName,
) -> Result<(), SegmentMapError> {
    let q = table.quoted();
    let invalid = connection
        .query_row(
            &format!(
                "SELECT segment_id, lo, hi FROM {q}
                 WHERE lo < 0 OR hi <= lo OR typeof(segment_key) <> 'blob'
                    OR typeof(value) <> 'blob' LIMIT 1"
            ),
            (),
            |row| Ok((row.get::<_, i64>(0)?, row.get(1)?, row.get(2)?)),
        )
        .optional()
        .map_err(|source| SegmentMapError::Sqlite {
            operation: "validate stored ranges",
            source,
        })?;
    if let Some((id, lo, hi)) = invalid {
        return Err(SegmentMapError::CorruptRow { id, lo, hi });
    }
    let overlap = connection
        .query_row(
            &format!(
                "SELECT a.segment_id, a.lo, a.hi, b.segment_id, b.lo, b.hi
                 FROM {q} AS a JOIN {q} AS b
                   ON a.segment_key = b.segment_key
                  AND a.segment_id < b.segment_id
                  AND a.lo < b.hi AND b.lo < a.hi LIMIT 1"
            ),
            (),
            |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, i64>(2)?,
                    row.get::<_, i64>(3)?,
                    row.get::<_, i64>(4)?,
                    row.get::<_, i64>(5)?,
                ))
            },
        )
        .optional()
        .map_err(|source| SegmentMapError::Sqlite {
            operation: "validate stored overlap",
            source,
        })?;
    if let Some((left_id, left_lo, left_hi, right_id, right_lo, right_hi)) = overlap {
        return Err(SegmentMapError::StoredOverlap {
            left: SegmentId(left_id),
            left_range: decode_range(left_lo, left_hi)?,
            right: SegmentId(right_id),
            right_range: decode_range(right_lo, right_hi)?,
        });
    }
    Ok(())
}

type RowData = (i64, Vec<u8>, i64, i64, Vec<u8>);

fn decode_segment(row: &sqlite::Row<'_>) -> sqlite::Result<RowData> {
    Ok((
        row.get(0)?,
        row.get(1)?,
        row.get(2)?,
        row.get(3)?,
        row.get(4)?,
    ))
}

fn validate_segment((id, key, lo, hi, value): RowData) -> Result<Segment, SegmentMapError> {
    Ok(Segment {
        id: SegmentId(id),
        key,
        range: decode_range(lo, hi)?,
        value,
    })
}

fn sqlite_range(range: SegmentRange) -> Result<(i64, i64), SegmentMapError> {
    let lo = i64::try_from(range.lo()).map_err(|_| SegmentMapError::RangeTooLarge { range })?;
    let hi = i64::try_from(range.hi()).map_err(|_| SegmentMapError::RangeTooLarge { range })?;
    Ok((lo, hi))
}

fn decode_range(lo: i64, hi: i64) -> Result<SegmentRange, SegmentMapError> {
    let unsigned_lo =
        u64::try_from(lo).map_err(|_| SegmentMapError::CorruptRow { id: 0, lo, hi })?;
    let unsigned_hi =
        u64::try_from(hi).map_err(|_| SegmentMapError::CorruptRow { id: 0, lo, hi })?;
    SegmentRange::new(unsigned_lo, unsigned_hi).map_err(|_| SegmentMapError::CorruptRow {
        id: 0,
        lo,
        hi,
    })
}

/// Failure to create, open, or operate a persistent segment map.
#[derive(Debug)]
pub enum SegmentMapError {
    /// Caller supplied an unsafe or qualified table name.
    InvalidTableName { name: String },
    /// Existing table does not have the segment-map schema.
    InvalidSchema {
        table: SegmentTableName,
        reason: String,
    },
    /// A stored row has invalid range geometry or storage classes.
    CorruptRow { id: i64, lo: i64, hi: i64 },
    /// Existing rows overlap within one key.
    StoredOverlap {
        left: SegmentId,
        left_range: SegmentRange,
        right: SegmentId,
        right_range: SegmentRange,
    },
    /// Requested insertion intersects a segment with the same key.
    Overlap {
        existing: SegmentId,
        range: SegmentRange,
    },
    /// A range cannot be represented by signed `SQLite` `INTEGER` endpoints.
    RangeTooLarge { range: SegmentRange },
    /// A point cannot be represented by a signed `SQLite` `INTEGER` endpoint.
    PointTooLarge { point: u64 },
    /// `SQLite` operation failed.
    Sqlite {
        operation: &'static str,
        source: sqlite::Error,
    },
}

impl fmt::Display for SegmentMapError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTableName { name } => {
                write!(formatter, "invalid SQLite table name {name:?}")
            }
            Self::InvalidSchema { table, reason } => {
                write!(
                    formatter,
                    "invalid segment-map table {}: {reason}",
                    table.as_str()
                )
            }
            Self::CorruptRow { id, lo, hi } => {
                write!(
                    formatter,
                    "invalid stored segment row {id} with range {lo}..{hi}"
                )
            }
            Self::StoredOverlap {
                left,
                left_range,
                right,
                right_range,
            } => write!(
                formatter,
                "stored segments {} at {}..{} and {} at {}..{} overlap",
                left.get(),
                left_range.lo(),
                left_range.hi(),
                right.get(),
                right_range.lo(),
                right_range.hi()
            ),
            Self::Overlap { existing, range } => write!(
                formatter,
                "segment {} at {}..{} overlaps the requested range",
                existing.get(),
                range.lo(),
                range.hi()
            ),
            Self::RangeTooLarge { range } => write!(
                formatter,
                "range {}..{} exceeds signed SQLite INTEGER",
                range.lo(),
                range.hi()
            ),
            Self::PointTooLarge { point } => {
                write!(formatter, "point {point} exceeds signed SQLite INTEGER")
            }
            Self::Sqlite { operation, source } => {
                write!(formatter, "could not {operation}: {source}")
            }
        }
    }
}

impl Error for SegmentMapError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Sqlite { source, .. } => Some(source),
            _ => None,
        }
    }
}
