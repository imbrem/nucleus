use covalence_data_segment::SegmentRange;
use covalence_nucleus::{Connection, SegmentMap, SegmentMapError};

fn range(lo: u64, hi: u64) -> SegmentRange {
    SegmentRange::new(lo, hi).expect("non-empty range")
}

#[test]
fn prepared_adapter_supports_keyed_point_range_and_remove() {
    let connection = Connection::open_in_memory().expect("open connection");
    let mut segments = connection
        .create_segment_map("file_segments")
        .expect("create segment map");

    let first = segments
        .insert(b"file-a", range(0, 10), b"first")
        .expect("insert first");
    let second = segments
        .insert(b"file-a", range(10, 20), b"second")
        .expect("insert adjacent");
    segments
        .insert(b"file-b", range(5, 15), b"other namespace")
        .expect("same geometry under another key");

    assert_eq!(segments.table().as_str(), "file_segments");
    assert_eq!(
        segments.get(b"file-a", 9).expect("point query").unwrap().id,
        first
    );
    assert_eq!(
        segments
            .get(b"file-a", 10)
            .expect("point query")
            .unwrap()
            .id,
        second
    );
    assert!(segments.get(b"file-a", 20).expect("point query").is_none());

    let overlap = segments
        .overlapping(b"file-a", range(8, 12))
        .expect("range query");
    assert_eq!(
        overlap.iter().map(|segment| segment.id).collect::<Vec<_>>(),
        [first, second]
    );

    let removed = segments.remove(first).expect("remove").expect("row exists");
    assert_eq!(removed.key, b"file-a");
    assert_eq!(removed.value, b"first");
    assert!(segments.remove(first).expect("repeat remove").is_none());
}

#[test]
fn overlap_is_rejected_only_within_the_same_key() {
    let connection = Connection::open_in_memory().expect("open connection");
    let mut segments = connection
        .create_segment_map("segments")
        .expect("create segment map");
    let first = segments
        .insert(b"a", range(10, 20), b"resident")
        .expect("insert");

    assert!(matches!(
        segments.insert(b"a", range(19, 21), b"overlap"),
        Err(SegmentMapError::Overlap { existing, range: old })
            if existing == first && old == range(10, 20)
    ));
    segments
        .insert(b"b", range(19, 21), b"different key")
        .expect("different key may overlap");
}

#[test]
fn sqlite_triggers_guard_writes_outside_the_adapter() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    {
        let mut segments = SegmentMap::create(&neutron, "segments").expect("create map");
        segments
            .insert(b"a", range(10, 20), b"resident")
            .expect("insert");
    }

    let error = neutron
        .sqlite()
        .execute(
            "INSERT INTO segments (segment_key, lo, hi, value) VALUES (?1, ?2, ?3, ?4)",
            (b"a".as_slice(), 15_i64, 25_i64, b"outside".as_slice()),
        )
        .expect_err("trigger rejects overlap");
    assert!(error.to_string().contains("segment overlap"));

    neutron
        .sqlite()
        .execute(
            "INSERT INTO segments (segment_key, lo, hi, value) VALUES (?1, ?2, ?3, ?4)",
            (b"b".as_slice(), 15_i64, 25_i64, b"other key".as_slice()),
        )
        .expect("other key does not overlap");

    neutron
        .sqlite()
        .execute(
            "INSERT INTO segments (segment_key, lo, hi, value) VALUES (?1, ?2, ?3, ?4)",
            (b"a".as_slice(), 20_i64, 30_i64, b"adjacent".as_slice()),
        )
        .expect("insert adjacent row for update test");
    let update_error = neutron
        .sqlite()
        .execute(
            "UPDATE segments SET lo = 19 WHERE segment_key = ?1 AND lo = 20",
            [b"a".as_slice()],
        )
        .expect_err("update trigger rejects overlap");
    assert!(update_error.to_string().contains("segment overlap"));
    assert_eq!(
        neutron
            .sqlite()
            .query_row(
                "SELECT lo FROM segments WHERE segment_key = ?1 AND hi = 30",
                [b"a".as_slice()],
                |row| row.get::<_, i64>(0),
            )
            .expect("failed update leaves geometry unchanged"),
        20
    );
}

#[test]
fn failed_create_removes_partial_schema_without_touching_outer_state() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    neutron
        .sqlite()
        .execute_batch(
            "SAVEPOINT caller_scope;
             CREATE TABLE caller_marker (value INTEGER) STRICT;
             CREATE TABLE broken_key_lo (collision INTEGER) STRICT;",
        )
        .expect("prepare outer state and derived-name collision");

    assert!(matches!(
        SegmentMap::create(&neutron, "broken"),
        Err(SegmentMapError::Sqlite { .. })
    ));
    assert_eq!(
        neutron
            .sqlite()
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema WHERE name = 'broken'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("query partial table"),
        0
    );
    assert_eq!(
        neutron
            .sqlite()
            .query_row("SELECT count(*) FROM caller_marker", (), |row| {
                row.get::<_, i64>(0)
            })
            .expect("caller savepoint remains active"),
        0
    );
    neutron
        .sqlite()
        .execute_batch("RELEASE caller_scope")
        .expect("caller retains control of outer savepoint");
}

#[test]
fn failed_open_cleans_up_only_its_validation_snapshot() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    neutron
        .sqlite()
        .execute_batch(
            "SAVEPOINT caller_scope;
             CREATE TABLE caller_marker (value INTEGER) STRICT;",
        )
        .expect("prepare outer state");

    assert!(matches!(
        SegmentMap::open(&neutron, "missing"),
        Err(SegmentMapError::InvalidSchema { .. })
    ));
    neutron
        .sqlite()
        .execute("INSERT INTO caller_marker VALUES (42)", ())
        .expect("outer transaction remains writable");
    neutron
        .sqlite()
        .execute_batch("RELEASE caller_scope")
        .expect("caller retains control of outer savepoint");
}

#[test]
fn open_checks_schema_guards_and_stored_invariants() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    neutron
        .sqlite()
        .execute_batch(
            "CREATE TABLE malformed (
                 segment_id INTEGER PRIMARY KEY,
                 segment_key BLOB NOT NULL,
                 lo INTEGER NOT NULL,
                 hi INTEGER NOT NULL,
                 value BLOB NOT NULL
             ) STRICT;
             CREATE TRIGGER malformed_no_overlap_insert BEFORE INSERT ON malformed
                 BEGIN SELECT 1; END;
             CREATE TRIGGER malformed_no_overlap_update BEFORE UPDATE ON malformed
                 BEGIN SELECT 1; END;
             INSERT INTO malformed (segment_key, lo, hi, value)
                 VALUES (X'01', 8, 8, X'02');",
        )
        .expect("create malformed table");

    assert!(matches!(
        SegmentMap::open(&neutron, "malformed"),
        Err(SegmentMapError::InvalidSchema { .. })
    ));

    neutron
        .sqlite()
        .execute_batch(
            "CREATE TABLE unguarded (
                 segment_id INTEGER PRIMARY KEY,
                 segment_key BLOB NOT NULL,
                 lo INTEGER NOT NULL CHECK (lo >= 0),
                 hi INTEGER NOT NULL CHECK (hi > lo),
                 value BLOB NOT NULL
             ) STRICT;",
        )
        .expect("create unguarded table");
    assert!(matches!(
        SegmentMap::open(&neutron, "unguarded"),
        Err(SegmentMapError::InvalidSchema { .. })
    ));
}

#[test]
fn open_detects_stored_overlap_even_with_valid_schema_guards() {
    let neutron = covalence_neutron::Connection::open_in_memory().expect("open connection");
    {
        let mut segments =
            SegmentMap::create(&neutron, "stored_overlap").expect("create segment map");
        segments
            .insert(b"a", range(0, 10), b"first")
            .expect("insert first");
    }
    neutron
        .sqlite()
        .execute_batch(
            "DROP TRIGGER stored_overlap_no_overlap_insert;
             INSERT INTO stored_overlap (segment_key, lo, hi, value)
                 VALUES (X'61', 5, 15, X'7365636f6e64');
             CREATE TRIGGER \"stored_overlap_no_overlap_insert\"
             BEFORE INSERT ON \"stored_overlap\"
             WHEN EXISTS (
                 SELECT 1 FROM \"stored_overlap\"
                 WHERE segment_key = NEW.segment_key
                   AND lo < NEW.hi AND NEW.lo < hi
             )
             BEGIN SELECT RAISE(ABORT, 'segment overlap'); END;",
        )
        .expect("inject overlap and restore guard");

    assert!(matches!(
        SegmentMap::open(&neutron, "stored_overlap"),
        Err(SegmentMapError::StoredOverlap { .. })
    ));
}

#[test]
fn table_names_and_signed_integer_boundary_are_checked() {
    let connection = Connection::open_in_memory().expect("open connection");
    assert!(matches!(
        connection.create_segment_map("main.segments"),
        Err(SegmentMapError::InvalidTableName { .. })
    ));
    assert!(matches!(
        connection.create_segment_map("segments; DROP TABLE x"),
        Err(SegmentMapError::InvalidTableName { .. })
    ));

    let mut segments = connection
        .create_segment_map("segments")
        .expect("create map");
    let beyond_sqlite = range(i64::MAX as u64, i64::MAX as u64 + 1);
    assert!(matches!(
        segments.insert(b"a", beyond_sqlite, b"value"),
        Err(SegmentMapError::RangeTooLarge { range }) if range == beyond_sqlite
    ));
    assert!(matches!(
        segments.get(b"a", i64::MAX as u64 + 1),
        Err(SegmentMapError::PointTooLarge { .. })
    ));
}
