use std::io::Cursor;

use covalence_logic_lean::{Error, read};

fn fixture(name: &str) -> &'static [u8] {
    match name {
        "valid-minimal" => include_bytes!("fixtures/valid-minimal.ndjson"),
        "version-skew" => include_bytes!("fixtures/version-skew.ndjson"),
        "unsupported-record" => include_bytes!("fixtures/unsupported-record.ndjson"),
        "forward-reference" => include_bytes!("fixtures/forward-reference.ndjson"),
        "duplicate-index" => include_bytes!("fixtures/duplicate-index.ndjson"),
        "malformed-json" => include_bytes!("fixtures/malformed-json.ndjson"),
        _ => panic!("unknown fixture"),
    }
}

#[test]
fn reads_pinned_minimal_export() {
    let export = read(Cursor::new(fixture("valid-minimal"))).expect("valid fixture");
    assert_eq!(export.metadata.format_version, "3.1.0");
    assert_eq!(export.names, 2);
    assert_eq!(export.levels, 1);
    assert_eq!(export.expressions, 4);
    assert_eq!(export.declarations, 1);
}

#[test]
fn version_skew_fails_explicitly() {
    assert!(matches!(
        read(Cursor::new(fixture("version-skew"))),
        Err(Error::Version { .. })
    ));
}

#[test]
fn unsupported_records_fail_explicitly() {
    assert!(matches!(
        read(Cursor::new(fixture("unsupported-record"))),
        Err(Error::Unsupported { .. })
    ));
}

#[test]
fn malformed_and_index_failures_are_distinct() {
    assert!(matches!(
        read(Cursor::new(fixture("forward-reference"))),
        Err(Error::Reference { .. })
    ));
    assert!(matches!(
        read(Cursor::new(fixture("duplicate-index"))),
        Err(Error::Index { .. })
    ));
    assert!(matches!(
        read(Cursor::new(fixture("malformed-json"))),
        Err(Error::Framing { .. })
    ));
}
