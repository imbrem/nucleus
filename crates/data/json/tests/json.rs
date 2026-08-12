//! `Json<I>` across its families: invariants, strictness, and round trips.

use covalence_data_json::{Entry, Json, Local, Map, MapError, Refs, Shared, from_str};

fn document() -> Json {
    Json::object([
        ("zeta", Json::from(1i64)),
        ("alpha", Json::array([Json::Null, Json::from(true)])),
        (
            "mid",
            Json::object([("inner", Json::string("value"))]).unwrap(),
        ),
    ])
    .unwrap()
}

#[test]
fn compact_output_is_sorted_and_whitespace_free() {
    assert_eq!(
        document().to_json_string(),
        r#"{"alpha":[null,true],"mid":{"inner":"value"},"zeta":1}"#
    );
}

#[test]
fn parsing_round_trips_canonically() {
    // Source order and spacing are forgotten; canonical form comes back out.
    let parsed: Json = from_str(r#"{ "zeta": 1, "mid": {"inner": "value"}, "alpha": [null, true] }"#)
        .unwrap();
    assert_eq!(parsed, document());
    assert_eq!(
        from_str::<Shared>(&parsed.to_json_string()).unwrap(),
        parsed
    );
}

#[test]
fn duplicate_keys_are_rejected_everywhere() {
    assert!(matches!(
        Json::<Shared>::object([("k", Json::Null), ("k", Json::Null)]),
        Err(MapError::Duplicate { .. })
    ));
    let error = from_str::<Shared>(r#"{"k": 1, "k": 2}"#).unwrap_err();
    assert!(error.to_string().contains("duplicate object key"), "{error}");
}

#[test]
fn subtree_extraction_shares_rather_than_copies() {
    let document = document();
    let subtree = document.get("mid").unwrap().clone();
    drop(document);
    assert_eq!(subtree.get("inner").unwrap().as_str(), Some("value"));
}

#[test]
fn families_compare_structurally_across_each_other() {
    static INNER: [Json<Refs>; 2] = [Json::Null, Json::Bool(true)];
    let borrowed: Json<Refs> = Json::Array(&INNER[..]);
    let shared: Json = Json::array([Json::Null, Json::from(true)]);
    let local: Json<Local> = Json::array([Json::Null, Json::from(true)]);
    assert_eq!(shared, borrowed);
    assert_eq!(shared, local);
    assert_eq!(borrowed, local);
    assert_ne!(shared, Json::<Shared>::array([Json::Null, Json::from(false)]));
}

#[test]
fn borrowed_maps_still_carry_the_invariant() {
    static ENTRIES: [Entry<Refs>; 2] = [
        Entry {
            key: "a",
            value: Json::Null,
        },
        Entry {
            key: "b",
            value: Json::Bool(false),
        },
    ];
    static UNSORTED: [Entry<Refs>; 2] = [
        Entry {
            key: "b",
            value: Json::Null,
        },
        Entry {
            key: "a",
            value: Json::Null,
        },
    ];
    let map = Map::<Refs>::from_sorted(&ENTRIES[..]).unwrap();
    assert_eq!(map.get("b"), Some(&Json::Bool(false)));
    assert_eq!(
        Map::<Refs>::from_sorted(&UNSORTED[..]).unwrap_err(),
        MapError::Unsorted { index: 1 }
    );
}

#[test]
fn numbers_stay_exact_and_finite() {
    let parsed: Json = from_str("[0, -1, 18446744073709551615, 0.5]").unwrap();
    let numbers = parsed.as_array().unwrap();
    assert_eq!(numbers[0].as_number().unwrap().as_i64(), Some(0));
    assert_eq!(numbers[1].as_number().unwrap().as_i64(), Some(-1));
    assert_eq!(
        numbers[2].as_number().unwrap().as_u64(),
        Some(u64::MAX),
        "u64::MAX must not sag into a float"
    );
    assert_eq!(numbers[3].as_number().unwrap().as_f64(), Some(0.5));
    assert!(Json::<Shared>::from_f64(f64::NAN).is_none());
    assert!(Json::<Shared>::from_f64(f64::INFINITY).is_none());
}

#[test]
fn value_conversions_round_trip() {
    let value: covalence_lib_json::Value =
        covalence_lib_json::from_str(r#"{"b": [1, 2], "a": "x"}"#).unwrap();
    let json: Json = Json::from(&value);
    assert_eq!(covalence_lib_json::Value::from(&json), value);
    assert_eq!(json.to_json_string(), r#"{"a":"x","b":[1,2]}"#);
}

#[test]
fn structural_hash_agrees_with_equality() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(document());
    assert!(set.contains(&from_str::<Shared>(&document().to_json_string()).unwrap()));
}

#[test]
fn accessors_report_kinds() {
    let document = document();
    assert_eq!(document.kind(), "object");
    assert_eq!(document.get("zeta").unwrap().kind(), "number");
    assert!(Json::<Shared>::Null.is_null());
    assert_eq!(document.get_index(0), None, "objects do not index by position");
}

#[test]
fn ordering_is_total_and_consistent_with_equality() {
    use std::cmp::Ordering;
    let ranked: Vec<Json> = vec![
        Json::Null,
        Json::from(false),
        Json::from(true),
        Json::from(-2i64),
        Json::from_f64(-1.5).unwrap(),
        Json::from(1i64),
        Json::from_f64(1.0).unwrap(), // a numeric tie orders the integer first
        Json::from_f64(1.5).unwrap(),
        Json::from(u64::MAX),
        Json::from_f64(2e19).unwrap(), // just above u64::MAX
        Json::string("a"),
        Json::string("b"),
        Json::array([]),
        Json::array([Json::Null]),
        Json::object::<&str>([]).unwrap(),
        Json::object([("a", Json::Null)]).unwrap(),
    ];
    for (i, left) in ranked.iter().enumerate() {
        for (j, right) in ranked.iter().enumerate() {
            assert_eq!(left.cmp(right), i.cmp(&j), "{left} versus {right}");
            assert_eq!(left.cmp(right) == Ordering::Equal, left == right);
        }
    }
}

#[test]
fn large_integers_and_floats_compare_exactly() {
    // u64::MAX rounds to 2^64 as a float; exact comparison must not equate them.
    let int = Json::<Shared>::from(u64::MAX);
    let float = Json::<Shared>::from_f64(18_446_744_073_709_551_616.0).unwrap();
    assert_eq!(int.cmp(&float), std::cmp::Ordering::Less);
    assert_eq!(float.cmp(&int), std::cmp::Ordering::Greater);
    // Distinct large integers must stay distinct despite equal float images.
    let near = Json::<Shared>::from(u64::MAX - 1);
    assert_eq!(near.cmp(&int), std::cmp::Ordering::Less);
}

#[test]
fn shared_subtrees_compare_equal_without_descending() {
    let document = document();
    let clone = document.clone();
    assert_eq!(document, clone);
    let extracted = document.get("mid").unwrap().clone();
    assert_eq!(document.get("mid").unwrap(), &extracted);
    let respliced = Json::object([("renamed", extracted)]).unwrap();
    assert_eq!(
        respliced.get("renamed").unwrap(),
        document.get("mid").unwrap()
    );
}

#[test]
fn json_works_as_a_btree_key() {
    use std::collections::BTreeSet;
    let mut set = BTreeSet::new();
    set.insert(document());
    set.insert(Json::from(1i64));
    set.insert(Json::from_f64(1.0).unwrap());
    assert_eq!(set.len(), 3, "1 and 1.0 are distinct JSON numbers");
    assert!(set.contains(&document()));
}
