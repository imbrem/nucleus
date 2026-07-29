use covalence_nucleus::{Connection, Standard, Unchecked};

#[test]
fn fresh_memory_admits_the_standard_invariant() {
    let connection = Connection::open_in_memory().unwrap();
    let _: &Connection<Standard> = &connection;
    let _: &Standard = connection.invariant();
    assert!(connection.catalog("main").is_ok());
    assert!(connection.catalog("temp").is_ok());
}

#[test]
fn external_state_is_unchecked_until_validated() {
    let path =
        std::env::temp_dir().join(format!("nucleus-unchecked-{}.sqlite", std::process::id()));
    let connection = Connection::open(&path).unwrap();
    let _: &Connection<Unchecked> = &connection;
    let _: &Unchecked = connection.invariant();
    drop(connection);
    std::fs::remove_file(path).unwrap();
}

#[test]
fn serialized_state_does_not_recover_trust_by_itself() {
    let connection = Connection::open_in_memory().unwrap();
    let bytes = connection.serialize().unwrap();
    let restored = Connection::deserialize(&bytes).unwrap();
    let _: &Connection<Unchecked> = &restored;
}
