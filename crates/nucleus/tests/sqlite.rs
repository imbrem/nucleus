#[test]
fn sqlite_is_available_to_consumers() {
    assert_eq!(covalence_nucleus::smoke(), 42);
}

#[test]
fn trusted_database_installs_extensions_through_the_bootstrap() {
    use covalence_nucleus::{InstallOutcome, TrustedDb};

    let mut database = TrustedDb::create_in_memory().unwrap();
    assert!(database.catalog().metatables().is_empty());
    assert_eq!(
        database.install_rust_types().unwrap(),
        InstallOutcome::Installed
    );
    let mut types = database.rust_types().unwrap();
    assert_eq!(
        types.register::<bool>().unwrap(),
        types.register::<bool>().unwrap()
    );
}
