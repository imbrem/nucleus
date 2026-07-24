#[test]
fn sqlite_is_available_to_consumers() {
    assert_eq!(covalence_nucleus::smoke(), 42);
}
