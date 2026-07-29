use bytes::Bytes;
use covalence_nucleus::{Connection, Registry};

#[test]
fn the_standard_cas_is_available_inside_and_outside_sessions() {
    let mut connection = Connection::open_in_memory().unwrap();
    let before = connection.cas().store(b"before").unwrap();

    {
        let session = connection.enter(Registry).unwrap();
        assert_eq!(
            session.cas().fetch(before).unwrap(),
            Some(Bytes::from_static(b"before"))
        );
        session.cas().store(b"during").unwrap();
    }

    let during = connection.cas().hash(b"during");
    assert_eq!(
        connection.cas().fetch(during).unwrap(),
        Some(Bytes::from_static(b"during"))
    );
}
