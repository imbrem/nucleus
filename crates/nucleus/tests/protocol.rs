use std::convert::Infallible;

use covalence_nucleus::{
    Connection, ConnectionCarrier, MutableConnectionCarrier, SessionProtocol, Standard,
    ViewProtocol,
};

#[derive(Clone, Copy, Debug)]
struct Inspect;

impl<C: ConnectionCarrier> ViewProtocol<C> for Inspect {
    type Error = Infallible;
    type View = C;

    fn view(self, carrier: C) -> Result<C, (Infallible, C)> {
        Ok(carrier)
    }
}

impl<C: MutableConnectionCarrier> SessionProtocol<C> for Inspect {
    type Error = Infallible;
    type Session = C;

    fn enter(self, carrier: C) -> Result<C, (Infallible, C)> {
        Ok(carrier)
    }
}

#[test]
fn application_protocols_choose_view_and_session_carriers_independently() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let shared = connection.view(Inspect).unwrap();
        let _: &Connection<Standard> = shared.connection();
    }

    {
        let mut exclusive = connection.view_mut(Inspect).unwrap();
        let _: &mut Connection<Standard> = exclusive.connection_mut();
    }

    let mut session = connection.session(Inspect).unwrap();
    let _: &mut Connection<Standard> = session.connection_mut();
}

#[test]
fn owned_protocols_can_return_the_original_connection() {
    let connection = Connection::open_in_memory().unwrap();
    let owned = connection.into_session(Inspect).unwrap();
    let connection = owned.into_connection();

    let owned = connection.into_view(Inspect).unwrap();
    let _: Connection<Standard> = owned.into_connection();
}
