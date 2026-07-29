mod private {
    pub trait Sealed {}
}

/// A trusted property maintained by a Nucleus connection.
///
/// This trait is sealed because admitting an invalid starting invariant would
/// invalidate every safe capability derived from the connection.
pub trait Invariant: private::Sealed {}

/// The standard Nucleus invariant.
///
/// Reserved `cov_conn_*` and `cov_db_*` tables have their standard meanings,
/// and every catalog assertion is truthful.
#[derive(Debug)]
pub struct Standard {
    _private: (),
}

impl Standard {
    pub(crate) const fn new() -> Self {
        Self { _private: () }
    }
}

impl private::Sealed for Standard {}
impl Invariant for Standard {}

/// No semantic property is asserted about the enclosed connection.
#[derive(Debug)]
pub struct Unchecked {
    _private: (),
}

impl Unchecked {
    pub(crate) const fn new() -> Self {
        Self { _private: () }
    }
}

impl private::Sealed for Unchecked {}
impl Invariant for Unchecked {}
