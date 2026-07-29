use std::ops::Deref;

/// A value admitted by the Nucleus kernel.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Thm<T>(T);

impl<T> Thm<T> {
    pub(crate) const fn new(value: T) -> Self {
        Self(value)
    }
}

impl<T> Deref for Thm<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
