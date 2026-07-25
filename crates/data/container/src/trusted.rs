use std::{ops::Deref, rc::Rc, sync::Arc};

mod sealed {
    pub trait TrustedDeref {}
    pub trait TrustedListIndex {}
}

/// An audited dereference wrapper with a stable target value.
///
/// The trait is sealed so adding a wrapper is an explicit trust decision. It
/// does not claim that the target address is immovable or that interior
/// mutation is absent; it guarantees only that dereferencing follows the
/// wrapper's documented ownership/borrowing relationship to a value of [`T`].
///
/// [`T`]: TrustedDeref::T
pub trait TrustedDeref: sealed::TrustedDeref + Deref<Target = Self::T> {
    /// The stable dereference target.
    type T: ?Sized;

    /// Borrows the trusted target.
    fn trusted_deref(&self) -> &Self::T {
        self
    }
}

macro_rules! impl_trusted_deref {
    ($wrapper:ty) => {
        impl<T: ?Sized> sealed::TrustedDeref for $wrapper {}

        impl<T: ?Sized> TrustedDeref for $wrapper {
            type T = T;
        }
    };
}

impl_trusted_deref!(&T);
impl_trusted_deref!(&mut T);
impl_trusted_deref!(Box<T>);
impl_trusted_deref!(Rc<T>);
impl_trusted_deref!(Arc<T>);

/// An audited, stable list-indexing implementation.
///
/// The built-in implementations cover slices, arrays, and [`Vec`], including
/// arbitrary nesting inside [`TrustedDeref`] wrappers supported by this crate.
pub trait TrustedListIndex: sealed::TrustedListIndex {
    /// The indexed element type.
    type T;

    /// Returns the number of elements.
    fn len(&self) -> usize;

    /// Returns whether the list contains no elements.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Borrows the element at `index`, or returns `None` when out of bounds.
    fn get(&self, index: usize) -> Option<&Self::T>;

    /// Borrows the element at `index`.
    ///
    /// # Panics
    ///
    /// Panics when `index >= self.len()`.
    fn index(&self, index: usize) -> &Self::T {
        self.get(index)
            .expect("trusted list index is within bounds")
    }
}

impl<T> sealed::TrustedListIndex for [T] {}

impl<T> TrustedListIndex for [T] {
    type T = T;

    fn len(&self) -> usize {
        <[T]>::len(self)
    }

    fn get(&self, index: usize) -> Option<&T> {
        <[T]>::get(self, index)
    }
}

impl<T, const N: usize> sealed::TrustedListIndex for [T; N] {}

impl<T, const N: usize> TrustedListIndex for [T; N] {
    type T = T;

    fn len(&self) -> usize {
        N
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.as_slice().get(index)
    }
}

impl<T> sealed::TrustedListIndex for Vec<T> {}

impl<T> TrustedListIndex for Vec<T> {
    type T = T;

    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.as_slice().get(index)
    }
}

macro_rules! impl_wrapped_list {
    ($wrapper:ty) => {
        impl<L> sealed::TrustedListIndex for $wrapper where L: TrustedListIndex + ?Sized {}

        impl<L> TrustedListIndex for $wrapper
        where
            L: TrustedListIndex + ?Sized,
        {
            type T = L::T;

            fn len(&self) -> usize {
                let target: &L = self;
                TrustedListIndex::len(target)
            }

            fn get(&self, index: usize) -> Option<&Self::T> {
                let target: &L = self;
                TrustedListIndex::get(target, index)
            }
        }
    };
}

impl_wrapped_list!(&L);
impl_wrapped_list!(&mut L);
impl_wrapped_list!(Box<L>);
impl_wrapped_list!(Rc<L>);
impl_wrapped_list!(Arc<L>);

#[cfg(test)]
mod tests {
    use std::{rc::Rc, sync::Arc};

    use super::{TrustedDeref, TrustedListIndex};

    fn first<L: TrustedListIndex + ?Sized>(list: &L) -> Option<&L::T> {
        list.get(0)
    }

    #[test]
    fn trusted_deref_covers_owned_shared_and_borrowed_wrappers() {
        let boxed = Box::new(String::from("boxed"));
        let shared = Rc::new(String::from("shared"));
        let atomic = Arc::new(String::from("atomic"));
        let borrowed = &*boxed;

        assert_eq!(TrustedDeref::trusted_deref(&boxed), "boxed");
        assert_eq!(TrustedDeref::trusted_deref(&shared), "shared");
        assert_eq!(TrustedDeref::trusted_deref(&atomic), "atomic");
        assert_eq!(TrustedDeref::trusted_deref(&borrowed), "boxed");
    }

    #[test]
    fn list_indexing_forwards_through_nested_trusted_wrappers() {
        let array = [10, 20, 30];
        let slice: &[i32] = &array;
        let vector = vec![40, 50];
        let nested = Arc::new(Box::new(vector));

        assert_eq!(first(&array), Some(&10));
        assert_eq!(first(slice), Some(&10));
        assert_eq!(first(&nested), Some(&40));
        assert_eq!(TrustedListIndex::len(&nested), 2);
        assert_eq!(TrustedListIndex::get(&nested, 2), None);
        assert_eq!(*TrustedListIndex::index(&nested, 1), 50);
    }
}
