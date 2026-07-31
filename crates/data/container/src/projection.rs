//! Const-indexed projections for heterogeneous tuples.
//!
//! [`Proj<I>`] is implemented only when `I` is a valid zero-based index. Its
//! [`Elem`](Proj::Elem) associated type therefore describes the element at
//! that position without repeating it as a trait parameter. [`Arity::LEN`] is
//! the exclusive upper bound: valid indices satisfy `I < LEN`.
//!
//! Both traits are sealed. This lets generic code rely on the implementations
//! and associated types supplied here, and leaves room to extend the supported
//! built-in tuple sizes without admitting conflicting downstream
//! implementations. This initial implementation covers tuples through arity
//! 12.

mod sealed {
    pub trait Sealed {}
}

/// A sealed product type with a statically known number of elements.
pub trait Arity: sealed::Sealed {
    /// The number of elements and exclusive upper bound for projection indices.
    const LEN: usize;
}

/// Projection at the zero-based const index `I`.
///
/// This trait is implemented only for valid indices. For example,
/// `(A, B, C): Proj<0, Elem = A> + Proj<1, Elem = B> + Proj<2, Elem = C>`,
/// while `Proj<3>` is not implemented.
///
/// ```compile_fail
/// use covalence_data_container::Proj;
///
/// fn fourth<P: Proj<3>>(product: &P) -> &P::Elem {
///     product.project()
/// }
///
/// fourth(&("a", "b", "c"));
/// ```
pub trait Proj<const I: usize>: Arity {
    /// The element type at `I`.
    type Elem;

    /// Borrows the element at `I`.
    fn project(&self) -> &Self::Elem;

    /// Mutably borrows the element at `I`.
    fn project_mut(&mut self) -> &mut Self::Elem;

    /// Replaces the element at `I`, returning its previous value.
    fn replace(&mut self, element: Self::Elem) -> Self::Elem {
        std::mem::replace(self.project_mut(), element)
    }

    /// Consumes the product and returns the element at `I`.
    fn into_project(self) -> Self::Elem;
}

impl sealed::Sealed for () {}

impl Arity for () {
    const LEN: usize = 0;
}

macro_rules! impl_tuple {
    ($len:literal; $($index:tt => $type:ident),+ $(,)?) => {
        impl<$($type),+> sealed::Sealed for ($($type,)+) {}

        impl<$($type),+> Arity for ($($type,)+) {
            const LEN: usize = $len;
        }

        impl_tuple_projections!(($($type),+); $($index => $type),+);
    };
}

macro_rules! impl_tuple_projections {
    (($($all:ident),+); $index:tt => $element:ident $(, $rest_index:tt => $rest_element:ident)*) => {
        impl<$($all),+> Proj<$index> for ($($all,)+) {
            type Elem = $element;

            fn project(&self) -> &Self::Elem {
                &self.$index
            }

            fn project_mut(&mut self) -> &mut Self::Elem {
                &mut self.$index
            }

            fn into_project(self) -> Self::Elem {
                self.$index
            }
        }

        impl_tuple_projections!(($($all),+); $($rest_index => $rest_element),*);
    };
    (($($all:ident),+);) => {};
}

impl_tuple!(1; 0 => A);
impl_tuple!(2; 0 => A, 1 => B);
impl_tuple!(3; 0 => A, 1 => B, 2 => C);
impl_tuple!(4; 0 => A, 1 => B, 2 => C, 3 => D);
impl_tuple!(5; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E);
impl_tuple!(6; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F);
impl_tuple!(7; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G);
impl_tuple!(8; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G, 7 => H);
impl_tuple!(9; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G, 7 => H, 8 => I);
impl_tuple!(10; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G, 7 => H, 8 => I, 9 => J);
impl_tuple!(11; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G, 7 => H, 8 => I, 9 => J, 10 => K);
impl_tuple!(12; 0 => A, 1 => B, 2 => C, 3 => D, 4 => E, 5 => F, 6 => G, 7 => H, 8 => I, 9 => J, 10 => K, 11 => L);

#[cfg(test)]
mod tests {
    use super::{Arity, Proj};

    fn second<P: Proj<1>>(product: &P) -> &P::Elem {
        product.project()
    }

    #[test]
    fn heterogeneous_tuple_projection_uses_an_associated_type() {
        let mut tuple = (7_u8, String::from("middle"), false);

        let value: &String = <_ as Proj<1>>::project(&tuple);
        assert_eq!(value, "middle");
        assert_eq!(second(&tuple), "middle");

        let previous = <_ as Proj<1>>::replace(&mut tuple, String::from("new"));
        assert_eq!(previous, "middle");
        assert_eq!(tuple.1, "new");

        let last: bool = <_ as Proj<2>>::into_project(tuple);
        assert!(!last);
        assert_eq!(<(u8, String, bool) as Arity>::LEN, 3);
    }
}
