//! Const-indexed projections for heterogeneous tuples and homogeneous arrays.
//!
//! [`Proj<I>`] is implemented only when `I` is a valid zero-based index. Its
//! [`Elem`](Proj::Elem) associated type therefore describes the element at
//! that position without repeating it as a trait parameter. [`Arity::LEN`] is
//! the exclusive upper bound: valid indices satisfy `I < LEN`.
//!
//! Both traits are sealed. This lets generic code rely on the implementations
//! and associated types supplied here, and leaves room to extend the supported
//! built-in tuple and array sizes without admitting conflicting downstream
//! implementations.
//!
//! This initial implementation covers tuples through arity 12 and arrays
//! through length 32. Stable Rust cannot yet express `I < N` as a generic impl
//! bound, so valid array/index pairs are enumerated to keep invalid projections
//! out of the type system.

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

macro_rules! impl_array {
    ($len:literal; $($index:literal),* $(,)?) => {
        $(
            impl<T> Proj<$index> for [T; $len] {
                type Elem = T;

                fn project(&self) -> &T {
                    &self[$index]
                }

                fn project_mut(&mut self) -> &mut T {
                    &mut self[$index]
                }

                fn into_project(self) -> T {
                    self.into_iter()
                        .nth($index)
                        .expect("the implementation only names valid indices")
                }
            }
        )*
    };
}

impl<T, const N: usize> sealed::Sealed for [T; N] {}

impl<T, const N: usize> Arity for [T; N] {
    const LEN: usize = N;
}

// Stable Rust cannot yet express `I < N` as a generic impl bound. Enumerating
// valid pairs keeps out-of-bounds projections absent from the type system.
impl_array!(0;);
impl_array!(1; 0);
impl_array!(2; 0, 1);
impl_array!(3; 0, 1, 2);
impl_array!(4; 0, 1, 2, 3);
impl_array!(5; 0, 1, 2, 3, 4);
impl_array!(6; 0, 1, 2, 3, 4, 5);
impl_array!(7; 0, 1, 2, 3, 4, 5, 6);
impl_array!(8; 0, 1, 2, 3, 4, 5, 6, 7);
impl_array!(9; 0, 1, 2, 3, 4, 5, 6, 7, 8);
impl_array!(10; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
impl_array!(11; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
impl_array!(12; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11);
impl_array!(13; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
impl_array!(14; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
impl_array!(15; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14);
impl_array!(16; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
impl_array!(17; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16);
impl_array!(18; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
impl_array!(19; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18);
impl_array!(20; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19);
impl_array!(21; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20);
impl_array!(22; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21);
impl_array!(23; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22);
impl_array!(24; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23);
impl_array!(25; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24);
impl_array!(26; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25);
impl_array!(27; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26);
impl_array!(28; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27);
impl_array!(29; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28);
impl_array!(30; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29);
impl_array!(31; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30);
impl_array!(32; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31);

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

    #[test]
    fn arrays_project_homogeneous_elements() {
        let mut array = [10, 20, 30, 40];

        assert_eq!(*<_ as Proj<0>>::project(&array), 10);
        *<_ as Proj<2>>::project_mut(&mut array) = 31;
        assert_eq!(<_ as Proj<2>>::into_project(array), 31);
        assert_eq!(<[i32; 4] as Arity>::LEN, 4);
        assert_eq!(<[i32; 0] as Arity>::LEN, 0);
    }
}
