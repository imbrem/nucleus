//! Exact, portable numeric value types.
//!
//! [`Num`] is a non-negative arbitrary-precision integer and [`Int`] is a
//! signed arbitrary-precision integer. [`Float32`] and [`Float64`] preserve the
//! complete identity of IEEE 754 binary bit patterns. Their backing
//! representations are private; use canonical bytes at storage and runtime
//! boundaries.

use std::error::Error;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use covalence_lib_bigint::{BigInt, BigUint, Sign};

mod decimal;
mod float;

pub use decimal::{Decimal, DecimalDivisionError, DecimalParseError, DecimalParts};
pub use float::{Float32, Float64, FloatClass, InexactFloatConversion};

/// A canonical integer decoding error.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecodeError {
    /// The input was empty.
    Empty,
    /// The representation was not the unique encoding of its value.
    NonCanonical,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("integer encoding is empty"),
            Self::NonCanonical => formatter.write_str("integer encoding is not canonical"),
        }
    }
}

impl Error for DecodeError {}

/// An arithmetic operation that is not defined for the supplied operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArithmeticError {
    /// A natural-number subtraction would produce a negative result.
    NegativeResult,
    /// Division by zero was requested.
    DivisionByZero,
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NegativeResult => {
                formatter.write_str("natural-number subtraction would be negative")
            }
            Self::DivisionByZero => formatter.write_str("division by zero"),
        }
    }
}

impl Error for ArithmeticError {}

/// A non-negative arbitrary-precision integer, including zero.
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Num(pub(crate) BigUint);

impl Num {
    /// Zero.
    pub const ZERO: Self = Self(BigUint::ZERO);

    /// Returns whether this value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0 == BigUint::ZERO
    }

    /// Returns the unique unsigned big-endian representation.
    ///
    /// Zero is encoded as `[0]`; every other value has no leading zero byte.
    #[must_use]
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let bytes = self.0.to_bytes_be();
        if bytes.is_empty() { vec![0] } else { bytes }
    }

    /// Decodes a canonical unsigned big-endian representation.
    ///
    /// # Errors
    ///
    /// Rejects empty and leading-zero representations.
    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.is_empty() {
            return Err(DecodeError::Empty);
        }
        if bytes.len() > 1 && bytes[0] == 0 {
            return Err(DecodeError::NonCanonical);
        }
        Ok(Self(BigUint::from_bytes_be(bytes)))
    }

    /// Subtracts without permitting a negative result.
    ///
    /// # Errors
    ///
    /// Returns [`ArithmeticError::NegativeResult`] when `rhs > self`.
    pub fn checked_sub(&self, rhs: &Self) -> Result<Self, ArithmeticError> {
        if self < rhs {
            Err(ArithmeticError::NegativeResult)
        } else {
            Ok(Self(&self.0 - &rhs.0))
        }
    }

    /// Returns the quotient and remainder.
    ///
    /// # Errors
    ///
    /// Returns [`ArithmeticError::DivisionByZero`] for a zero divisor.
    pub fn div_rem(&self, rhs: &Self) -> Result<(Self, Self), ArithmeticError> {
        if rhs.is_zero() {
            return Err(ArithmeticError::DivisionByZero);
        }
        Ok((Self(&self.0 / &rhs.0), Self(&self.0 % &rhs.0)))
    }
}

impl fmt::Debug for Num {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl fmt::Display for Num {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, formatter)
    }
}

/// A signed arbitrary-precision mathematical integer.
#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Int(pub(crate) BigInt);

impl Int {
    /// Zero.
    pub const ZERO: Self = Self(BigInt::ZERO);

    /// Returns whether this value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0 == BigInt::ZERO
    }

    /// Returns the unique two's-complement big-endian representation.
    ///
    /// The encoding is the shortest byte sequence preserving the sign. Zero is
    /// `[0]`; positive values whose high bit is set have a leading zero byte.
    #[must_use]
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        self.0.to_signed_bytes_be()
    }

    /// Decodes a canonical two's-complement big-endian representation.
    ///
    /// # Errors
    ///
    /// Rejects empty and redundant sign-extension bytes.
    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.is_empty() {
            return Err(DecodeError::Empty);
        }
        let value = BigInt::from_signed_bytes_be(bytes);
        if value.to_signed_bytes_be() != bytes {
            return Err(DecodeError::NonCanonical);
        }
        Ok(Self(value))
    }

    /// Returns the quotient and remainder, truncating the quotient toward zero.
    ///
    /// # Errors
    ///
    /// Returns [`ArithmeticError::DivisionByZero`] for a zero divisor.
    pub fn div_rem(&self, rhs: &Self) -> Result<(Self, Self), ArithmeticError> {
        if rhs.is_zero() {
            return Err(ArithmeticError::DivisionByZero);
        }
        Ok((Self(&self.0 / &rhs.0), Self(&self.0 % &rhs.0)))
    }
}

impl fmt::Debug for Int {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl fmt::Display for Int {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, formatter)
    }
}

macro_rules! impl_unsigned {
    ($($type:ty),+ $(,)?) => {$(
        impl From<$type> for Num {
            fn from(value: $type) -> Self {
                Self(BigUint::from(value))
            }
        }

        impl TryFrom<&Num> for $type {
            type Error = PrimitiveConversionError;

            fn try_from(value: &Num) -> Result<Self, Self::Error> {
                let bytes = value.0.to_bytes_be();
                if bytes.len() > std::mem::size_of::<$type>() {
                    return Err(PrimitiveConversionError);
                }
                let mut output = [0; std::mem::size_of::<$type>()];
                let start = output.len() - bytes.len();
                output[start..].copy_from_slice(&bytes);
                Ok(<$type>::from_be_bytes(output))
            }
        }

        impl TryFrom<Num> for $type {
            type Error = PrimitiveConversionError;

            fn try_from(value: Num) -> Result<Self, Self::Error> {
                Self::try_from(&value)
            }
        }
    )+};
}

impl_unsigned!(u8, u16, u32, u64, u128, usize);

/// A value cannot be represented by the requested primitive or sign domain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrimitiveConversionError;

impl fmt::Display for PrimitiveConversionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("value is outside the destination type's range")
    }
}

impl Error for PrimitiveConversionError {}

macro_rules! impl_signed {
    ($($type:ty),+ $(,)?) => {$(
        impl From<$type> for Int {
            fn from(value: $type) -> Self {
                Self(BigInt::from(value))
            }
        }

        impl TryFrom<&Int> for $type {
            type Error = PrimitiveConversionError;

            fn try_from(value: &Int) -> Result<Self, Self::Error> {
                let bytes = value.0.to_signed_bytes_be();
                let padding = if value.0.sign() == Sign::Minus { u8::MAX } else { 0 };
                if bytes.len() > std::mem::size_of::<$type>() {
                    return Err(PrimitiveConversionError);
                }
                let mut output = [padding; std::mem::size_of::<$type>()];
                let start = output.len() - bytes.len();
                output[start..].copy_from_slice(&bytes);
                Ok(<$type>::from_be_bytes(output))
            }
        }

        impl TryFrom<Int> for $type {
            type Error = PrimitiveConversionError;

            fn try_from(value: Int) -> Result<Self, Self::Error> {
                Self::try_from(&value)
            }
        }

        impl TryFrom<$type> for Num {
            type Error = PrimitiveConversionError;

            fn try_from(value: $type) -> Result<Self, Self::Error> {
                BigUint::try_from(value)
                    .map(Self)
                    .map_err(|_| PrimitiveConversionError)
            }
        }
    )+};
}

impl_signed!(i8, i16, i32, i64, i128, isize);

impl From<Num> for Int {
    fn from(value: Num) -> Self {
        Self(BigInt::from(value.0))
    }
}

impl From<&Num> for Int {
    fn from(value: &Num) -> Self {
        Self(BigInt::from(value.0.clone()))
    }
}

impl TryFrom<Int> for Num {
    type Error = PrimitiveConversionError;

    fn try_from(value: Int) -> Result<Self, Self::Error> {
        value
            .0
            .to_biguint()
            .map(Self)
            .ok_or(PrimitiveConversionError)
    }
}

impl TryFrom<&Int> for Num {
    type Error = PrimitiveConversionError;

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        value
            .0
            .to_biguint()
            .map(Self)
            .ok_or(PrimitiveConversionError)
    }
}

impl<'b> Add<&'b Num> for &Num {
    type Output = Num;

    fn add(self, rhs: &'b Num) -> Self::Output {
        Num(&self.0 + &rhs.0)
    }
}

impl<'b> Mul<&'b Num> for &Num {
    type Output = Num;

    fn mul(self, rhs: &'b Num) -> Self::Output {
        Num(&self.0 * &rhs.0)
    }
}

impl<'b> Add<&'b Int> for &Int {
    type Output = Int;

    fn add(self, rhs: &'b Int) -> Self::Output {
        Int(&self.0 + &rhs.0)
    }
}

impl<'b> Sub<&'b Int> for &Int {
    type Output = Int;

    fn sub(self, rhs: &'b Int) -> Self::Output {
        Int(&self.0 - &rhs.0)
    }
}

impl<'b> Mul<&'b Int> for &Int {
    type Output = Int;

    fn mul(self, rhs: &'b Int) -> Self::Output {
        Int(&self.0 * &rhs.0)
    }
}

impl Neg for &Int {
    type Output = Int;

    fn neg(self) -> Self::Output {
        Int(-&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values_beyond_u128_round_trip() {
        let bytes = [0x80; 33];
        let value = Num::from_canonical_bytes(&bytes).unwrap();
        assert_eq!(value.to_canonical_bytes(), bytes);
        assert_eq!(u128::try_from(&value), Err(PrimitiveConversionError));
    }

    #[test]
    fn num_encoding_is_unique() {
        assert_eq!(Num::ZERO.to_canonical_bytes(), [0]);
        assert_eq!(
            Num::from_canonical_bytes(&[0, 1]),
            Err(DecodeError::NonCanonical)
        );
        assert_eq!(Num::from_canonical_bytes(&[]), Err(DecodeError::Empty));
    }

    #[test]
    fn int_encoding_handles_sign_edges() {
        let vectors = [
            (0_i16, vec![0]),
            (127, vec![0x7f]),
            (128, vec![0, 0x80]),
            (-128, vec![0x80]),
            (-129, vec![0xff, 0x7f]),
        ];
        for (primitive, bytes) in vectors {
            let value = Int::from(primitive);
            assert_eq!(value.to_canonical_bytes(), bytes);
            assert_eq!(Int::from_canonical_bytes(&bytes).unwrap(), value);
        }
        assert_eq!(
            Int::from_canonical_bytes(&[0, 1]),
            Err(DecodeError::NonCanonical)
        );
    }

    #[test]
    fn partial_arithmetic_is_explicit() {
        let one = Num::from(1_u8);
        let two = Num::from(2_u8);
        assert_eq!(one.checked_sub(&two), Err(ArithmeticError::NegativeResult));
        assert_eq!(
            two.div_rem(&Num::ZERO),
            Err(ArithmeticError::DivisionByZero)
        );
        assert_eq!(two.div_rem(&one).unwrap(), (two.clone(), Num::ZERO));
    }

    #[test]
    fn arithmetic_identities_hold_beyond_primitives() {
        let large = Num::from_canonical_bytes(&[1; 33]).unwrap();
        let three = Num::from(3_u8);
        let product = &large * &three;
        let (quotient, remainder) = product.div_rem(&three).unwrap();
        assert_eq!(quotient, large);
        assert_eq!(remainder, Num::ZERO);
    }

    #[test]
    fn exact_cross_domain_conversions() {
        let positive = Int::from(42_i8);
        assert_eq!(Num::try_from(&positive).unwrap(), Num::from(42_u8));
        assert_eq!(
            Num::try_from(Int::from(-1_i8)),
            Err(PrimitiveConversionError)
        );
        assert_eq!(
            Int::from(Num::from(u128::MAX)).to_string(),
            u128::MAX.to_string()
        );
    }
}
