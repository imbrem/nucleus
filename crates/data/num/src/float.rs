//! Portable, bit-preserving IEEE 754 values.
//!
//! These types deliberately model bit patterns rather than Rust's numeric
//! equality. In particular, NaN payloads and the sign of zero are part of a
//! value's identity.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};

/// The IEEE 754 class of a floating-point bit pattern.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FloatClass {
    /// Positive or negative zero.
    Zero,
    /// A finite, nonzero value below the normal range.
    Subnormal,
    /// A finite value in the normal range.
    Normal,
    /// Positive or negative infinity.
    Infinite,
    /// A quiet or signaling not-a-number value.
    Nan,
}

/// An exact conversion between floating-point formats was not possible.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InexactFloatConversion;

impl fmt::Display for InexactFloatConversion {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("value is not exactly representable in the destination format")
    }
}

impl Error for InexactFloatConversion {}

macro_rules! float_type {
    (
        $(#[$metadata:meta])*
        $name:ident,
        $primitive:ty,
        $bits:ty,
        $bytes:literal,
        $sign:expr,
        $exponent:expr,
        $fraction:expr
    ) => {
        $(#[$metadata])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Default)]
        pub struct $name($bits);

        impl $name {
            /// Positive zero.
            pub const ZERO: Self = Self(0);

            /// Creates a value from its complete IEEE 754 representation.
            #[must_use]
            pub const fn from_bits(bits: $bits) -> Self {
                Self(bits)
            }

            /// Returns the complete IEEE 754 representation.
            #[must_use]
            pub const fn to_bits(self) -> $bits {
                self.0
            }

            /// Creates a value from its canonical big-endian wire bytes.
            #[must_use]
            pub const fn from_wire_bytes(bytes: [u8; $bytes]) -> Self {
                Self(<$bits>::from_be_bytes(bytes))
            }

            /// Returns the canonical big-endian wire bytes.
            #[must_use]
            pub const fn to_wire_bytes(self) -> [u8; $bytes] {
                self.0.to_be_bytes()
            }

            /// Creates a value while retaining every bit of a Rust primitive.
            #[must_use]
            pub fn from_primitive(value: $primitive) -> Self {
                Self(value.to_bits())
            }

            /// Returns the corresponding Rust primitive without changing bits.
            #[must_use]
            pub fn to_primitive(self) -> $primitive {
                <$primitive>::from_bits(self.0)
            }

            /// Classifies the represented value.
            #[must_use]
            pub const fn classify(self) -> FloatClass {
                let exponent = self.0 & $exponent;
                let fraction = self.0 & $fraction;
                if exponent == 0 {
                    if fraction == 0 {
                        FloatClass::Zero
                    } else {
                        FloatClass::Subnormal
                    }
                } else if exponent == $exponent {
                    if fraction == 0 {
                        FloatClass::Infinite
                    } else {
                        FloatClass::Nan
                    }
                } else {
                    FloatClass::Normal
                }
            }

            /// Returns whether the sign bit is set.
            ///
            /// This observes the sign of zero and NaN as well as finite values.
            #[must_use]
            pub const fn is_sign_negative(self) -> bool {
                self.0 & $sign != 0
            }

            /// Returns whether this bit pattern represents a NaN.
            #[must_use]
            pub const fn is_nan(self) -> bool {
                matches!(self.classify(), FloatClass::Nan)
            }

            /// Returns whether this bit pattern represents a finite value.
            #[must_use]
            pub const fn is_finite(self) -> bool {
                matches!(
                    self.classify(),
                    FloatClass::Zero | FloatClass::Subnormal | FloatClass::Normal
                )
            }
        }

        impl From<$primitive> for $name {
            fn from(value: $primitive) -> Self {
                Self::from_primitive(value)
            }
        }

        impl From<$name> for $primitive {
            fn from(value: $name) -> Self {
                value.to_primitive()
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        impl Eq for $name {}

        impl Hash for $name {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.0.hash(state);
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.to_primitive().total_cmp(&other.to_primitive())
            }
        }

        impl PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    formatter,
                    "{}({:#0width$x})",
                    stringify!($name),
                    self.0,
                    width = 2 + $bytes * 2
                )
            }
        }
    };
}

float_type!(
    /// An IEEE 754 binary32 bit pattern.
    Float32,
    f32,
    u32,
    4,
    0x8000_0000,
    0x7f80_0000,
    0x007f_ffff
);

float_type!(
    /// An IEEE 754 binary64 bit pattern.
    Float64,
    f64,
    u64,
    8,
    0x8000_0000_0000_0000,
    0x7ff0_0000_0000_0000,
    0x000f_ffff_ffff_ffff
);

impl Float32 {
    /// Widens binary32 to binary64 exactly.
    ///
    /// NaN sign, signaling/quiet state, and payload bits are preserved by
    /// placing the binary32 significand in the high bits of the binary64
    /// significand.
    #[must_use]
    pub const fn widen(self) -> Float64 {
        let bits = self.0;
        let sign = ((bits >> 31) as u64) << 63;
        let exponent = (bits >> 23) & 0xff;
        let fraction = bits & 0x007f_ffff;

        let magnitude = match (exponent, fraction) {
            (0, 0) => 0,
            (0, fraction) => {
                let leading = fraction.ilog2();
                let exponent64 = (leading as u64) + 874;
                let fraction64 = ((fraction ^ (1_u32 << leading)) as u64) << (52 - leading);
                (exponent64 << 52) | fraction64
            }
            (0xff, fraction) => 0x7ff0_0000_0000_0000 | ((fraction as u64) << 29),
            (exponent, fraction) => {
                let exponent64 = (exponent as u64) + 896;
                (exponent64 << 52) | ((fraction as u64) << 29)
            }
        };
        Float64(sign | magnitude)
    }
}

impl Float64 {
    /// Narrows to binary32 only when every identity-bearing bit is preserved.
    ///
    /// This rejects finite values that would round, overflow, or underflow. A
    /// NaN is accepted only if its payload has the exact widened binary32 form.
    ///
    /// # Errors
    ///
    /// Returns [`InexactFloatConversion`] when no binary32 value widens back
    /// to this exact binary64 bit pattern.
    #[allow(clippy::cast_possible_truncation)]
    pub fn try_narrow(self) -> Result<Float32, InexactFloatConversion> {
        let exponent = self.0 & 0x7ff0_0000_0000_0000;
        if exponent == 0x7ff0_0000_0000_0000 {
            let sign = ((self.0 >> 63) as u32) << 31;
            let fraction = self.0 & 0x000f_ffff_ffff_ffff;
            if fraction & ((1_u64 << 29) - 1) != 0 {
                return Err(InexactFloatConversion);
            }
            let candidate = Float32::from_bits(sign | 0x7f80_0000 | ((fraction >> 29) as u32));
            return if candidate.widen() == self {
                Ok(candidate)
            } else {
                Err(InexactFloatConversion)
            };
        }

        let candidate = Float32::from_primitive(self.to_primitive() as f32);
        if candidate.widen() == self {
            Ok(candidate)
        } else {
            Err(InexactFloatConversion)
        }
    }
}

impl From<Float32> for Float64 {
    fn from(value: Float32) -> Self {
        value.widen()
    }
}

impl TryFrom<Float64> for Float32 {
    type Error = InexactFloatConversion;

    fn try_from(value: Float64) -> Result<Self, Self::Error> {
        value.try_narrow()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeSet, HashSet};

    #[test]
    fn classification_covers_binary32_boundaries() {
        let vectors = [
            (0x0000_0000, FloatClass::Zero),
            (0x8000_0000, FloatClass::Zero),
            (0x0000_0001, FloatClass::Subnormal),
            (0x007f_ffff, FloatClass::Subnormal),
            (0x0080_0000, FloatClass::Normal),
            (0x7f7f_ffff, FloatClass::Normal),
            (0x7f80_0000, FloatClass::Infinite),
            (0xff80_0000, FloatClass::Infinite),
            (0x7f80_0001, FloatClass::Nan),
            (0x7fc0_0000, FloatClass::Nan),
            (0xffff_ffff, FloatClass::Nan),
        ];
        for (bits, class) in vectors {
            assert_eq!(Float32::from_bits(bits).classify(), class);
        }
    }

    #[test]
    fn classification_covers_binary64_boundaries() {
        let vectors = [
            (0x0000_0000_0000_0000, FloatClass::Zero),
            (0x8000_0000_0000_0000, FloatClass::Zero),
            (0x0000_0000_0000_0001, FloatClass::Subnormal),
            (0x000f_ffff_ffff_ffff, FloatClass::Subnormal),
            (0x0010_0000_0000_0000, FloatClass::Normal),
            (0x7fef_ffff_ffff_ffff, FloatClass::Normal),
            (0x7ff0_0000_0000_0000, FloatClass::Infinite),
            (0xfff0_0000_0000_0000, FloatClass::Infinite),
            (0x7ff0_0000_0000_0001, FloatClass::Nan),
            (0x7ff8_0000_0000_0000, FloatClass::Nan),
            (0xffff_ffff_ffff_ffff, FloatClass::Nan),
        ];
        for (bits, class) in vectors {
            assert_eq!(Float64::from_bits(bits).classify(), class);
        }
    }

    #[test]
    fn identity_and_hash_preserve_nan_payloads_and_signed_zero() {
        let values = [
            Float32::from_bits(0),
            Float32::from_bits(0x8000_0000),
            Float32::from_bits(0x7f80_0001),
            Float32::from_bits(0x7fc0_0001),
            Float32::from_bits(0xffc0_0001),
        ];
        assert_eq!(values.into_iter().collect::<HashSet<_>>().len(), 5);
        assert_eq!(values.into_iter().collect::<BTreeSet<_>>().len(), 5);
    }

    #[test]
    fn wire_and_primitive_round_trips_preserve_every_bit() {
        for bits in [
            0_u64,
            0x8000_0000_0000_0000,
            1,
            0x7ff0_0000_0000_0001,
            0x7ff8_dead_beef_cafe,
            u64::MAX,
        ] {
            let value = Float64::from_bits(bits);
            assert_eq!(Float64::from_wire_bytes(value.to_wire_bytes()), value);
            assert_eq!(Float64::from_primitive(value.to_primitive()), value);
        }
    }

    #[test]
    fn widening_is_exact_and_preserves_nan_fields() {
        for bits in [
            0_u32,
            0x8000_0000,
            1,
            0x007f_ffff,
            0x0080_0000,
            0x3f80_0000,
            0x7f80_0000,
            0x7f80_0001,
            0x7fc0_1234,
            u32::MAX,
        ] {
            let source = Float32::from_bits(bits);
            let widened = source.widen();
            assert_eq!(widened.try_narrow(), Ok(source));
        }
    }

    #[test]
    fn narrowing_rejects_rounding_overflow_and_extra_nan_payload_bits() {
        assert_eq!(
            Float64::from_bits(0x3ff0_0000_0000_0001).try_narrow(),
            Err(InexactFloatConversion)
        );
        assert_eq!(
            Float64::from_bits(0x7fe0_0000_0000_0000).try_narrow(),
            Err(InexactFloatConversion)
        );
        assert_eq!(
            Float64::from_bits(0x7ff8_0000_0000_0001).try_narrow(),
            Err(InexactFloatConversion)
        );
    }

    #[test]
    fn ordering_is_total_and_consistent_with_identity() {
        let mut values = [
            Float64::from_bits(0xfff8_0000_0000_0001),
            Float64::from_bits(0x8000_0000_0000_0000),
            Float64::ZERO,
            Float64::from_bits(0x7ff8_0000_0000_0001),
            Float64::from_bits(0x7ff8_0000_0000_0002),
        ];
        values.sort();
        for pair in values.windows(2) {
            assert!(pair[0] < pair[1]);
        }
    }
}
