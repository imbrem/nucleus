//! Exact finite base-10 decimals.
//!
//! [`Decimal`] is a lossless landing zone for decimal literals: text parses to
//! an exact `coefficient × 10^-scale` pair without rounding, and downstream
//! consumers decide how to interpret it. Arithmetic deliberately lives with
//! those consumers, not here.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use covalence_lib_bigint::{BigInt, Sign};

use crate::{Int, Num};

/// Why decimal text could not be parsed exactly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecimalParseError {
    /// The input was empty or contained only a sign.
    Empty,
    /// The input did not match the accepted decimal grammar.
    InvalidSyntax,
    /// The scale overflows `u32`.
    ScaleOverflow,
}

impl fmt::Display for DecimalParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("decimal is empty"),
            Self::InvalidSyntax => formatter.write_str("invalid decimal syntax"),
            Self::ScaleOverflow => formatter.write_str("decimal scale exceeds u32::MAX"),
        }
    }
}

impl Error for DecimalParseError {}

/// Canonical components of an exact decimal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DecimalParts {
    /// Signed arbitrary-precision coefficient.
    pub coefficient: Int,
    /// Number of base-10 fractional places.
    pub scale: u32,
}

/// An exact finite base-10 value.
///
/// The mathematical value is `coefficient × 10^-scale`. The representation is
/// canonical: a non-zero coefficient is never divisible by ten, and zero
/// always has scale zero. Consequently `1`, `1.0`, and `1.00` are one value for
/// equality, ordering, and hashing.
#[derive(Clone)]
pub struct Decimal {
    coefficient: Int,
    scale: u32,
}

impl Decimal {
    /// Zero.
    pub const ZERO: Self = Self {
        coefficient: Int::ZERO,
        scale: 0,
    };

    /// Creates a decimal and removes insignificant trailing zeros.
    #[must_use]
    pub fn new(coefficient: Int, scale: u32) -> Self {
        let (coefficient, scale) = normalize(coefficient.0, scale);
        Self {
            coefficient: Int(coefficient),
            scale,
        }
    }

    /// Returns canonical components.
    #[must_use]
    pub fn into_parts(self) -> DecimalParts {
        DecimalParts {
            coefficient: self.coefficient,
            scale: self.scale,
        }
    }

    /// Returns the canonical coefficient.
    #[must_use]
    pub const fn coefficient(&self) -> &Int {
        &self.coefficient
    }

    /// Returns the canonical scale.
    #[must_use]
    pub const fn scale(&self) -> u32 {
        self.scale
    }

    /// Returns whether this value is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.coefficient.is_zero()
    }
}

impl From<Int> for Decimal {
    fn from(value: Int) -> Self {
        Self::new(value, 0)
    }
}

impl From<Num> for Decimal {
    fn from(value: Num) -> Self {
        Self::from(Int::from(value))
    }
}

impl FromStr for Decimal {
    type Err = DecimalParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse_decimal(input)
    }
}

impl fmt::Display for Decimal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rendered = self.coefficient.to_string();
        let (sign, digits) = rendered
            .strip_prefix('-')
            .map_or(("", rendered.as_str()), |digits| ("-", digits));
        if self.scale == 0 {
            return write!(formatter, "{sign}{digits}");
        }

        let scale = usize::try_from(self.scale).map_err(|_| fmt::Error)?;
        formatter.write_str(sign)?;
        if digits.len() > scale {
            let split = digits.len() - scale;
            formatter.write_str(&digits[..split])?;
            formatter.write_str(".")?;
            formatter.write_str(&digits[split..])
        } else {
            formatter.write_str("0.")?;
            for _ in 0..(scale - digits.len()) {
                formatter.write_str("0")?;
            }
            formatter.write_str(digits)
        }
    }
}

impl fmt::Debug for Decimal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.scale == other.scale && self.coefficient == other.coefficient
    }
}

impl Eq for Decimal {}

impl Hash for Decimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.coefficient.hash(state);
        self.scale.hash(state);
    }
}

impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        let left_sign = self.coefficient.0.sign();
        let right_sign = other.coefficient.0.sign();
        match sign_rank(left_sign).cmp(&sign_rank(right_sign)) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
        if left_sign == Sign::NoSign {
            return Ordering::Equal;
        }
        let ordering = compare_magnitudes(self, other);
        if left_sign == Sign::Minus {
            ordering.reverse()
        } else {
            ordering
        }
    }
}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn normalize(mut coefficient: BigInt, mut scale: u32) -> (BigInt, u32) {
    if coefficient == BigInt::ZERO {
        return (BigInt::ZERO, 0);
    }
    let ten = BigInt::from(10_u8);
    while scale > 0 && (&coefficient % &ten) == BigInt::ZERO {
        coefficient /= &ten;
        scale -= 1;
    }
    (coefficient, scale)
}

fn parse_decimal(input: &str) -> Result<Decimal, DecimalParseError> {
    if input.is_empty() {
        return Err(DecimalParseError::Empty);
    }
    let (negative, unsigned) = match input.as_bytes()[0] {
        b'+' => (false, &input[1..]),
        b'-' => (true, &input[1..]),
        _ => (false, input),
    };
    if unsigned.is_empty() {
        return Err(DecimalParseError::Empty);
    }

    let (mantissa, exponent_text) = split_once_e(unsigned)?;
    let (integer, fraction) = match mantissa.split_once('.') {
        Some((integer, fraction)) => {
            if fraction.contains('.') {
                return Err(DecimalParseError::InvalidSyntax);
            }
            (integer, fraction)
        }
        None => (mantissa, ""),
    };
    if integer.is_empty() && fraction.is_empty() {
        return Err(DecimalParseError::InvalidSyntax);
    }
    if !integer
        .bytes()
        .chain(fraction.bytes())
        .all(|byte| byte.is_ascii_digit())
    {
        return Err(DecimalParseError::InvalidSyntax);
    }

    let exponent = parse_exponent(exponent_text)?;
    let required_scale = i128::try_from(fraction.len()).unwrap_or(i128::MAX) - exponent;
    let digits = format!("{integer}{fraction}");
    let mut coefficient =
        BigInt::parse_bytes(digits.as_bytes(), 10).ok_or(DecimalParseError::InvalidSyntax)?;
    if negative {
        coefficient = -coefficient;
    }

    if required_scale <= 0 {
        let shift = u32::try_from(required_scale.unsigned_abs())
            .map_err(|_| DecimalParseError::ScaleOverflow)?;
        coefficient *= BigInt::from(10_u8).pow(shift);
        Ok(Decimal::new(Int(coefficient), 0))
    } else {
        let scale =
            u32::try_from(required_scale).map_err(|_| DecimalParseError::ScaleOverflow)?;
        Ok(Decimal::new(Int(coefficient), scale))
    }
}

fn split_once_e(input: &str) -> Result<(&str, Option<&str>), DecimalParseError> {
    let mut parts = input.split(['e', 'E']);
    let mantissa = parts.next().expect("split always has one item");
    let exponent = parts.next();
    if parts.next().is_some() || exponent == Some("") {
        return Err(DecimalParseError::InvalidSyntax);
    }
    Ok((mantissa, exponent))
}

fn parse_exponent(input: Option<&str>) -> Result<i128, DecimalParseError> {
    let Some(input) = input else {
        return Ok(0);
    };
    let (negative, digits) = match input.as_bytes().first() {
        Some(b'+') => (false, &input[1..]),
        Some(b'-') => (true, &input[1..]),
        _ => (false, input),
    };
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(DecimalParseError::InvalidSyntax);
    }
    let magnitude = digits
        .parse::<u128>()
        .map_err(|_| DecimalParseError::ScaleOverflow)?;
    let magnitude = i128::try_from(magnitude).map_err(|_| DecimalParseError::ScaleOverflow)?;
    Ok(if negative { -magnitude } else { magnitude })
}

fn compare_magnitudes(left: &Decimal, right: &Decimal) -> Ordering {
    let left_digits = magnitude_digits(&left.coefficient);
    let right_digits = magnitude_digits(&right.coefficient);
    let left_position = left_digits.len() as i128 - i128::from(left.scale);
    let right_position = right_digits.len() as i128 - i128::from(right.scale);
    match left_position.cmp(&right_position) {
        Ordering::Equal => {}
        ordering => return ordering,
    }
    let width = left_digits.len().max(right_digits.len());
    for index in 0..width {
        let left_digit = left_digits.as_bytes().get(index).copied().unwrap_or(b'0');
        let right_digit = right_digits.as_bytes().get(index).copied().unwrap_or(b'0');
        match left_digit.cmp(&right_digit) {
            Ordering::Equal => {}
            ordering => return ordering,
        }
    }
    Ordering::Equal
}

fn magnitude_digits(value: &Int) -> String {
    let rendered = value.to_string();
    rendered.strip_prefix('-').unwrap_or(&rendered).to_owned()
}

const fn sign_rank(sign: Sign) -> u8 {
    match sign {
        Sign::Minus => 0,
        Sign::NoSign => 1,
        Sign::Plus => 2,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;

    use super::*;

    fn decimal(input: &str) -> Decimal {
        input.parse().unwrap()
    }

    fn hash(value: &Decimal) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn normalization_defines_value_identity() {
        let values = ["1", "1.0", "1.00", "01.000", "10e-1"];
        for value in values {
            assert_eq!(decimal(value), decimal("1"));
            assert_eq!(hash(&decimal(value)), hash(&decimal("1")));
        }
        for value in ["0", "-0", "+0.000", "0e100"] {
            assert_eq!(decimal(value), Decimal::ZERO);
            assert_eq!(decimal(value).scale(), 0);
        }
    }

    #[test]
    fn exact_parse_and_canonical_format_round_trip() {
        let vectors = [
            ("-12.3400", "-12.34"),
            (".5", "0.5"),
            ("5.", "5"),
            ("1.25e3", "1250"),
            ("125e-3", "0.125"),
            ("1e-8", "0.00000001"),
        ];
        for (input, canonical) in vectors {
            let value = decimal(input);
            assert_eq!(value.to_string(), canonical);
            assert_eq!(decimal(&value.to_string()), value);
        }
    }

    #[test]
    fn ordering_does_not_expand_large_scale_gaps() {
        let tiny = Decimal::new(Int::from(1_i8), u32::MAX);
        let less_tiny = Decimal::new(Int::from(2_i8), u32::MAX);
        assert!(Decimal::ZERO < tiny);
        assert!(tiny < less_tiny);
        assert!(decimal("-100") < decimal("-0.001"));
        assert!(decimal("9.99") < decimal("10"));
        assert_eq!(decimal("1.0").cmp(&decimal("1")), Ordering::Equal);
    }

    #[test]
    fn very_large_coefficients_and_scales_are_exact() {
        let coefficient = "9".repeat(10_000);
        let value: Decimal = format!("{coefficient}e-10000").parse().unwrap();
        assert_eq!(value.scale(), 10_000);
        assert_eq!(value.to_string().parse::<Decimal>().unwrap(), value);
    }

    #[test]
    fn parts_round_trip_without_loss() {
        for input in ["-12.34", "0.125", "1250", "0.00000001", "0"] {
            let value = decimal(input);
            let DecimalParts { coefficient, scale } = value.clone().into_parts();
            assert_eq!(Decimal::new(coefficient, scale), value);
        }
    }

    #[test]
    fn malformed_forms_are_rejected() {
        for input in ["", "+", ".", "1..0", "1e", "1e+", "1_0", "NaN", "inf"] {
            assert!(input.parse::<Decimal>().is_err(), "{input}");
        }
    }
}
