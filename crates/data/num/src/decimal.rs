//! Exact finite base-10 decimals.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

use covalence_lib_bigint::{BigInt, Sign};

use crate::{Int, Num};

/// Default maximum number of coefficient digits accepted by [`Decimal::parse_with_limit`].
pub const DEFAULT_MAX_DECIMAL_DIGITS: usize = 1024 * 1024;

/// Default maximum scale accepted by [`Decimal::parse_with_limit`].
pub const DEFAULT_MAX_DECIMAL_SCALE: u32 = 1024 * 1024;

/// Resource bounds for parsing untrusted decimal text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DecimalLimit {
    max_digits: usize,
    max_scale: u32,
}

impl DecimalLimit {
    /// Creates parsing bounds.
    #[must_use]
    pub const fn new(max_digits: usize, max_scale: u32) -> Self {
        Self {
            max_digits,
            max_scale,
        }
    }

    /// Returns the maximum coefficient digit count.
    #[must_use]
    pub const fn max_digits(self) -> usize {
        self.max_digits
    }

    /// Returns the maximum scale.
    #[must_use]
    pub const fn max_scale(self) -> u32 {
        self.max_scale
    }
}

impl Default for DecimalLimit {
    fn default() -> Self {
        Self::new(DEFAULT_MAX_DECIMAL_DIGITS, DEFAULT_MAX_DECIMAL_SCALE)
    }
}

/// Why decimal text could not be parsed exactly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecimalParseError {
    /// The input was empty or contained only a sign.
    Empty,
    /// The input did not match the accepted decimal grammar.
    InvalidSyntax,
    /// The coefficient has too many digits.
    DigitLimitExceeded {
        /// Number of coefficient digits in the input.
        actual: usize,
        /// Configured maximum.
        limit: usize,
    },
    /// The represented scale exceeds the configured limit.
    ScaleLimitExceeded {
        /// Required scale.
        actual: u64,
        /// Configured maximum.
        limit: u32,
    },
}

impl fmt::Display for DecimalParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("decimal is empty"),
            Self::InvalidSyntax => formatter.write_str("invalid decimal syntax"),
            Self::DigitLimitExceeded { actual, limit } => {
                write!(formatter, "decimal has {actual} digits; limit is {limit}")
            }
            Self::ScaleLimitExceeded { actual, limit } => {
                write!(formatter, "decimal scale is {actual}; limit is {limit}")
            }
        }
    }
}

impl Error for DecimalParseError {}

/// Why exact decimal division could not produce a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecimalDivisionError {
    /// The divisor was zero.
    DivisionByZero,
    /// The quotient has a non-terminating base-10 expansion.
    NonTerminating,
    /// The exact quotient requires a scale larger than [`u32::MAX`].
    ScaleOverflow,
}

impl fmt::Display for DecimalDivisionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DivisionByZero => formatter.write_str("division by zero"),
            Self::NonTerminating => {
                formatter.write_str("quotient has a non-terminating decimal expansion")
            }
            Self::ScaleOverflow => formatter.write_str("exact quotient scale exceeds u32::MAX"),
        }
    }
}

impl Error for DecimalDivisionError {}

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

    /// Parses the exact grammar `[+-]?digits[.digits]?[e[+-]?digits]?`.
    ///
    /// The integer or fractional digit sequence may be empty only when the
    /// other one is non-empty. Exponent notation changes the value exactly; it
    /// never rounds.
    ///
    /// # Errors
    ///
    /// Returns a syntax or resource-limit error before constructing an
    /// over-limit coefficient or scale.
    pub fn parse_with_limit(input: &str, limit: DecimalLimit) -> Result<Self, DecimalParseError> {
        parse_decimal(input, limit)
    }

    /// Divides only when the quotient has a finite base-10 expansion.
    ///
    /// # Errors
    ///
    /// Returns [`DecimalDivisionError::NonTerminating`] rather than selecting
    /// an implicit precision or rounding mode.
    pub fn checked_div(&self, rhs: &Self) -> Result<Self, DecimalDivisionError> {
        if rhs.is_zero() {
            return Err(DecimalDivisionError::DivisionByZero);
        }
        if self.is_zero() {
            return Ok(Self::ZERO);
        }

        let mut numerator = self.coefficient.0.clone();
        let mut denominator = rhs.coefficient.0.clone();
        if denominator.sign() == Sign::Minus {
            numerator = -numerator;
            denominator = -denominator;
        }

        let divisor = gcd(abs(numerator.clone()), denominator.clone());
        numerator /= &divisor;
        denominator /= divisor;

        let two = BigInt::from(2_u8);
        let five = BigInt::from(5_u8);
        let mut twos = 0_u32;
        let mut fives = 0_u32;
        while (&denominator % &two) == BigInt::ZERO {
            denominator /= &two;
            twos = twos
                .checked_add(1)
                .ok_or(DecimalDivisionError::ScaleOverflow)?;
        }
        while (&denominator % &five) == BigInt::ZERO {
            denominator /= &five;
            fives = fives
                .checked_add(1)
                .ok_or(DecimalDivisionError::ScaleOverflow)?;
        }
        if denominator != BigInt::from(1_u8) {
            return Err(DecimalDivisionError::NonTerminating);
        }

        let quotient_scale = twos.max(fives);
        if twos < quotient_scale {
            numerator *= two.pow(quotient_scale - twos);
        }
        if fives < quotient_scale {
            numerator *= five.pow(quotient_scale - fives);
        }

        let signed_scale = i64::from(self.scale) - i64::from(rhs.scale) + i64::from(quotient_scale);
        if signed_scale < 0 {
            let shift =
                u32::try_from(-signed_scale).map_err(|_| DecimalDivisionError::ScaleOverflow)?;
            numerator *= BigInt::from(10_u8).pow(shift);
            Ok(Self::new(Int(numerator), 0))
        } else {
            let scale =
                u32::try_from(signed_scale).map_err(|_| DecimalDivisionError::ScaleOverflow)?;
            Ok(Self::new(Int(numerator), scale))
        }
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
        Self::parse_with_limit(input, DecimalLimit::default())
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

fn parse_decimal(input: &str, limit: DecimalLimit) -> Result<Decimal, DecimalParseError> {
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
    let digit_count =
        integer
            .len()
            .checked_add(fraction.len())
            .ok_or(DecimalParseError::DigitLimitExceeded {
                actual: usize::MAX,
                limit: limit.max_digits,
            })?;
    if digit_count > limit.max_digits {
        return Err(DecimalParseError::DigitLimitExceeded {
            actual: digit_count,
            limit: limit.max_digits,
        });
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
        let shift = required_scale.unsigned_abs();
        if shift > u128::from(limit.max_scale) {
            return Err(DecimalParseError::ScaleLimitExceeded {
                actual: u64::try_from(shift).unwrap_or(u64::MAX),
                limit: limit.max_scale,
            });
        }
        let shift = u32::try_from(shift).map_err(|_| DecimalParseError::ScaleLimitExceeded {
            actual: u64::MAX,
            limit: limit.max_scale,
        })?;
        coefficient *= BigInt::from(10_u8).pow(shift);
        Ok(Decimal::new(Int(coefficient), 0))
    } else {
        let actual = u64::try_from(required_scale).unwrap_or(u64::MAX);
        if actual > u64::from(limit.max_scale) {
            return Err(DecimalParseError::ScaleLimitExceeded {
                actual,
                limit: limit.max_scale,
            });
        }
        let scale = u32::try_from(actual).map_err(|_| DecimalParseError::ScaleLimitExceeded {
            actual,
            limit: limit.max_scale,
        })?;
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
        .map_err(|_| DecimalParseError::ScaleLimitExceeded {
            actual: u64::MAX,
            limit: DEFAULT_MAX_DECIMAL_SCALE,
        })?;
    let magnitude =
        i128::try_from(magnitude).map_err(|_| DecimalParseError::ScaleLimitExceeded {
            actual: u64::MAX,
            limit: DEFAULT_MAX_DECIMAL_SCALE,
        })?;
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

fn abs(value: BigInt) -> BigInt {
    if value.sign() == Sign::Minus {
        -value
    } else {
        value
    }
}

fn gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    while right != BigInt::ZERO {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    left
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
    fn parsing_enforces_hostile_input_limits() {
        let limit = DecimalLimit::new(4, 8);
        assert_eq!(
            Decimal::parse_with_limit("12345", limit),
            Err(DecimalParseError::DigitLimitExceeded {
                actual: 5,
                limit: 4
            })
        );
        assert_eq!(
            Decimal::parse_with_limit("1e-9", limit),
            Err(DecimalParseError::ScaleLimitExceeded {
                actual: 9,
                limit: 8
            })
        );
    }

    #[test]
    fn exact_division_rejects_non_terminating_results() {
        assert_eq!(
            decimal("1").checked_div(&decimal("3")),
            Err(DecimalDivisionError::NonTerminating)
        );
        assert_eq!(
            decimal("1").checked_div(&Decimal::ZERO),
            Err(DecimalDivisionError::DivisionByZero)
        );
        assert_eq!(
            decimal("1").checked_div(&decimal("8")).unwrap(),
            decimal("0.125")
        );
        assert_eq!(
            decimal("1.2").checked_div(&decimal("0.5")).unwrap(),
            decimal("2.4")
        );
        assert_eq!(
            decimal("-10").checked_div(&decimal("4")).unwrap(),
            decimal("-2.5")
        );
    }

    #[test]
    fn very_large_coefficients_and_scales_are_exact() {
        let coefficient = "9".repeat(10_000);
        let value = Decimal::parse_with_limit(
            &format!("{coefficient}e-10000"),
            DecimalLimit::new(10_000, 10_000),
        )
        .unwrap();
        assert_eq!(value.scale(), 10_000);
        assert_eq!(value.to_string().parse::<Decimal>().unwrap(), value);
    }

    #[test]
    fn malformed_forms_are_rejected() {
        for input in ["", "+", ".", "1..0", "1e", "1e+", "1_0", "NaN", "inf"] {
            assert!(input.parse::<Decimal>().is_err(), "{input}");
        }
    }
}
