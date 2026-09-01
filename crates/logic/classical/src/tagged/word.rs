use covalence_lib_error::snafu::Snafu;

const NEGATIVE_MASK: u64 = 1 << 63;
const PAYLOAD_MASK: u64 = NEGATIVE_MASK - 1;

/// Failure to construct a packed tagged-classical word.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WordError {
    /// The requested literal atom does not fit the 63-bit payload.
    #[snafu(display("literal atom {atom} does not fit the 63-bit payload"))]
    LiteralOverflow {
        /// Rejected atom identifier.
        atom: u64,
    },
    /// A packed array pointer was not nonzero, aligned, and tagged `AND`/`OR`/`SAT`.
    #[snafu(display("invalid packed pointer base {base} with tag {tag}"))]
    InvalidPointer {
        /// Rejected array base.
        base: u64,
        /// Rejected low-bit tag.
        tag: u8,
    },
    /// A metadata value does not fit the 63-bit payload.
    #[snafu(display("metadata value {value} does not fit the 63-bit payload"))]
    MetadataOverflow {
        /// Rejected metadata value.
        value: u64,
    },
    /// Canonical zero cannot be refined to a proposition reference.
    #[snafu(display("zero is not a proposition reference"))]
    ZeroReference,
}

/// One 64-bit sign-magnitude runtime word.
///
/// Bit 63 is polarity. The low 63 bits are an unsigned payload whose bottom
/// two bits are `AND = 0`, `OR = 1`, `SAT = 2`, and `literal = 3`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Word(u64);

impl Word {
    /// Canonical zero, used for null pointers, terminators, and padding.
    pub const ZERO: Self = Self(0);

    /// Recovers a word from its exact machine representation.
    #[must_use]
    pub const fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    /// Returns the exact machine representation.
    #[must_use]
    pub const fn raw(self) -> u64 {
        self.0
    }

    /// Returns the independent polarity bit.
    #[must_use]
    pub const fn is_negative(self) -> bool {
        self.0 & NEGATIVE_MASK != 0
    }

    /// Returns the unsigned 63-bit payload.
    #[must_use]
    pub const fn payload(self) -> u64 {
        self.0 & PAYLOAD_MASK
    }

    /// Returns the low-two-bit constructor tag.
    #[must_use]
    pub const fn tag(self) -> u8 {
        (self.payload() & 3) as u8
    }

    /// Returns the four-aligned payload base.
    #[must_use]
    pub const fn base(self) -> u64 {
        self.payload() & !3
    }

    /// Returns whether this word is a nonzero proposition reference.
    #[must_use]
    pub const fn is_ref(self) -> bool {
        self.payload() != 0
    }

    /// Complements the polarity bit without changing the payload or tag.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self(self.0 ^ NEGATIVE_MASK)
    }

    /// Encodes one literal atom.
    ///
    /// # Errors
    ///
    /// Returns an error when `4 * atom + 3` does not fit the 63-bit payload.
    pub fn literal(atom: u64, negative: bool) -> Result<Self, WordError> {
        let payload = atom
            .checked_mul(4)
            .and_then(|value| value.checked_add(3))
            .filter(|value| *value <= PAYLOAD_MASK)
            .ok_or(WordError::LiteralOverflow { atom })?;
        Ok(Self::with_polarity(payload, negative))
    }

    /// Encodes one aligned, nonzero array pointer.
    ///
    /// # Errors
    ///
    /// Returns an error unless `base` is nonzero and four-aligned, `tag` is
    /// `AND`, `OR`, or `SAT`, and the complete payload fits in 63 bits.
    pub fn pointer(base: u64, tag: u8, negative: bool) -> Result<Self, WordError> {
        let valid = base != 0
            && base.is_multiple_of(4)
            && tag < 3
            && base
                .checked_add(u64::from(tag))
                .is_some_and(|value| value <= PAYLOAD_MASK);
        if !valid {
            return Err(WordError::InvalidPointer { base, tag });
        }
        Ok(Self::with_polarity(base + u64::from(tag), negative))
    }

    /// Encodes one unsigned metadata value.
    ///
    /// # Errors
    ///
    /// Returns an error when the value does not fit the 63-bit payload.
    pub fn natural(value: u64) -> Result<Self, WordError> {
        if value > PAYLOAD_MASK {
            Err(WordError::MetadataOverflow { value })
        } else {
            Ok(Self(value))
        }
    }

    const fn with_polarity(payload: u64, negative: bool) -> Self {
        Self(payload | if negative { NEGATIVE_MASK } else { 0 })
    }
}

/// A checked nonzero packed proposition reference.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Ref(Word);

impl Ref {
    /// Refines a nonzero word to a proposition reference.
    ///
    /// # Errors
    ///
    /// Returns an error for canonical zero and negative zero.
    pub const fn new(word: Word) -> Result<Self, WordError> {
        if word.is_ref() {
            Ok(Self(word))
        } else {
            Err(WordError::ZeroReference)
        }
    }

    /// Returns the underlying machine word.
    #[must_use]
    pub const fn word(self) -> Word {
        self.0
    }

    /// Complements the reference polarity.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self(self.0.negated())
    }
}

impl TryFrom<Word> for Ref {
    type Error = WordError;

    fn try_from(value: Word) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}
