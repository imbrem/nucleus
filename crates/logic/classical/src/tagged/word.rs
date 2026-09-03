use covalence_lib_error::snafu::Snafu;

const NEGATIVE_MASK: u32 = 1 << 31;
const PAYLOAD_MASK: u32 = NEGATIVE_MASK - 1;

/// Failure to construct a packed tagged-classical word.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WordError {
    /// The requested literal atom does not fit the payload.
    #[snafu(display("literal atom {atom} does not fit the word payload"))]
    LiteralOverflow {
        /// Rejected atom identifier.
        atom: u32,
    },
    /// A packed reference was neither an aligned pointer nor a literal.
    #[snafu(display("invalid packed reference base {base} with low bits {tag}"))]
    InvalidPointer {
        /// Rejected array base.
        base: u32,
        /// Rejected low-bit tag.
        tag: u8,
    },
    /// A metadata value does not fit the payload.
    #[snafu(display("metadata value {value} does not fit the word payload"))]
    MetadataOverflow {
        /// Rejected metadata value.
        value: u32,
    },
    /// Canonical zero cannot be refined to a proposition reference.
    #[snafu(display("zero is not a proposition reference"))]
    ZeroReference,
}

/// One 32-bit sign-magnitude runtime word.
///
/// Bit 31 is polarity. The low 31 bits are an unsigned payload whose bottom
/// two bits distinguish aligned pointers (`00`) from literal immediates (`11`).
/// A pointed-to live header stores its connective, size class, and refcount.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Word(u32);

impl Word {
    /// Canonical zero, used for null pointers, terminators, and padding.
    pub const ZERO: Self = Self(0);

    /// Recovers a word from its exact machine representation.
    #[must_use]
    pub const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// Returns the exact machine representation.
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }

    /// Returns the independent polarity bit.
    #[must_use]
    pub const fn is_negative(self) -> bool {
        self.0 & NEGATIVE_MASK != 0
    }

    /// Returns the unsigned payload.
    #[must_use]
    pub const fn payload(self) -> u32 {
        self.0 & PAYLOAD_MASK
    }

    /// Returns the low-two-bit constructor tag.
    #[must_use]
    pub const fn tag(self) -> u8 {
        (self.payload() & 3) as u8
    }

    /// Returns the four-aligned payload base.
    #[must_use]
    pub const fn base(self) -> u32 {
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
    /// Returns an error when `4 * atom + 3` does not fit the payload.
    pub fn literal(atom: u32, negative: bool) -> Result<Self, WordError> {
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
    /// Returns an error unless `base` is nonzero, four-aligned, and fits the
    /// payload. The constructor is stored in the target header.
    pub fn pointer(base: u32, negative: bool) -> Result<Self, WordError> {
        let valid = base != 0 && base.is_multiple_of(4) && base <= PAYLOAD_MASK;
        if !valid {
            return Err(WordError::InvalidPointer { base, tag: 0 });
        }
        Ok(Self::with_polarity(base, negative))
    }

    /// Encodes one unsigned metadata value.
    ///
    /// # Errors
    ///
    /// Returns an error when the value does not fit the payload.
    pub fn natural(value: u32) -> Result<Self, WordError> {
        if value > PAYLOAD_MASK {
            Err(WordError::MetadataOverflow { value })
        } else {
            Ok(Self(value))
        }
    }

    const fn with_polarity(payload: u32, negative: bool) -> Self {
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
        if word.is_ref() && (word.tag() == 0 || word.tag() == 3) {
            Ok(Self(word))
        } else if word.is_ref() {
            Err(WordError::InvalidPointer {
                base: word.base(),
                tag: word.tag(),
            })
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
    #[cfg(test)]
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
