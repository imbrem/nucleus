//! Dense arena representation and its specialized kernel operations.

use crate::{ArenaRepr, Error, Expr, Kernel as GenericKernel, Kind, Row, Tm, Ty, sealed};

/// Dense signed-offset arena storage.
///
/// This value alone is untrusted. Only a `Kernel<Arena>` is an admitted
/// kernel witness.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Arena {
    pub(crate) offset: i64,
    pub(crate) rows: Vec<Row>,
}

impl Arena {
    #[must_use]
    pub const fn offset(&self) -> i64 {
        self.offset
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.rows.len()
    }

    pub(crate) fn rows(&self) -> &[Row] {
        &self.rows
    }

    pub(crate) fn from_untrusted(offset: i64, rows: Vec<Row>) -> Self {
        Self { offset, rows }
    }

    fn push(&mut self, row: Row) -> Result<i64, Error> {
        let length = i64::try_from(self.rows.len()).map_err(|_| Error::ArenaFull)?;
        let index = self
            .offset
            .checked_add(length)
            .ok_or(Error::IndexOverflow)?;
        self.rows.push(row);
        Ok(index)
    }
}

impl sealed::Sealed for Arena {}
impl ArenaRepr for Arena {}

/// The dense kernel specialization.
pub type Kernel = GenericKernel<Arena>;

impl GenericKernel<Arena> {
    /// Constructs the empty, sound dense arena.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            arena: Arena {
                offset: 0,
                rows: Vec::new(),
            },
        }
    }

    /// Appends the kind `Star`, whose sort is `Kind`.
    ///
    /// # Errors
    ///
    /// Returns an error if the next signed arena index is not representable.
    pub fn star(&mut self) -> Result<Kind, Error> {
        let index = self.arena.push(Row::syntax(Expr::KindStar))?;
        Ok(Kind { index })
    }

    /// Appends the Boolean type. Duplicate rows are allowed.
    ///
    /// # Errors
    ///
    /// Returns an error if the next signed arena index is not representable.
    pub fn bool_ty(&mut self) -> Result<Ty, Error> {
        let index = self.arena.push(Row::syntax(Expr::BoolTy))?;
        Ok(Ty { index })
    }

    /// Appends a Boolean constant. Duplicate rows are allowed.
    ///
    /// # Errors
    ///
    /// Returns an error if the next signed arena index is not representable.
    pub fn bool_const(&mut self, value: bool) -> Result<Tm, Error> {
        let index = self.arena.push(Row::syntax(Expr::Bool(value)))?;
        Ok(Tm { index })
    }
}

impl Default for GenericKernel<Arena> {
    fn default() -> Self {
        Self::empty()
    }
}
