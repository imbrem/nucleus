//! Output modes.

use std::fmt;
use std::str::FromStr;

/// How query results are rendered.
///
/// Five of upstream's twenty-three. The omissions are deliberate: `csv`,
/// `tabs` and `ascii` are `list` with a different separator, `markdown`,
/// `table` and `qbox` are `box` with different glyphs, and the rest —
/// `insert`, `html`, `tcl`, `www`, `jatom`, `jobject`, `split`, `psql`,
/// `line`, `count`, `off`, `c` — serve workflows this shell does not have.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Mode {
    /// Values joined by the separator, one row per line. `SQLite`'s default.
    #[default]
    List,
    /// Aligned columns, sized to their contents.
    Column,
    /// Aligned columns inside Unicode box drawing.
    Box,
    /// A JSON array of objects, one per row.
    Json,
    /// `SQL` literals, joined by commas.
    Quote,
}

impl Mode {
    /// The name accepted by `.mode` and reported by `.mode` with no argument.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::List => "list",
            Self::Column => "column",
            Self::Box => "box",
            Self::Json => "json",
            Self::Quote => "quote",
        }
    }

    /// Whether selecting this mode turns headers on, as upstream does for its
    /// aligned modes.
    #[must_use]
    pub const fn implies_headers(self) -> bool {
        matches!(self, Self::Column | Self::Box)
    }

    /// Every mode, for `.help` and error messages.
    #[must_use]
    pub const fn all() -> [Self; 5] {
        [Self::List, Self::Column, Self::Box, Self::Json, Self::Quote]
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// A `.mode` argument this shell does not have.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnknownMode(pub String);

impl fmt::Display for UnknownMode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "no such mode: {}. Choices are:", self.0)?;
        for mode in Mode::all() {
            write!(formatter, " {mode}")?;
        }
        Ok(())
    }
}

impl std::error::Error for UnknownMode {}

impl FromStr for Mode {
    type Err = UnknownMode;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        match text {
            "list" => Ok(Self::List),
            "column" | "columns" => Ok(Self::Column),
            "box" => Ok(Self::Box),
            "json" => Ok(Self::Json),
            "quote" => Ok(Self::Quote),
            other => Err(UnknownMode(other.to_owned())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_mode_round_trips_through_its_name() {
        for mode in Mode::all() {
            assert_eq!(mode.as_str().parse::<Mode>().unwrap(), mode);
        }
    }

    #[test]
    fn an_unknown_mode_lists_the_choices() {
        let error = "csv".parse::<Mode>().unwrap_err();
        assert_eq!(error, UnknownMode("csv".to_owned()));
        assert!(error.to_string().contains("box"));
    }
}
