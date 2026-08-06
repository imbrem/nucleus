//! Dot commands: tokenising a line, and what it means.

use std::fmt;

use crate::mode::{Mode, UnknownMode};

/// A dot command this shell understands.
///
/// Thirteen of upstream's eighty-one. Everything that mutates a database
/// through the shell rather than through `SQL` (`.import`, `.restore`,
/// `.clone`, `.backup`, `.recover`), everything diagnostic (`.stats`,
/// `.scanstats`, `.testctrl`, `.filectrl`, `.dbinfo`, `.expert`, `.lint`),
/// and everything that reaches outside the process (`.shell`, `.system`,
/// `.load`, `.archive`, `.excel`) is absent on purpose.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Command {
    /// `.open [--readonly] [FILE|URI]` — replace the connection.
    Open {
        /// Whether to open read-only.
        readonly: bool,
        /// The file or URI; `None` reopens an empty in-memory database.
        target: Option<String>,
    },
    /// `.quit` / `.exit` — stop reading input.
    Quit,
    /// `.help [PATTERN]` — list the commands.
    Help(Option<String>),
    /// `.tables [PATTERN]` — list tables and views.
    Tables(Option<String>),
    /// `.schema [PATTERN]` — show `CREATE` statements.
    Schema(Option<String>),
    /// `.databases` — list attached databases.
    Databases,
    /// `.mode [MODE]` — set or report the output mode.
    Mode(Option<Mode>),
    /// `.headers on|off`.
    Headers(bool),
    /// `.nullvalue TEXT`.
    NullValue(String),
    /// `.separator TEXT`.
    Separator(String),
    /// `.read FILE` — run a file as if typed.
    Read(String),
    /// `.output [FILE]` — redirect output, or return it to the default sink.
    Output(Option<String>),
    /// `.dump [PATTERN]` — emit `SQL` reproducing the database.
    Dump(Option<String>),
}

/// Why a dot command could not be understood.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// The line was not a dot command at all.
    NotACommand,
    /// No such command.
    Unknown(String),
    /// A quoted argument never closed.
    UnterminatedQuote,
    /// The command was given the wrong arguments.
    Usage(&'static str),
    /// `.mode` was given a mode this shell does not have.
    Mode(UnknownMode),
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotACommand => formatter.write_str("not a dot command"),
            Self::Unknown(name) => write!(
                formatter,
                "unknown command or invalid arguments: \"{name}\". Enter \".help\" for help"
            ),
            Self::UnterminatedQuote => formatter.write_str("unterminated quoted string"),
            Self::Usage(usage) => write!(formatter, "usage: {usage}"),
            Self::Mode(inner) => inner.fmt(formatter),
        }
    }
}

impl std::error::Error for ParseError {}

/// Splits a dot-command line into arguments.
///
/// Single quotes are literal; double quotes take the usual backslash escapes.
/// This is upstream's tokeniser minus its handling of `\NNN` octal escapes.
///
/// # Errors
///
/// Returns [`ParseError::UnterminatedQuote`] when a quote never closes.
pub fn split_arguments(line: &str) -> Result<Vec<String>, ParseError> {
    let mut arguments = Vec::new();
    let mut characters = line.chars().peekable();
    loop {
        while characters.peek().is_some_and(|c| c.is_whitespace()) {
            characters.next();
        }
        let Some(&first) = characters.peek() else {
            return Ok(arguments);
        };
        let mut argument = String::new();
        match first {
            '\'' => {
                characters.next();
                loop {
                    match characters.next() {
                        None => return Err(ParseError::UnterminatedQuote),
                        Some('\'') => break,
                        Some(other) => argument.push(other),
                    }
                }
            }
            '"' => {
                characters.next();
                loop {
                    match characters.next() {
                        None => return Err(ParseError::UnterminatedQuote),
                        Some('"') => break,
                        Some('\\') => match characters.next() {
                            None => return Err(ParseError::UnterminatedQuote),
                            Some('n') => argument.push('\n'),
                            Some('t') => argument.push('\t'),
                            Some('r') => argument.push('\r'),
                            Some('0') => argument.push('\0'),
                            Some(other) => argument.push(other),
                        },
                        Some(other) => argument.push(other),
                    }
                }
            }
            _ => {
                while let Some(&next) = characters.peek() {
                    if next.is_whitespace() {
                        break;
                    }
                    argument.push(next);
                    characters.next();
                }
            }
        }
        arguments.push(argument);
    }
}

impl Command {
    /// Parses a line beginning with `.`.
    ///
    /// # Errors
    ///
    /// Returns [`ParseError`] when the line is not a command, names no
    /// command, or is given arguments the command cannot use.
    pub fn parse(line: &str) -> Result<Self, ParseError> {
        let trimmed = line.trim_start();
        if !trimmed.starts_with('.') {
            return Err(ParseError::NotACommand);
        }
        let arguments = split_arguments(&trimmed[1..])?;
        let Some((name, rest)) = arguments.split_first() else {
            return Err(ParseError::Unknown(String::new()));
        };
        let one = |usage| match rest {
            [only] => Ok(only.clone()),
            _ => Err(ParseError::Usage(usage)),
        };
        let optional = || rest.first().cloned();

        match name.as_str() {
            "open" => {
                let mut readonly = false;
                let mut target = None;
                for argument in rest {
                    match argument.as_str() {
                        "--readonly" | "-readonly" => readonly = true,
                        "--new" | "-new" => {}
                        flag if flag.starts_with('-') => {
                            return Err(ParseError::Usage(".open [--readonly] [FILE|URI]"));
                        }
                        other => target = Some(other.to_owned()),
                    }
                }
                Ok(Self::Open { readonly, target })
            }
            "quit" | "exit" => Ok(Self::Quit),
            "help" => Ok(Self::Help(optional())),
            "tables" => Ok(Self::Tables(optional())),
            "schema" => Ok(Self::Schema(optional())),
            "databases" => Ok(Self::Databases),
            "dump" => Ok(Self::Dump(optional())),
            "mode" => match rest {
                [] => Ok(Self::Mode(None)),
                [only] => only
                    .parse::<Mode>()
                    .map(|mode| Self::Mode(Some(mode)))
                    .map_err(ParseError::Mode),
                _ => Err(ParseError::Usage(".mode [MODE]")),
            },
            "headers" | "header" => match one(".headers on|off")?.as_str() {
                "on" | "yes" | "true" | "1" => Ok(Self::Headers(true)),
                "off" | "no" | "false" | "0" => Ok(Self::Headers(false)),
                _ => Err(ParseError::Usage(".headers on|off")),
            },
            "nullvalue" => Ok(Self::NullValue(one(".nullvalue TEXT")?)),
            "separator" => Ok(Self::Separator(one(".separator TEXT")?)),
            "read" => Ok(Self::Read(one(".read FILE")?)),
            "output" => match rest {
                [] => Ok(Self::Output(None)),
                [only] if only == "stdout" => Ok(Self::Output(None)),
                [only] => Ok(Self::Output(Some(only.clone()))),
                _ => Err(ParseError::Usage(".output [FILE]")),
            },
            other => Err(ParseError::Unknown(other.to_owned())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arguments_split_on_whitespace() {
        assert_eq!(split_arguments("a b  c").unwrap(), ["a", "b", "c"]);
        assert_eq!(split_arguments("   ").unwrap(), Vec::<String>::new());
    }

    #[test]
    fn single_quotes_are_literal() {
        assert_eq!(split_arguments("'a b' 'c\\d'").unwrap(), ["a b", "c\\d"]);
    }

    #[test]
    fn double_quotes_take_escapes() {
        assert_eq!(
            split_arguments(r#""a\tb" "c\"d""#).unwrap(),
            ["a\tb", "c\"d"]
        );
    }

    #[test]
    fn an_unterminated_quote_is_an_error() {
        assert_eq!(
            split_arguments("'oops").unwrap_err(),
            ParseError::UnterminatedQuote
        );
        assert_eq!(
            split_arguments("\"oops").unwrap_err(),
            ParseError::UnterminatedQuote
        );
    }

    #[test]
    fn open_takes_a_uri_and_a_readonly_flag() {
        assert_eq!(
            Command::parse(".open file:abc?vfs=cas").unwrap(),
            Command::Open {
                readonly: false,
                target: Some("file:abc?vfs=cas".to_owned())
            }
        );
        assert_eq!(
            Command::parse(".open --readonly 'my db.sqlite'").unwrap(),
            Command::Open {
                readonly: true,
                target: Some("my db.sqlite".to_owned())
            }
        );
        assert_eq!(
            Command::parse(".open").unwrap(),
            Command::Open {
                readonly: false,
                target: None
            }
        );
    }

    #[test]
    fn mode_reports_when_given_nothing_and_rejects_what_it_lacks() {
        assert_eq!(Command::parse(".mode").unwrap(), Command::Mode(None));
        assert_eq!(
            Command::parse(".mode box").unwrap(),
            Command::Mode(Some(Mode::Box))
        );
        assert_eq!(
            Command::parse(".mode csv").unwrap_err(),
            ParseError::Mode(UnknownMode("csv".to_owned()))
        );
    }

    #[test]
    fn headers_accepts_the_usual_spellings() {
        assert_eq!(
            Command::parse(".headers on").unwrap(),
            Command::Headers(true)
        );
        assert_eq!(
            Command::parse(".header off").unwrap(),
            Command::Headers(false)
        );
        assert_eq!(
            Command::parse(".headers maybe").unwrap_err(),
            ParseError::Usage(".headers on|off")
        );
        assert_eq!(
            Command::parse(".headers").unwrap_err(),
            ParseError::Usage(".headers on|off")
        );
    }

    #[test]
    fn quit_has_two_spellings() {
        assert_eq!(Command::parse(".quit").unwrap(), Command::Quit);
        assert_eq!(Command::parse(".exit").unwrap(), Command::Quit);
    }

    #[test]
    fn output_with_no_argument_returns_to_the_default_sink() {
        assert_eq!(Command::parse(".output").unwrap(), Command::Output(None));
        assert_eq!(
            Command::parse(".output stdout").unwrap(),
            Command::Output(None)
        );
        assert_eq!(
            Command::parse(".output log.txt").unwrap(),
            Command::Output(Some("log.txt".to_owned()))
        );
    }

    #[test]
    fn an_unknown_command_names_itself() {
        assert_eq!(
            Command::parse(".archive").unwrap_err(),
            ParseError::Unknown("archive".to_owned())
        );
        assert!(
            Command::parse(".archive")
                .unwrap_err()
                .to_string()
                .contains(".help")
        );
    }

    #[test]
    fn a_line_without_a_dot_is_not_a_command() {
        assert_eq!(
            Command::parse("SELECT 1;").unwrap_err(),
            ParseError::NotACommand
        );
    }
}
