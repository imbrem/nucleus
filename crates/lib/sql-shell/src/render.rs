//! Turning result rows into bytes.
//!
//! `list`, `json` and `quote` stream: a row is written as soon as it arrives.
//! `column` and `box` cannot, because a column's width is not known until the
//! last row has been seen, so those two buffer the result.

use std::io::{self, Write};

use crate::mode::Mode;
use crate::value::Cell;

/// The formatting knobs `.mode`, `.headers`, `.nullvalue` and `.separator`
/// set.
#[derive(Clone, Debug)]
pub struct Style {
    /// How to render rows.
    pub mode: Mode,
    /// Whether to print column names.
    pub headers: bool,
    /// What `.nullvalue` prints for `NULL`.
    pub null_text: String,
    /// What `list` puts between values.
    pub separator: String,
}

impl Default for Style {
    fn default() -> Self {
        Self {
            mode: Mode::default(),
            headers: false,
            null_text: String::new(),
            separator: "|".to_owned(),
        }
    }
}

/// Writes one result set.
pub struct Renderer<'a> {
    style: &'a Style,
    columns: Vec<String>,
    buffered: Vec<Vec<Cell>>,
    rows: usize,
}

impl<'a> Renderer<'a> {
    /// Begins a result set with the given column names.
    pub fn new(style: &'a Style, columns: Vec<String>) -> Self {
        Self {
            style,
            columns,
            buffered: Vec::new(),
            rows: 0,
        }
    }

    /// Accepts one row.
    ///
    /// # Errors
    ///
    /// Propagates failures from the sink.
    pub fn row(&mut self, out: &mut dyn Write, cells: Vec<Cell>) -> io::Result<()> {
        match self.style.mode {
            Mode::Column | Mode::Box => self.buffered.push(cells),
            Mode::List => {
                if self.rows == 0 && self.style.headers {
                    writeln!(out, "{}", self.columns.join(&self.style.separator))?;
                }
                let values: Vec<String> = cells
                    .iter()
                    .map(|cell| cell.plain(&self.style.null_text))
                    .collect();
                writeln!(out, "{}", values.join(&self.style.separator))?;
            }
            Mode::Quote => {
                if self.rows == 0 && self.style.headers {
                    let names: Vec<String> = self
                        .columns
                        .iter()
                        .map(|name| Cell::Text(name.clone()).sql_literal())
                        .collect();
                    writeln!(out, "{}", names.join(","))?;
                }
                let values: Vec<String> = cells.iter().map(Cell::sql_literal).collect();
                writeln!(out, "{}", values.join(","))?;
            }
            Mode::Json => {
                out.write_all(if self.rows == 0 { b"[" } else { b",\n" })?;
                out.write_all(b"{")?;
                for (index, cell) in cells.iter().enumerate() {
                    if index > 0 {
                        out.write_all(b",")?;
                    }
                    write!(
                        out,
                        "{}:{}",
                        Cell::Text(self.columns[index].clone()).json(),
                        cell.json()
                    )?;
                }
                out.write_all(b"}")?;
            }
        }
        self.rows += 1;
        Ok(())
    }

    /// Finishes the result set.
    ///
    /// # Errors
    ///
    /// Propagates failures from the sink.
    pub fn finish(self, out: &mut dyn Write) -> io::Result<()> {
        match self.style.mode {
            Mode::Column => self.aligned(out, false),
            Mode::Box => self.aligned(out, true),
            Mode::Json if self.rows > 0 => writeln!(out, "]"),
            _ => Ok(()),
        }
    }

    /// Renders the buffered modes, once every width is known.
    fn aligned(&self, out: &mut dyn Write, boxed: bool) -> io::Result<()> {
        if self.rows == 0 {
            return Ok(());
        }
        let rendered: Vec<Vec<String>> = self
            .buffered
            .iter()
            .map(|row| {
                row.iter()
                    .map(|cell| cell.plain(&self.style.null_text))
                    .collect()
            })
            .collect();

        let widths: Vec<usize> = self
            .columns
            .iter()
            .enumerate()
            .map(|(index, name)| {
                let header = if self.style.headers { width(name) } else { 0 };
                rendered
                    .iter()
                    .filter_map(|row| row.get(index))
                    .map(|text| width(text))
                    .fold(header, usize::max)
            })
            .collect();

        // A column is right-aligned when every value in it is a number, which
        // is what upstream does and what makes a table of counts readable.
        let numeric: Vec<bool> = (0..self.columns.len())
            .map(|index| {
                self.buffered
                    .iter()
                    .filter_map(|row| row.get(index))
                    .any(Cell::is_numeric)
                    && self
                        .buffered
                        .iter()
                        .filter_map(|row| row.get(index))
                        .all(|cell| cell.is_numeric() || matches!(cell, Cell::Null))
            })
            .collect();

        if boxed {
            self.write_box(out, &rendered, &widths, &numeric)
        } else {
            self.write_column(out, &rendered, &widths, &numeric)
        }
    }

    fn write_column(
        &self,
        out: &mut dyn Write,
        rendered: &[Vec<String>],
        widths: &[usize],
        numeric: &[bool],
    ) -> io::Result<()> {
        if self.style.headers {
            let header: Vec<String> = self
                .columns
                .iter()
                .zip(widths)
                .map(|(name, width)| centre(name, *width))
                .collect();
            writeln!(out, "{}", header.join("  ").trim_end())?;
            let rule: Vec<String> = widths.iter().map(|width| "-".repeat(*width)).collect();
            writeln!(out, "{}", rule.join("  "))?;
        }
        for row in rendered {
            let cells: Vec<String> = row
                .iter()
                .zip(widths)
                .zip(numeric)
                .map(|((text, width), right)| pad(text, *width, *right))
                .collect();
            writeln!(out, "{}", cells.join("  ").trim_end())?;
        }
        Ok(())
    }

    fn write_box(
        &self,
        out: &mut dyn Write,
        rendered: &[Vec<String>],
        widths: &[usize],
        numeric: &[bool],
    ) -> io::Result<()> {
        let rule = |out: &mut dyn Write, left: &str, mid: &str, right: &str, fill: &str| {
            let segments: Vec<String> = widths.iter().map(|width| fill.repeat(width + 2)).collect();
            writeln!(out, "{left}{}{right}", segments.join(mid))
        };

        rule(out, "\u{256d}", "\u{252c}", "\u{256e}", "\u{2500}")?;
        if self.style.headers {
            let header: Vec<String> = self
                .columns
                .iter()
                .zip(widths)
                .map(|(name, width)| format!(" {} ", centre(name, *width)))
                .collect();
            writeln!(out, "\u{2502}{}\u{2502}", header.join("\u{2502}"))?;
            rule(out, "\u{255e}", "\u{256a}", "\u{2561}", "\u{2550}")?;
        }
        for row in rendered {
            let cells: Vec<String> = row
                .iter()
                .zip(widths)
                .zip(numeric)
                .map(|((text, width), right)| format!(" {} ", pad(text, *width, *right)))
                .collect();
            writeln!(out, "\u{2502}{}\u{2502}", cells.join("\u{2502}"))?;
        }
        rule(out, "\u{2570}", "\u{2534}", "\u{256f}", "\u{2500}")
    }
}

/// Display width, counted in `char`s.
///
/// Upstream measures the same way for the common case. Both get East Asian
/// wide characters and combining marks wrong.
fn width(text: &str) -> usize {
    text.chars().count()
}

/// Pads `text` to `width`, on the left when `right` is set.
fn pad(text: &str, width_to: usize, right: bool) -> String {
    let padding = width_to.saturating_sub(width(text));
    if right {
        format!("{}{text}", " ".repeat(padding))
    } else {
        format!("{text}{}", " ".repeat(padding))
    }
}

/// Centres `text` in `width`, biased left, as upstream centres headers.
fn centre(text: &str, width_to: usize) -> String {
    let padding = width_to.saturating_sub(width(text));
    let left = padding / 2;
    format!("{}{text}{}", " ".repeat(left), " ".repeat(padding - left))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn render(style: &Style, columns: &[&str], rows: Vec<Vec<Cell>>) -> String {
        let mut out = Vec::new();
        let mut renderer = Renderer::new(
            style,
            columns.iter().map(|name| (*name).to_owned()).collect(),
        );
        for row in rows {
            renderer.row(&mut out, row).unwrap();
        }
        renderer.finish(&mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    fn sample() -> Vec<Vec<Cell>> {
        vec![
            vec![
                Cell::Integer(1),
                Cell::Text("hi".to_owned()),
                Cell::Blob(vec![0x00, 0xff, 0x41]),
            ],
            vec![
                Cell::Null,
                Cell::Text("longer text here".to_owned()),
                Cell::Real(3.5),
            ],
            vec![
                Cell::Integer(-2),
                Cell::Text(String::new()),
                Cell::Blob(Vec::new()),
            ],
        ]
    }

    #[test]
    fn list_is_separated_values() {
        let style = Style {
            headers: true,
            ..Style::default()
        };
        assert_eq!(
            render(&style, &["a", "b", "c"], sample()),
            "a|b|c\n1|hi|x'00ff41'\n|longer text here|3.5\n-2||x''\n"
        );
    }

    #[test]
    fn list_honours_the_separator_and_nullvalue() {
        let style = Style {
            separator: ", ".to_owned(),
            null_text: "NIL".to_owned(),
            ..Style::default()
        };
        assert_eq!(
            render(
                &style,
                &["a"],
                vec![vec![Cell::Null], vec![Cell::Integer(7)]]
            ),
            "NIL\n7\n"
        );
        let style = Style {
            separator: ", ".to_owned(),
            ..Style::default()
        };
        assert_eq!(
            render(
                &style,
                &["a", "b"],
                vec![vec![Cell::Integer(1), Cell::Integer(2)]]
            ),
            "1, 2\n"
        );
    }

    #[test]
    fn column_centres_headers_and_right_aligns_numbers() {
        let style = Style {
            mode: Mode::Column,
            headers: true,
            ..Style::default()
        };
        // Column `a` is numeric (integers and NULL), so it right-aligns.
        // Column `c` mixes a blob with a real, so it does not. Headers are
        // centred and trailing padding is trimmed, both as upstream does.
        let expected = concat!(
            "a          b              c\n",
            "--  ----------------  ---------\n",
            " 1  hi                x'00ff41'\n",
            "    longer text here  3.5\n",
            "-2                    x''\n",
        );
        assert_eq!(render(&style, &["a", "b", "c"], sample()), expected);
    }

    #[test]
    fn column_without_headers_omits_the_rule() {
        let style = Style {
            mode: Mode::Column,
            headers: false,
            ..Style::default()
        };
        assert_eq!(render(&style, &["a"], vec![vec![Cell::Integer(1)]]), "1\n");
    }

    #[test]
    fn box_draws_a_frame() {
        let style = Style {
            mode: Mode::Box,
            headers: true,
            ..Style::default()
        };
        assert_eq!(
            render(
                &style,
                &["n"],
                vec![vec![Cell::Integer(42)], vec![Cell::Integer(7)]]
            ),
            concat!(
                "\u{256d}\u{2500}\u{2500}\u{2500}\u{2500}\u{256e}\n",
                "\u{2502} n  \u{2502}\n",
                "\u{255e}\u{2550}\u{2550}\u{2550}\u{2550}\u{2561}\n",
                "\u{2502} 42 \u{2502}\n",
                "\u{2502}  7 \u{2502}\n",
                "\u{2570}\u{2500}\u{2500}\u{2500}\u{2500}\u{256f}\n",
            )
        );
    }

    #[test]
    fn json_is_one_object_per_row() {
        let style = Style {
            mode: Mode::Json,
            ..Style::default()
        };
        assert_eq!(
            render(
                &style,
                &["a", "b"],
                vec![
                    vec![Cell::Integer(1), Cell::Text("x".to_owned())],
                    vec![Cell::Null, Cell::Real(3.5)],
                ]
            ),
            "[{\"a\":1,\"b\":\"x\"},\n{\"a\":null,\"b\":3.5}]\n"
        );
    }

    #[test]
    fn quote_emits_sql_literals() {
        let style = Style {
            mode: Mode::Quote,
            headers: true,
            ..Style::default()
        };
        assert_eq!(
            render(&style, &["a", "b", "c"], sample()),
            concat!(
                "'a','b','c'\n",
                "1,'hi',x'00ff41'\n",
                "NULL,'longer text here',3.5\n",
                "-2,'',x''\n",
            )
        );
    }

    #[test]
    fn an_empty_result_prints_nothing() {
        for mode in Mode::all() {
            let style = Style {
                mode,
                headers: true,
                ..Style::default()
            };
            assert_eq!(render(&style, &["a"], Vec::new()), "", "mode {mode}");
        }
    }
}
