//! Statement completeness, answered by `SQLite` rather than by guesswork.

use std::ffi::CString;

/// Reports whether `sql` ends in a complete `SQL` statement.
///
/// This is the question an input loop has to answer on every line: keep
/// prompting, or hand the buffer to `SQLite`? Getting it right means tracking
/// string literals, bracketed and backtick identifiers, both comment forms,
/// and `BEGIN ... END` trigger bodies, where a semicolon does *not* terminate
/// the statement. `SQLite` already has that lexer, so this asks it.
///
/// A buffer containing an interior NUL is reported incomplete: `SQLite`'s C
/// interface cannot see past it, so no honest answer is available.
#[must_use]
pub fn is_complete(sql: &str) -> bool {
    let Ok(text) = CString::new(sql) else {
        return false;
    };
    // SAFETY: `text` is a valid, NUL-terminated C string that outlives the
    // call. `sqlite3_complete` only reads it, returns an `int`, retains
    // nothing, and requires no library initialisation.
    #[allow(
        unsafe_code,
        reason = "the one FFI call in this crate: sqlite3_complete over a CString"
    )]
    let complete = unsafe { covalence_lib_sqlite::ffi::sqlite3_complete(text.as_ptr()) };
    complete != 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_terminated_statement_is_complete() {
        assert!(is_complete("SELECT 1;"));
        assert!(is_complete("SELECT 1;\n"));
        assert!(is_complete("SELECT 1; SELECT 2;"));
    }

    #[test]
    fn an_unterminated_statement_is_not() {
        assert!(!is_complete("SELECT 1"));
        assert!(!is_complete("SELECT"));
        assert!(!is_complete(""));
    }

    #[test]
    fn a_semicolon_inside_a_literal_does_not_terminate() {
        assert!(!is_complete("SELECT ';'"));
        assert!(is_complete("SELECT ';';"));
        assert!(!is_complete("SELECT \"a;b\""));
        assert!(!is_complete("SELECT [a;b]"));
    }

    #[test]
    fn a_semicolon_inside_a_comment_does_not_terminate() {
        assert!(!is_complete("SELECT 1 -- ;\n"));
        assert!(!is_complete("SELECT 1 /* ; */"));
        assert!(is_complete("SELECT 1 /* ; */;"));
    }

    #[test]
    fn a_trigger_body_needs_its_own_end() {
        // The case a hand-rolled `ends_with(';')` gets wrong.
        let partial = "CREATE TRIGGER t AFTER INSERT ON x BEGIN SELECT 1;";
        assert!(!is_complete(partial));
        assert!(is_complete(&format!("{partial} END;")));
    }

    #[test]
    fn an_interior_nul_is_reported_incomplete() {
        assert!(!is_complete("SELECT 1;\u{0}"));
    }
}
