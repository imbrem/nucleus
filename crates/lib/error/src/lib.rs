//! Error handling conventions for Nucleus.
//!
//! Production crates use [`snafu`] to define concrete domain errors and typed
//! implementation fault chains. These errors remain matchable by callers and
//! preserve the context needed to handle or propagate a failure.
//!
//! Orchestration and surface crates use [`miette`] when failures need dynamic
//! reports or structured, user-understandable diagnostics. Rendering policy
//! belongs in surface-specific crates rather than here.
//!
//! Miette is built with its `fancy` renderer. Without it, returning
//! [`miette::Result`] from `main` prints `Diagnostic { message: … }` and a note
//! telling the reader to recompile with the feature — worse than printing the
//! error's own `Display`, which is why nothing used miette before it was turned
//! on. It costs twenty crates of compile time and nothing else: the renderer is
//! dead code wherever no report is constructed, so the Wasm bundle is
//! byte-identical with and without it.
//!
//! Expected malformed input, warnings, and recoverable outcomes are not fatal
//! failures by default. Shared diagnostic and outcome types can be added when
//! concrete consumers establish their requirements.

/// SNAFU's typed error and context APIs.
pub use snafu;

/// Miette's diagnostic and dynamic report APIs.
pub use miette;

#[cfg(test)]
mod tests {
    use super::{miette, snafu};

    #[derive(Debug, snafu::Snafu, miette::Diagnostic)]
    #[snafu(display("could not read input"))]
    #[diagnostic(code(nucleus::test_input))]
    struct ExampleError;

    #[test]
    fn reexports_support_typed_diagnostics() {
        let error = ExampleError;
        assert!(snafu::ErrorCompat::backtrace(&error).is_none());
        assert_eq!(
            miette::Diagnostic::code(&error)
                .expect("diagnostic code")
                .to_string(),
            "nucleus::test_input"
        );
    }
}
