//! Lossless, resource-bounded WebAssembly binary data.
//!
//! Parsing and validation are userspace operations. They do not create theorem
//! facts or establish that these bytes denote a term in a HOL semantics.

use std::ops::Range;

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_wasm::wasmparser::{
    BinaryReader, Encoding, FunctionBody, Parser, Payload, Validator, WasmFeatures,
};

/// Resource policy applied while recognizing a module envelope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Greatest accepted binary size.
    pub bytes: usize,
    /// Greatest accepted number of sections, including custom sections.
    pub sections: usize,
    /// Greatest accepted number of defined function bodies.
    pub functions: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            bytes: 64 * 1024 * 1024,
            sections: 100_000,
            functions: 1_000_000,
        }
    }
}

/// One section in source order, preserving its exact payload location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Section {
    /// Binary section identifier.
    pub id: u8,
    /// Payload byte range in the original module.
    pub payload: Range<usize>,
}

/// One defined function body in function-index order after imports.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    body: Range<usize>,
}

impl Function {
    /// Returns the body byte range, including locals and instructions but not
    /// its encoded size prefix.
    #[must_use]
    pub fn range(&self) -> Range<usize> {
        self.body.clone()
    }
}

/// A validated WebAssembly 3.0 core module borrowing its exact bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module<'a> {
    bytes: &'a [u8],
    cid: Cid,
    sections: Vec<Section>,
    functions: Vec<Function>,
}

impl<'a> Module<'a> {
    /// Returns the exact bytes from which this view was parsed.
    #[must_use]
    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    /// Returns the raw SHA-256 content address of the exact module bytes.
    #[must_use]
    pub const fn cid(&self) -> Cid {
        self.cid
    }

    /// Streams every typed parser payload from the retained exact bytes.
    ///
    /// Section readers and function bodies borrow this module. The parser uses
    /// exactly the standardized WebAssembly 3.0 feature profile.
    pub fn payloads(
        &self,
    ) -> impl Iterator<Item = Result<Payload<'a>, covalence_lib_wasm::wasmparser::BinaryReaderError>> + 'a
    {
        let mut parser = Parser::new(0);
        parser.set_features(WasmFeatures::WASM3);
        parser.parse_all(self.bytes)
    }

    /// Returns all binary sections in source order.
    #[must_use]
    pub fn sections(&self) -> &[Section] {
        &self.sections
    }

    /// Returns defined function bodies in binary order.
    #[must_use]
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }

    /// Opens a typed, borrowing reader for a function's locals and operators.
    ///
    /// The reader uses exactly the WebAssembly 3.0 feature profile. This is a
    /// compositional view over the retained bytes, not a second semantic AST.
    #[must_use]
    pub fn function_body(&self, function: &Function) -> FunctionBody<'a> {
        let mut reader = BinaryReader::new(&self.bytes[function.body.clone()], function.body.start);
        reader.set_features(WasmFeatures::WASM3);
        FunctionBody::new(reader)
    }

    /// Returns the exact payload bytes for a section from this module.
    #[must_use]
    pub fn payload(&self, section: &Section) -> &'a [u8] {
        &self.bytes[section.payload.clone()]
    }
}

/// Why bytes could not be recognized as a WebAssembly 3.0 core module.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// Input exceeded the configured byte budget.
    #[snafu(display("WebAssembly binary is {actual} bytes; limit is {limit}"))]
    Bytes {
        /// Actual byte length.
        actual: usize,
        /// Configured limit.
        limit: usize,
    },
    /// Input exceeded the configured section budget.
    #[snafu(display("WebAssembly binary has more than {limit} sections"))]
    Sections {
        /// Configured limit.
        limit: usize,
    },
    /// Input exceeded the configured defined-function budget.
    #[snafu(display("WebAssembly binary has more than {limit} defined functions"))]
    Functions {
        /// Configured limit.
        limit: usize,
    },
    /// Input used a non-module binary encoding.
    #[snafu(display("WebAssembly binary is not a core module"))]
    NotModule,
    /// Binary structure or WebAssembly 3.0 validation failed.
    #[snafu(display("invalid WebAssembly 3.0 module: {source}"))]
    Invalid {
        /// Parser or validator failure.
        source: covalence_lib_wasm::wasmparser::BinaryReaderError,
    },
}

/// Recognizes and validates an exact WebAssembly 3.0 core module.
///
/// The returned view borrows the input and retains every byte, including
/// custom sections. Validation enables exactly the standardized WebAssembly
/// 3.0 feature set exposed by the pinned binary reader.
///
/// # Errors
///
/// Returns an error when a resource limit is exceeded, the bytes use the
/// component encoding, or parsing or WebAssembly 3.0 validation fails.
pub fn parse(bytes: &[u8], limits: Limits) -> Result<Module<'_>, Error> {
    if bytes.len() > limits.bytes {
        return Err(Error::Bytes {
            actual: bytes.len(),
            limit: limits.bytes,
        });
    }

    let mut sections = Vec::new();
    let mut functions = Vec::new();
    let mut is_module = false;
    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|source| Error::Invalid { source })?;
        if let Payload::Version { encoding, .. } = payload {
            is_module = encoding == Encoding::Module;
        }
        if let Payload::CodeSectionEntry(body) = &payload {
            if functions.len() == limits.functions {
                return Err(Error::Functions {
                    limit: limits.functions,
                });
            }
            functions.push(Function { body: body.range() });
        }
        if let Some((id, payload)) = payload.as_section() {
            if sections.len() == limits.sections {
                return Err(Error::Sections {
                    limit: limits.sections,
                });
            }
            sections.push(Section { id, payload });
        }
    }
    if !is_module {
        return Err(Error::NotModule);
    }

    Validator::new_with_features(WasmFeatures::WASM3)
        .validate_all(bytes)
        .map_err(|source| Error::Invalid { source })?;

    Ok(Module {
        bytes,
        cid: drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        sections,
        functions,
    })
}

#[cfg(test)]
mod tests {
    use covalence_lib_wasm::wasmparser::Operator;

    use covalence_data_cbor::drisl::{self, CidCodec, CidHash};

    use super::{Error, Limits, parse};

    const EMPTY_MODULE: &[u8] = b"\0asm\x01\0\0\0";

    #[test]
    fn retains_exact_bytes_and_ordered_section_payloads() {
        let bytes = b"\0asm\x01\0\0\0\0\x04\x01x\x01y\x01\x01\0";
        let module = parse(bytes, Limits::default()).expect("valid module");

        assert_eq!(module.bytes(), bytes);
        assert_eq!(
            module.cid(),
            drisl::address(CidCodec::Raw, CidHash::Sha256, bytes)
        );
        assert_eq!(module.sections().len(), 2);
        assert_eq!(module.sections()[0].id, 0);
        assert_eq!(module.payload(&module.sections()[0]), b"\x01x\x01y");
        assert_eq!(module.sections()[1].id, 1);
        assert_eq!(module.payload(&module.sections()[1]), b"\0");
    }

    #[test]
    fn applies_resource_limits_before_returning_a_view() {
        assert!(matches!(
            parse(
                EMPTY_MODULE,
                Limits {
                    bytes: 7,
                    sections: 0,
                    functions: 0,
                }
            ),
            Err(Error::Bytes { .. })
        ));
    }

    #[test]
    fn rejects_features_beyond_wasm_3() {
        // A version-1 module with an unknown non-custom section.
        let bytes = b"\0asm\x01\0\0\0\x2a\0";
        assert!(matches!(
            parse(bytes, Limits::default()),
            Err(Error::Invalid { .. })
        ));
    }

    #[test]
    fn opens_typed_wasm3_operators_without_copying_the_module() {
        let bytes = b"\0asm\x01\0\0\0\x01\x04\x01\x60\0\0\x03\x02\x01\0\x0a\x04\x01\x02\0\x0b";
        let module = parse(bytes, Limits::default()).expect("valid function module");
        let [function] = module.functions() else {
            panic!("expected one function")
        };
        let body = module.function_body(function);
        assert_eq!(body.as_bytes(), b"\0\x0b");
        let mut operators = body.get_operators_reader().expect("locals decode");
        assert!(matches!(operators.read(), Ok(Operator::End)));
        assert!(operators.eof());
        assert_eq!(module.payloads().filter_map(Result::ok).count(), 6);
    }
}
