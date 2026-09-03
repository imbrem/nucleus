//! Lossless, resource-bounded WebAssembly binary data.
//!
//! Parsing and validation are userspace operations. They do not create theorem
//! facts or establish that these bytes denote a term in a HOL semantics.

use std::{ops::Range, sync::Arc};

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
    payload: Range<usize>,
}

impl Section {
    /// Returns the payload byte range in the exact module.
    #[must_use]
    pub fn range(&self) -> Range<usize> {
        self.payload.clone()
    }
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
    /// # Errors
    ///
    /// Returns an error if `function` did not originate from this module and
    /// its retained range is outside the exact bytes.
    pub fn function_body(&self, function: &Function) -> Result<FunctionBody<'a>, Error> {
        let bytes = checked_range(self.bytes, &function.body, "function body")?;
        let mut reader = BinaryReader::new(bytes, function.body.start);
        reader.set_features(WasmFeatures::WASM3);
        Ok(FunctionBody::new(reader))
    }

    /// Returns the exact payload bytes for a section from this module.
    /// # Errors
    ///
    /// Returns an error if `section` did not originate from this module and
    /// its retained range is outside the exact bytes.
    pub fn payload(&self, section: &Section) -> Result<&'a [u8], Error> {
        checked_range(self.bytes, &section.payload, "section payload")
    }

    /// Copies the exact bytes into an immutable, shareable module artifact.
    ///
    /// The already validated section/function metadata and CID are retained;
    /// this does not parse, validate, or assign semantic meaning a second time.
    #[must_use]
    pub fn into_shared(self) -> SharedModule {
        SharedModule {
            bytes: Arc::from(self.bytes),
            cid: self.cid,
            sections: Arc::from(self.sections),
            functions: Arc::from(self.functions),
        }
    }
}

/// A validated WebAssembly 3.0 core module with shared exact-byte ownership.
///
/// This is the portable/concurrent counterpart of borrowing [`Module`]. It is
/// immutable and uses `Arc` only for storage ownership; neither validation nor
/// a content address constitutes a semantic theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SharedModule {
    bytes: Arc<[u8]>,
    cid: Cid,
    sections: Arc<[Section]>,
    functions: Arc<[Function]>,
}

impl SharedModule {
    /// Returns the exact retained module bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the raw SHA-256 content address of the exact module bytes.
    #[must_use]
    pub const fn cid(&self) -> Cid {
        self.cid
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

    /// Streams parser payloads from the retained exact bytes.
    ///
    /// The parser uses the same WebAssembly 3.0 feature profile with which the
    /// original borrowed module was validated.
    pub fn payloads(
        &self,
    ) -> impl Iterator<Item = Result<Payload<'_>, covalence_lib_wasm::wasmparser::BinaryReaderError>>
    {
        let mut parser = Parser::new(0);
        parser.set_features(WasmFeatures::WASM3);
        parser.parse_all(&self.bytes)
    }

    /// Opens a typed reader for one retained function body.
    /// # Errors
    ///
    /// Returns an error if `function` did not originate from this module and
    /// its retained range is outside the exact bytes.
    pub fn function_body(&self, function: &Function) -> Result<FunctionBody<'_>, Error> {
        let bytes = checked_range(&self.bytes, &function.body, "function body")?;
        let mut reader = BinaryReader::new(bytes, function.body.start);
        reader.set_features(WasmFeatures::WASM3);
        Ok(FunctionBody::new(reader))
    }

    /// Returns the exact payload bytes for a retained section.
    /// # Errors
    ///
    /// Returns an error if `section` did not originate from this module and
    /// its retained range is outside the exact bytes.
    pub fn payload(&self, section: &Section) -> Result<&[u8], Error> {
        checked_range(&self.bytes, &section.payload, "section payload")
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
    /// A retained view did not belong to the module on which it was used.
    #[snafu(display("{kind} byte range {start}..{end} is outside module length {length}"))]
    Range {
        /// Kind of retained byte view.
        kind: &'static str,
        /// Inclusive start offset.
        start: usize,
        /// Exclusive end offset.
        end: usize,
        /// Exact module byte length.
        length: usize,
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

fn checked_range<'a>(
    bytes: &'a [u8],
    range: &Range<usize>,
    kind: &'static str,
) -> Result<&'a [u8], Error> {
    bytes.get(range.clone()).ok_or(Error::Range {
        kind,
        start: range.start,
        end: range.end,
        length: bytes.len(),
    })
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

/// Recognizes and validates an already shared exact WebAssembly module.
///
/// Unlike [`Module::into_shared`], this retains the caller's `Arc<[u8]>`
/// allocation. Parsing and validation remain userspace operations and create
/// no theorem fact.
///
/// # Errors
///
/// Returns under the same conditions as [`parse`].
pub fn parse_shared(bytes: Arc<[u8]>, limits: Limits) -> Result<SharedModule, Error> {
    let parsed = parse(&bytes, limits)?;
    let Module {
        cid,
        sections,
        functions,
        ..
    } = parsed;
    Ok(SharedModule {
        bytes,
        cid,
        sections: Arc::from(sections),
        functions: Arc::from(functions),
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use covalence_lib_wasm::wasmparser::Operator;

    use covalence_data_cbor::drisl::{self, CidCodec, CidHash};

    use super::{Error, Limits, SharedModule, parse, parse_shared};

    const EMPTY_MODULE: &[u8] = b"\0asm\x01\0\0\0";

    fn assert_send_sync<T: Send + Sync>() {}

    #[test]
    fn shared_modules_retain_exact_owned_bytes() {
        assert_send_sync::<SharedModule>();
        let bytes: Arc<[u8]> = Arc::from(EMPTY_MODULE);
        let module = parse_shared(Arc::clone(&bytes), Limits::default()).unwrap();

        assert!(Arc::ptr_eq(&bytes, &module.bytes));
        assert_eq!(module.bytes(), EMPTY_MODULE);
        assert_eq!(
            module.cid(),
            parse(EMPTY_MODULE, Limits::default()).unwrap().cid()
        );
        assert!(module.sections().is_empty());
        assert!(module.functions().is_empty());
        assert_eq!(
            parse(EMPTY_MODULE, Limits::default())
                .unwrap()
                .into_shared(),
            module
        );

        let cloned = module.clone();
        std::thread::spawn(move || assert_eq!(cloned.bytes(), EMPTY_MODULE))
            .join()
            .unwrap();
    }

    #[test]
    fn rejects_views_from_other_modules_without_panicking() {
        let module = parse(EMPTY_MODULE, Limits::default()).unwrap();
        let foreign_section = super::Section {
            id: 0,
            payload: 100..101,
        };
        let foreign_function = super::Function { body: 100..101 };

        assert!(matches!(
            module.payload(&foreign_section),
            Err(Error::Range {
                kind: "section payload",
                ..
            })
        ));
        assert!(matches!(
            module.function_body(&foreign_function),
            Err(Error::Range {
                kind: "function body",
                ..
            })
        ));

        let shared = module.into_shared();
        assert!(matches!(
            shared.payload(&foreign_section),
            Err(Error::Range {
                kind: "section payload",
                ..
            })
        ));
        assert!(matches!(
            shared.function_body(&foreign_function),
            Err(Error::Range {
                kind: "function body",
                ..
            })
        ));
    }

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
        assert_eq!(
            module.payload(&module.sections()[0]).unwrap(),
            b"\x01x\x01y"
        );
        assert_eq!(module.sections()[1].id, 1);
        assert_eq!(module.payload(&module.sections()[1]).unwrap(), b"\0");
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
        let body = module.function_body(function).unwrap();
        assert_eq!(body.as_bytes(), b"\0\x0b");
        let mut operators = body.get_operators_reader().expect("locals decode");
        assert!(matches!(operators.read(), Ok(Operator::End)));
        assert!(operators.eof());
        assert_eq!(module.payloads().filter_map(Result::ok).count(), 6);
    }
}
