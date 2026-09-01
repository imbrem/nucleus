//! Owned WebAssembly language objects and bounded binary extraction.
//!
//! [`load`] recognizes a deliberately small, standards-compliant core Wasm
//! profile. It preserves the exact input bytes and source ranges, but neither
//! parsing nor validation creates theorem facts. The types exported here do
//! not expose the parser implementation, so executors and future checked logic
//! can share a stable vocabulary.

use covalence_lib_error::snafu::Snafu;
use covalence_lib_wasm::wasmparser::{
    Chunk, Encoding, ExternalKind, FuncType, Operator, Parser, Payload, ValType, Validator,
    WasmFeatures,
};

/// The supported Wasm language profile.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum Profile {
    /// One exported core function over `i32`, with straight-line arithmetic.
    ///
    /// Core-module validity is judged with the pinned parser dependency's
    /// `WASM3` feature set before this smaller profile is extracted.
    TinyCoreV0,
}

/// A half-open range in the exact module bytes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ByteRange {
    /// Inclusive byte offset.
    pub start: usize,
    /// Exclusive byte offset.
    pub end: usize,
}

impl ByteRange {
    /// Returns the number of bytes in the range.
    #[must_use]
    pub const fn len(self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Returns whether the range is empty.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }
}

impl From<std::ops::Range<usize>> for ByteRange {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

/// A value type recognized by [`Profile::TinyCoreV0`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueType {
    /// A 32-bit integer word.
    I32,
}

/// A runtime value using Wasm's raw word representation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Value {
    /// The uninterpreted bits of an `i32` value.
    I32(u32),
}

/// Instruction forms recognized by [`Profile::TinyCoreV0`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum InstructionKind {
    /// Pushes the raw bits of a 32-bit constant.
    I32Const(u32),
    /// Pushes a parameter or local by zero-based index.
    LocalGet(u32),
    /// Adds the top two words modulo 2^32.
    I32Add,
    /// Returns from the function.
    Return,
}

/// The sole defined and exported function in a tiny module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    /// UTF-8 export name from the binary.
    export_name: String,
    /// Parameter types in index order.
    params: Vec<ValueType>,
    /// Result types in order.
    results: Vec<ValueType>,
    /// Non-parameter local types in index order.
    locals: Vec<ValueType>,
    /// Decoded straight-line semantic instructions.
    instructions: Vec<InstructionKind>,
}

impl Function {
    /// Returns the sole exported function name.
    #[must_use]
    pub fn export_name(&self) -> &str {
        &self.export_name
    }

    /// Returns parameter types in local-index order.
    #[must_use]
    pub fn params(&self) -> &[ValueType] {
        &self.params
    }

    /// Returns result types in result order.
    #[must_use]
    pub fn results(&self) -> &[ValueType] {
        &self.results
    }

    /// Returns non-parameter local types in local-index order.
    #[must_use]
    pub fn locals(&self) -> &[ValueType] {
        &self.locals
    }

    /// Returns decoded semantic instructions, excluding the structural `end`.
    #[must_use]
    pub fn instructions(&self) -> &[InstructionKind] {
        &self.instructions
    }
}

/// Pure executable meaning selected from a supported Wasm module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    /// Profile defining the executable vocabulary.
    profile: Profile,
    /// Sole defined and exported core function.
    function: Function,
}

impl Module {
    /// Returns the recognition profile used to load the module.
    #[must_use]
    pub const fn profile(&self) -> Profile {
        self.profile
    }

    /// Returns the sole defined and exported function.
    #[must_use]
    pub const fn function(&self) -> &Function {
        &self.function
    }
}

/// Byte provenance for one [`Module`] extracted from an exact binary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceMap {
    function: ByteRange,
    export: ByteRange,
    end: ByteRange,
    instructions: Vec<ByteRange>,
}

impl SourceMap {
    /// Returns the encoded function-body range.
    #[must_use]
    pub const fn function(&self) -> ByteRange {
        self.function
    }

    /// Returns the containing export-section range.
    #[must_use]
    pub const fn export(&self) -> ByteRange {
        self.export
    }

    /// Returns the structural final `end` marker range.
    #[must_use]
    pub const fn end(&self) -> ByteRange {
        self.end
    }

    /// Returns one range per semantic instruction in program order.
    #[must_use]
    pub fn instructions(&self) -> &[ByteRange] {
        &self.instructions
    }
}

/// Exact bytes together with their extracted executable meaning and provenance.
///
/// Fields are opaque so safe callers cannot silently mutate the semantic
/// object away from the bytes and source map produced by [`load`]. This is
/// still untrusted parsing data, not checked byte-to-semantics evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoadedModule {
    bytes: Vec<u8>,
    module: Module,
    sources: SourceMap,
}

impl LoadedModule {
    /// Returns the exact input bytes without normalization or re-encoding.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the pure executable meaning selected from the bytes.
    #[must_use]
    pub const fn module(&self) -> &Module {
        &self.module
    }

    /// Returns byte provenance for the selected executable meaning.
    #[must_use]
    pub const fn sources(&self) -> &SourceMap {
        &self.sources
    }
}

/// Resource budgets for loading and extracting owned language objects.
///
/// The byte limit is checked before upstream validation and bounds the entire
/// input. The finer limits are checked while extracting the supported profile,
/// after validation and before growing the corresponding owned object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Maximum exact module byte length.
    pub bytes: usize,
    /// Maximum type definitions.
    pub types: u32,
    /// Maximum function declarations.
    pub functions: u32,
    /// Maximum exports.
    pub exports: u32,
    /// Maximum parameters on the supported function.
    pub params: u32,
    /// Maximum results on the supported function.
    pub results: u32,
    /// Maximum expanded local count on the supported function.
    pub locals: u32,
    /// Maximum decoded instructions on the supported function.
    pub instructions: u32,
    /// Maximum bytes in the supported export name.
    pub name_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            bytes: 1024 * 1024,
            types: 64,
            functions: 64,
            exports: 64,
            params: 64,
            results: 1,
            locals: 1024,
            instructions: 100_000,
            name_bytes: 1024,
        }
    }
}

/// The resource whose configured budget was exceeded.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Resource {
    /// Exact input byte length.
    Bytes,
    /// Type definitions.
    Types,
    /// Function declarations.
    Functions,
    /// Exports.
    Exports,
    /// Function parameters.
    Params,
    /// Function results.
    Results,
    /// Expanded function locals.
    Locals,
    /// Decoded function instructions.
    Instructions,
    /// Export-name bytes.
    NameBytes,
}

impl std::fmt::Display for Resource {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Bytes => "bytes",
            Self::Types => "types",
            Self::Functions => "functions",
            Self::Exports => "exports",
            Self::Params => "parameters",
            Self::Results => "results",
            Self::Locals => "locals",
            Self::Instructions => "instructions",
            Self::NameBytes => "export-name bytes",
        })
    }
}

/// A valid Wasm construct outside [`Profile::TinyCoreV0`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unsupported {
    /// The input contains an import section.
    Imports,
    /// The input contains a table section.
    Tables,
    /// The input contains a memory section.
    Memories,
    /// The input contains a tag section.
    Tags,
    /// The input contains a global section.
    Globals,
    /// The input contains a start section.
    Start,
    /// The input contains an element section.
    Elements,
    /// The input contains a data-count section.
    DataCount,
    /// The input contains a data section.
    Data,
    /// The input contains an unknown section.
    UnknownSection,
    /// A type definition is not a plain function type.
    TypeDefinition,
    /// A function signature or local uses a type other than `i32`.
    ValueType,
    /// The module does not contain exactly one type and one defined function.
    FunctionShape,
    /// The module does not contain exactly one function export.
    ExportShape,
    /// The export does not refer to the sole defined function.
    ExportTarget,
    /// The function contains an instruction outside the tiny profile.
    Instruction,
}

impl std::fmt::Display for Unsupported {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Imports => "imports",
            Self::Tables => "tables",
            Self::Memories => "memories",
            Self::Tags => "tags",
            Self::Globals => "globals",
            Self::Start => "start function",
            Self::Elements => "elements",
            Self::DataCount => "data count",
            Self::Data => "data segments",
            Self::UnknownSection => "unknown section",
            Self::TypeDefinition => "non-function type definition",
            Self::ValueType => "non-i32 value type",
            Self::FunctionShape => "function shape",
            Self::ExportShape => "export shape",
            Self::ExportTarget => "export target",
            Self::Instruction => "instruction",
        })
    }
}

/// Why exact module bytes could not be loaded into an owned language object.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum LoadError {
    /// The outer binary framing could not be decoded.
    #[snafu(display("malformed Wasm at byte {offset}: {message}"))]
    Malformed {
        /// Byte offset reported by the binary reader.
        offset: usize,
        /// Parser diagnostic, without a parser-library type in the API.
        message: String,
    },
    /// The decoded binary is not a valid WebAssembly module.
    #[snafu(display("invalid Wasm at byte {offset}: {message}"))]
    Invalid {
        /// Byte offset reported by the validator.
        offset: usize,
        /// Validator diagnostic, without a parser-library type in the API.
        message: String,
    },
    /// The binary uses Component Model rather than core-module encoding.
    #[snafu(display("Wasm component encoding does not match the core-module profile"))]
    Encoding,
    /// The binary is valid but outside the selected profile.
    #[snafu(display("unsupported Wasm {feature} at byte {offset}"))]
    Unsupported {
        /// Unsupported valid construct.
        feature: Unsupported,
        /// First relevant byte offset.
        offset: usize,
    },
    /// A configured resource budget was exceeded.
    #[snafu(display("Wasm {resource} count {actual} exceeds limit {limit}"))]
    ResourceLimit {
        /// Resource whose allocation was bounded.
        resource: Resource,
        /// Observed or requested count.
        actual: u64,
        /// Configured maximum.
        limit: u64,
    },
}

/// Loads exact core Wasm bytes under an explicit, resource-bounded profile.
///
/// Parsing, upstream validation, and profile extraction are separate steps:
/// malformed outer framing, a different outer encoding, invalid core Wasm, and
/// valid-but-unsupported core Wasm remain distinguishable to callers. The
/// returned [`LoadedModule::bytes`] are exactly `bytes`; source ranges index
/// that stored copy.
///
/// # Errors
///
/// Returns [`LoadError::Malformed`] when outer binary framing cannot be read,
/// [`LoadError::Encoding`] for a component rather than a core module,
/// [`LoadError::Invalid`] when upstream Wasm validation fails,
/// [`LoadError::Unsupported`] for a valid construct outside `profile`, or
/// [`LoadError::ResourceLimit`] when a configured loading budget is exceeded.
pub fn load(bytes: &[u8], profile: Profile, limits: Limits) -> Result<LoadedModule, LoadError> {
    check_limit(Resource::Bytes, bytes.len(), limits.bytes)?;
    let encoding = scan_outer_framing(bytes)?;
    if encoding != Encoding::Module {
        return Err(LoadError::Encoding);
    }

    Validator::new_with_features(WasmFeatures::WASM3)
        .validate_all(bytes)
        .map_err(|error| invalid(&error))?;

    match profile {
        Profile::TinyCoreV0 => extract_tiny_core(bytes, limits),
    }
}

fn scan_outer_framing(bytes: &[u8]) -> Result<Encoding, LoadError> {
    match Parser::new(0)
        .parse(bytes, true)
        .map_err(|error| malformed(&error))?
    {
        Chunk::Parsed {
            payload: Payload::Version { encoding, .. },
            ..
        } => Ok(encoding),
        Chunk::Parsed { .. } | Chunk::NeedMoreData(_) => Err(LoadError::Malformed {
            offset: 0,
            message: "missing Wasm version header".to_owned(),
        }),
    }
}

fn malformed(error: &covalence_lib_wasm::wasmparser::BinaryReaderError) -> LoadError {
    LoadError::Malformed {
        offset: error.offset(),
        message: error.message().to_owned(),
    }
}

fn invalid(error: &covalence_lib_wasm::wasmparser::BinaryReaderError) -> LoadError {
    LoadError::Invalid {
        offset: error.offset(),
        message: error.message().to_owned(),
    }
}

fn check_limit(
    resource: Resource,
    actual: impl TryInto<u64>,
    limit: impl TryInto<u64>,
) -> Result<(), LoadError> {
    let actual = actual.try_into().unwrap_or(u64::MAX);
    let limit = limit.try_into().unwrap_or(u64::MAX);
    if actual > limit {
        Err(LoadError::ResourceLimit {
            resource,
            actual,
            limit,
        })
    } else {
        Ok(())
    }
}

#[derive(Default)]
struct Parts {
    types: Vec<FuncType>,
    type_offset: Option<usize>,
    function_types: Vec<u32>,
    export: Option<RawExport>,
    export_count: u32,
    body: Option<RawBody>,
    code_count: u32,
    unsupported: Option<(Unsupported, usize)>,
}

struct RawExport {
    name: String,
    kind: ExternalKind,
    index: u32,
    source: ByteRange,
}

struct RawBody {
    locals: Vec<ValueType>,
    instructions: Vec<InstructionKind>,
    instruction_sources: Vec<ByteRange>,
    source: ByteRange,
    end: ByteRange,
}

fn extract_tiny_core(bytes: &[u8], limits: Limits) -> Result<LoadedModule, LoadError> {
    let mut parts = Parts::default();

    for payload in Parser::new(0).parse_all(bytes) {
        let payload = payload.map_err(|error| malformed(&error))?;
        extract_payload(payload, limits, &mut parts)?;
    }

    if let Some((feature, offset)) = parts.unsupported {
        return Err(LoadError::Unsupported { feature, offset });
    }
    if parts.types.len() != 1
        || parts.function_types.as_slice() != [0]
        || parts.code_count != 1
        || parts.body.is_none()
    {
        return Err(LoadError::Unsupported {
            feature: Unsupported::FunctionShape,
            offset: bytes.len(),
        });
    }
    if parts.export_count != 1 || parts.export.is_none() {
        return Err(LoadError::Unsupported {
            feature: Unsupported::ExportShape,
            offset: bytes.len(),
        });
    }

    let ty = &parts.types[0];
    check_limit(Resource::Params, ty.params().len(), limits.params)?;
    check_limit(Resource::Results, ty.results().len(), limits.results)?;
    let type_offset = parts.type_offset.unwrap_or(0);
    let params = value_types(ty.params(), type_offset)?;
    let results = value_types(ty.results(), type_offset)?;
    let export = parts.export.expect("export presence checked above");
    if export.kind != ExternalKind::Func || export.index != 0 {
        return Err(LoadError::Unsupported {
            feature: Unsupported::ExportTarget,
            offset: export.source.start,
        });
    }
    let body = parts.body.expect("body presence checked above");

    let module = Module {
        profile: Profile::TinyCoreV0,
        function: Function {
            export_name: export.name,
            params,
            results,
            locals: body.locals,
            instructions: body.instructions,
        },
    };
    let sources = SourceMap {
        function: body.source,
        export: export.source,
        end: body.end,
        instructions: body.instruction_sources,
    };
    Ok(LoadedModule {
        bytes: bytes.to_vec(),
        module,
        sources,
    })
}

#[allow(clippy::too_many_lines)]
fn extract_payload(
    payload: Payload<'_>,
    limits: Limits,
    parts: &mut Parts,
) -> Result<(), LoadError> {
    match payload {
        Payload::TypeSection(reader) => {
            parts.type_offset.get_or_insert(reader.range().start);
            check_limit(Resource::Types, reader.count(), limits.types)?;
            for ty in reader.into_iter_err_on_gc_types() {
                match ty {
                    Ok(ty) => parts.types.push(ty),
                    Err(error) => {
                        remember_unsupported(parts, Unsupported::TypeDefinition, error.offset());
                        break;
                    }
                }
            }
        }
        Payload::ImportSection(reader) => {
            remember_unsupported(parts, Unsupported::Imports, reader.range().start);
        }
        Payload::FunctionSection(reader) => {
            check_limit(Resource::Functions, reader.count(), limits.functions)?;
            for index in reader {
                parts
                    .function_types
                    .push(index.map_err(|error| malformed(&error))?);
            }
        }
        Payload::TableSection(reader) => {
            remember_unsupported(parts, Unsupported::Tables, reader.range().start);
        }
        Payload::MemorySection(reader) => {
            remember_unsupported(parts, Unsupported::Memories, reader.range().start);
        }
        Payload::TagSection(reader) => {
            remember_unsupported(parts, Unsupported::Tags, reader.range().start);
        }
        Payload::GlobalSection(reader) => {
            remember_unsupported(parts, Unsupported::Globals, reader.range().start);
        }
        Payload::ExportSection(reader) => {
            check_limit(Resource::Exports, reader.count(), limits.exports)?;
            parts.export_count = parts.export_count.saturating_add(reader.count());
            let source = ByteRange::from(reader.range());
            for export in reader {
                let export = export.map_err(|error| malformed(&error))?;
                check_limit(Resource::NameBytes, export.name.len(), limits.name_bytes)?;
                if parts.export.is_none() {
                    parts.export = Some(RawExport {
                        name: export.name.to_owned(),
                        kind: export.kind,
                        index: export.index,
                        source,
                    });
                }
            }
        }
        Payload::StartSection { range, .. } => {
            remember_unsupported(parts, Unsupported::Start, range.start);
        }
        Payload::ElementSection(reader) => {
            remember_unsupported(parts, Unsupported::Elements, reader.range().start);
        }
        Payload::DataCountSection { range, .. } => {
            remember_unsupported(parts, Unsupported::DataCount, range.start);
        }
        Payload::DataSection(reader) => {
            remember_unsupported(parts, Unsupported::Data, reader.range().start);
        }
        Payload::CodeSectionStart { count, range, .. } => {
            check_limit(Resource::Functions, count, limits.functions)?;
            parts.code_count = count;
            if count != 1 {
                remember_unsupported(parts, Unsupported::FunctionShape, range.start);
            }
        }
        Payload::CodeSectionEntry(body) => {
            if parts.body.is_some() {
                remember_unsupported(parts, Unsupported::FunctionShape, body.range().start);
            } else {
                parts.body = Some(extract_body(&body, limits)?);
            }
        }
        Payload::Version { .. } | Payload::CustomSection(_) | Payload::End(_) => {}
        Payload::UnknownSection { range, .. } => {
            remember_unsupported(parts, Unsupported::UnknownSection, range.start);
        }
        _ => remember_unsupported(parts, Unsupported::UnknownSection, 0),
    }
    Ok(())
}

fn remember_unsupported(parts: &mut Parts, feature: Unsupported, offset: usize) {
    if parts.unsupported.is_none() {
        parts.unsupported = Some((feature, offset));
    }
}

fn value_types(types: &[ValType], offset: usize) -> Result<Vec<ValueType>, LoadError> {
    types
        .iter()
        .map(|ty| {
            if *ty == ValType::I32 {
                Ok(ValueType::I32)
            } else {
                Err(LoadError::Unsupported {
                    feature: Unsupported::ValueType,
                    offset,
                })
            }
        })
        .collect()
}

fn extract_body(
    body: &covalence_lib_wasm::wasmparser::FunctionBody<'_>,
    limits: Limits,
) -> Result<RawBody, LoadError> {
    let mut locals = Vec::new();
    let locals_reader = body
        .get_locals_reader()
        .map_err(|error| malformed(&error))?;
    for local in locals_reader {
        let (count, ty) = local.map_err(|error| malformed(&error))?;
        let total = u32::try_from(locals.len())
            .unwrap_or(u32::MAX)
            .saturating_add(count);
        check_limit(Resource::Locals, total, limits.locals)?;
        if ty != ValType::I32 {
            return Err(LoadError::Unsupported {
                feature: Unsupported::ValueType,
                offset: body.range().start,
            });
        }
        locals.extend(std::iter::repeat_n(ValueType::I32, count as usize));
    }

    let mut reader = body
        .get_operators_reader()
        .map_err(|error| malformed(&error))?;
    let mut instructions = Vec::new();
    let mut instruction_sources = Vec::new();
    let mut final_end = None;
    while !reader.eof() {
        let (operator, start) = reader
            .read_with_offset()
            .map_err(|error| malformed(&error))?;
        let end = reader.original_position();
        let kind = match operator {
            Operator::I32Const { value } => InstructionKind::I32Const(value.cast_unsigned()),
            Operator::LocalGet { local_index } => InstructionKind::LocalGet(local_index),
            Operator::I32Add => InstructionKind::I32Add,
            Operator::Return => InstructionKind::Return,
            Operator::End => {
                final_end = Some(ByteRange { start, end });
                continue;
            }
            _ => {
                return Err(LoadError::Unsupported {
                    feature: Unsupported::Instruction,
                    offset: start,
                });
            }
        };
        let actual = instructions.len().saturating_add(1);
        check_limit(Resource::Instructions, actual, limits.instructions)?;
        instructions.push(kind);
        instruction_sources.push(ByteRange { start, end });
    }

    Ok(RawBody {
        locals,
        instructions,
        instruction_sources,
        source: body.range().into(),
        end: final_end.ok_or_else(|| LoadError::Invalid {
            offset: body.range().end,
            message: "function body has no final end".to_owned(),
        })?,
    })
}

#[cfg(test)]
mod tests {
    use super::{
        InstructionKind, Limits, LoadError, Profile, Resource, Unsupported, ValueType, load,
    };

    const ADD: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // header
        0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7f, // type
        0x03, 0x02, 0x01, 0x00, // function
        0x07, 0x07, 0x01, 0x03, b'a', b'd', b'd', 0x00, 0x00, // export
        0x0a, 0x09, 0x01, 0x07, 0x00, 0x20, 0x00, 0x20, 0x01, 0x6a, 0x0b, // code
    ];

    const NEGATIVE_ONE: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // header
        0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type
        0x03, 0x02, 0x01, 0x00, // function
        0x07, 0x07, 0x01, 0x03, b'n', b'e', b'g', 0x00, 0x00, // export
        0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x7f, 0x0b, // code
    ];

    const I64_IDENTITY: &[u8] = &[
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // header
        0x01, 0x06, 0x01, 0x60, 0x01, 0x7e, 0x01, 0x7e, // type
        0x03, 0x02, 0x01, 0x00, // function
        0x07, 0x06, 0x01, 0x02, b'i', b'd', 0x00, 0x00, // export
        0x0a, 0x06, 0x01, 0x04, 0x00, 0x20, 0x00, 0x0b, // code
    ];

    #[test]
    fn extracts_exact_i32_add_module() {
        let loaded = load(ADD, Profile::TinyCoreV0, Limits::default()).unwrap();
        let module = loaded.module();
        assert_eq!(loaded.bytes(), ADD);
        assert_eq!(module.function().export_name(), "add");
        assert_eq!(module.function().params(), [ValueType::I32, ValueType::I32]);
        assert_eq!(module.function().results(), [ValueType::I32]);
        assert!(module.function().locals().is_empty());
        assert_eq!(
            module.function().instructions(),
            [
                InstructionKind::LocalGet(0),
                InstructionKind::LocalGet(1),
                InstructionKind::I32Add,
            ]
        );
        assert_eq!(loaded.sources().instructions().len(), 3);
        for source in loaded.sources().instructions() {
            assert!(!source.is_empty());
            assert!(source.end <= loaded.bytes().len());
        }
        assert_eq!(
            &loaded.bytes()[loaded.sources().end().start..loaded.sources().end().end],
            &[0x0b]
        );
    }

    #[test]
    fn preserves_i32_constant_bits() {
        let loaded = load(NEGATIVE_ONE, Profile::TinyCoreV0, Limits::default()).unwrap();
        assert_eq!(
            loaded.module().function().instructions()[0],
            InstructionKind::I32Const(u32::MAX)
        );
    }

    #[test]
    fn separates_malformed_invalid_and_unsupported() {
        assert!(matches!(
            load(b"not wasm", Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Malformed { .. })
        ));

        let mut invalid = ADD.to_vec();
        let add = invalid.iter().position(|byte| *byte == 0x6a).unwrap();
        invalid[add] = 0x6b; // i32.sub is valid and supported by validation
        assert!(matches!(
            load(&invalid, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Unsupported {
                feature: Unsupported::Instruction,
                ..
            })
        ));

        invalid[add] = 0x6a;
        let local = invalid.iter().position(|byte| *byte == 0x20).unwrap();
        invalid[local + 1] = 0x02;
        assert!(matches!(
            load(&invalid, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Invalid { .. })
        ));
    }

    #[test]
    fn enforces_limits_before_owned_growth() {
        let limits = Limits {
            instructions: 2,
            ..Limits::default()
        };
        assert!(matches!(
            load(ADD, Profile::TinyCoreV0, limits),
            Err(LoadError::ResourceLimit {
                resource: Resource::Instructions,
                actual: 3,
                limit: 2,
            })
        ));
    }

    #[test]
    fn accepts_spec_permitted_padded_leb_and_custom_trailer() {
        let mut padded = ADD[..30].to_vec();
        padded.extend_from_slice(&[
            0x0a, 0x0a, 0x01, 0x08, 0x00, 0x20, 0x80, 0x00, 0x20, 0x01, 0x6a, 0x0b,
        ]);
        padded.extend_from_slice(&[0x00, 0x01, 0x00]);

        let loaded = load(&padded, Profile::TinyCoreV0, Limits::default()).unwrap();
        assert_eq!(loaded.bytes(), padded);
        assert_eq!(
            loaded.module().function().instructions()[0],
            InstructionKind::LocalGet(0)
        );
        assert_eq!(loaded.sources().instructions()[0].len(), 3);
    }

    #[test]
    fn rejects_leb_beyond_the_width_limit() {
        let mut too_long = ADD[..30].to_vec();
        too_long.extend_from_slice(&[
            0x0a, 0x0e, 0x01, 0x0c, 0x00, 0x20, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00, 0x20, 0x01,
            0x6a, 0x0b,
        ]);
        assert!(matches!(
            load(&too_long, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Invalid { .. })
        ));
    }

    #[test]
    fn rejects_invalid_section_order_duplicates_truncation_and_trailing_bytes() {
        let mut duplicate_type = ADD[..17].to_vec();
        duplicate_type.extend_from_slice(&ADD[8..17]);
        duplicate_type.extend_from_slice(&ADD[17..]);
        assert!(matches!(
            load(&duplicate_type, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Invalid { .. })
        ));

        let mut out_of_order = ADD[..17].to_vec();
        out_of_order.extend_from_slice(&ADD[21..30]);
        out_of_order.extend_from_slice(&ADD[17..21]);
        out_of_order.extend_from_slice(&ADD[30..]);
        assert!(matches!(
            load(&out_of_order, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Invalid { .. })
        ));

        assert!(
            load(
                &ADD[..ADD.len() - 1],
                Profile::TinyCoreV0,
                Limits::default()
            )
            .is_err()
        );

        let mut trailing = ADD.to_vec();
        trailing.push(0xff);
        assert!(load(&trailing, Profile::TinyCoreV0, Limits::default()).is_err());
    }

    #[test]
    fn distinguishes_valid_but_unsupported_types_and_export_shape() {
        assert!(matches!(
            load(I64_IDENTITY, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Unsupported {
                feature: Unsupported::ValueType,
                offset: 10,
            })
        ));

        let mut two_exports = ADD[..21].to_vec();
        two_exports.extend_from_slice(&[
            0x07, 0x0d, 0x02, 0x03, b'a', b'd', b'd', 0x00, 0x00, 0x03, b's', b'u', b'm', 0x00,
            0x00,
        ]);
        two_exports.extend_from_slice(&ADD[30..]);
        assert!(matches!(
            load(&two_exports, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Unsupported {
                feature: Unsupported::ExportShape,
                ..
            })
        ));
    }

    #[test]
    fn component_encoding_is_an_explicit_profile_mismatch() {
        const EMPTY_COMPONENT: &[u8] = &[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00];
        const COMPONENT_WITH_CORE_MODULE: &[u8] = &[
            0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00, 0x01, 0x08, 0x00, 0x61, 0x73, 0x6d,
            0x01, 0x00, 0x00, 0x00,
        ];
        assert!(matches!(
            load(EMPTY_COMPONENT, Profile::TinyCoreV0, Limits::default()),
            Err(LoadError::Encoding)
        ));
        assert!(matches!(
            load(
                COMPONENT_WITH_CORE_MODULE,
                Profile::TinyCoreV0,
                Limits::default()
            ),
            Err(LoadError::Encoding)
        ));
    }
}
