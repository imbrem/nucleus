//! Untrusted, named DAG-JSON source for the existing HOL arena wire value.
//!
//! Names are editing metadata carried by rows. Compilation removes them and
//! resolves string references to one-based indices before deserializing through
//! the ordinary raw-arena Serde view. Neither direction checks or creates facts.

use std::collections::BTreeMap;

use covalence_lib_error::snafu::Snafu;
use covalence_lib_json::Value;
use covalence_logic_hol::{Arena, Ref, wire};

/// A rejected named arena source document.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The JSON value does not have the existing arena wire shape.
    #[snafu(display("invalid arena JSON at {path}: {message}"))]
    Shape { path: String, message: String },
    /// Two rows define the same editing name.
    #[snafu(display("duplicate arena row name {name:?}"))]
    DuplicateName { name: String },
    /// A string reference does not name a row in the same `defs` table.
    #[snafu(display("unknown arena row name {name:?} at {path}"))]
    UnknownName { path: String, name: String },
    /// The resolved JSON does not deserialize as the current arena wire value.
    #[snafu(display("resolved JSON is not an arena: {message}"))]
    Arena { message: String },
    /// The arena cannot be represented as JSON.
    #[snafu(display("could not render arena as JSON: {message}"))]
    Render { message: String },
    /// The current canonical arena encoder rejected the resolved arena.
    #[snafu(display("could not encode resolved arena: {message}"))]
    Encode { message: String },
    /// The current arena decoder rejected CBOR input to the pretty-printer.
    #[snafu(display("could not decode arena CBOR: {message}"))]
    Decode { message: String },
    /// More than one external name points at one definition row.
    #[snafu(display("row {reference} has both names {first:?} and {second:?}"))]
    NameCollision {
        reference: i32,
        first: String,
        second: String,
    },
}

/// Compiles named arena JSON to the existing canonical CBOR format.
///
/// Numeric references remain accepted. String references are resolved against
/// `name` keys on rows in this document's own `hol.defs` array. Names may refer
/// forward or backward because they are metadata, not construction order.
///
/// # Errors
///
/// Returns an error for a malformed arena shape, duplicate or unknown names,
/// an arena rejected by the existing raw wire deserializer, or CBOR encoding.
pub fn compile(value: &Value) -> Result<Vec<u8>, Error> {
    let mut value = value.clone();
    let names = collect_names(defs_mut(&mut value)?)?;
    resolve_arena_refs(&mut value, &names)?;
    let arena: Arena = covalence_lib_json::from_value(value).map_err(|error| Error::Arena {
        message: error.to_string(),
    })?;
    let mut bytes = Vec::new();
    wire::serialize(&arena, &mut bytes).map_err(|error| Error::Encode {
        message: error.to_string(),
    })?;
    Ok(bytes)
}

/// Pretty-prints an arena wire value with optional names on definition rows.
///
/// References whose target has a supplied name are rendered using that name;
/// all other references retain their one-based numeric spelling.
///
/// # Errors
///
/// Returns an error if names are nonresident or collide, or if the arena's
/// existing Serde view cannot be represented as JSON.
pub fn render<'a>(
    arena: &Arena,
    names: impl IntoIterator<Item = (&'a str, Ref)>,
) -> Result<Value, Error> {
    let mut by_index = BTreeMap::new();
    for (name, reference) in names {
        if usize::try_from(reference.get())
            .ok()
            .is_none_or(|ix| ix == 0 || ix > arena.len())
        {
            return Err(Error::Shape {
                path: "$.hol.defs".into(),
                message: format!("name {name:?} points outside the definition table"),
            });
        }
        if let Some(first) = by_index.insert(reference.get(), name.to_owned()) {
            return Err(Error::NameCollision {
                reference: reference.get(),
                first,
                second: name.to_owned(),
            });
        }
    }
    let mut value = covalence_lib_json::to_value(arena).map_err(|error| Error::Render {
        message: error.to_string(),
    })?;
    let defs = defs_mut(&mut value)?;
    for (position, row) in defs.iter_mut().enumerate() {
        let index = i32::try_from(position + 1).map_err(|_| {
            shape(
                "$.hol.defs",
                "definition table length exceeds the reference range",
            )
        })?;
        if let Some(name) = by_index.get(&index) {
            row.as_object_mut()
                .ok_or_else(|| shape(row_path(position), "row must be an object"))?
                .insert("name".into(), Value::String(name.clone()));
        }
    }
    render_arena_refs(&mut value, &by_index)?;
    Ok(value)
}

/// Pretty-prints canonical arena CBOR as named JSON.
///
/// # Errors
///
/// Returns an error if the existing wire decoder rejects the bytes, or if
/// [`render`] rejects the supplied names.
pub fn render_cbor<'a>(
    bytes: &[u8],
    names: impl IntoIterator<Item = (&'a str, Ref)>,
) -> Result<Value, Error> {
    let arena = wire::deserialize(bytes).map_err(|error| Error::Decode {
        message: error.to_string(),
    })?;
    render(&arena, names)
}

fn defs_mut(value: &mut Value) -> Result<&mut Vec<Value>, Error> {
    value
        .get_mut("hol")
        .and_then(|v| v.get_mut("defs"))
        .and_then(Value::as_array_mut)
        .ok_or_else(|| shape("$.hol.defs", "must be an array"))
}

fn collect_names(defs: &mut [Value]) -> Result<BTreeMap<String, i32>, Error> {
    let mut names = BTreeMap::new();
    for (position, row) in defs.iter_mut().enumerate() {
        let object = row
            .as_object_mut()
            .ok_or_else(|| shape(row_path(position), "row must be an object"))?;
        let Some(name) = object.remove("name") else {
            continue;
        };
        let name = name
            .as_str()
            .ok_or_else(|| shape(format!("{}.name", row_path(position)), "must be a string"))?;
        if name.is_empty() {
            return Err(shape(
                format!("{}.name", row_path(position)),
                "must not be empty",
            ));
        }
        let index = i32::try_from(position + 1).expect("JSON arrays cannot exceed i32 in practice");
        if names.insert(name.to_owned(), index).is_some() {
            return Err(Error::DuplicateName {
                name: name.to_owned(),
            });
        }
    }
    Ok(names)
}

fn resolve_arena_refs(value: &mut Value, names: &BTreeMap<String, i32>) -> Result<(), Error> {
    visit_ref_fields(value, &mut |reference, path| {
        if let Value::String(name) = reference {
            let index = names.get(name).ok_or_else(|| Error::UnknownName {
                path: path.to_owned(),
                name: name.clone(),
            })?;
            *reference = Value::from(*index);
        }
        Ok(())
    })
}

fn render_arena_refs(value: &mut Value, names: &BTreeMap<i32, String>) -> Result<(), Error> {
    visit_ref_fields(value, &mut |reference, _| {
        if let Some(index) = reference.as_i64().and_then(|n| i32::try_from(n).ok())
            && let Some(name) = names.get(&index)
        {
            *reference = Value::String(name.clone());
        }
        Ok(())
    })
}

// Ref occurrences in the current arena Serde schema. The init slice has only
// definition-row children, but columns and contexts are covered as well.
fn visit_ref_fields(
    value: &mut Value,
    visit: &mut impl FnMut(&mut Value, &str) -> Result<(), Error>,
) -> Result<(), Error> {
    let hol = value
        .get_mut("hol")
        .and_then(Value::as_object_mut)
        .ok_or_else(|| shape("$.hol", "must be an object"))?;
    visit_rows(
        hol.get_mut("defs")
            .ok_or_else(|| shape("$.hol.defs", "is required"))?,
        "$.hol.defs",
        visit,
    )?;
    for key in ["ctx", "eq"] {
        if let Some(field) = hol.get_mut(key) {
            visit_array_refs(field, &format!("$.hol.{key}"), visit)?;
        }
    }
    if let Some(syn) = hol.get_mut("syn").and_then(Value::as_object_mut) {
        for key in ["eq", "conv"] {
            if let Some(field) = syn.get_mut(key) {
                visit_array_refs(field, &format!("$.hol.syn.{key}"), visit)?;
            }
        }
    }
    Ok(())
}

fn visit_rows(
    value: &mut Value,
    path: &str,
    visit: &mut impl FnMut(&mut Value, &str) -> Result<(), Error>,
) -> Result<(), Error> {
    let rows = value
        .as_array_mut()
        .ok_or_else(|| shape(path, "must be an array"))?;
    for (position, row) in rows.iter_mut().enumerate() {
        let object = row
            .as_object_mut()
            .ok_or_else(|| shape(format!("{path}[{position}]"), "must be an object"))?;
        if let Some(ixs) = object.get_mut("ixs") {
            visit_array_refs(ixs, &format!("{path}[{position}].ixs"), visit)?;
        }
        if let Some(ix) = object.get_mut("ix") {
            visit(ix, &format!("{path}[{position}].ix"))?;
        }
    }
    Ok(())
}

fn visit_array_refs(
    value: &mut Value,
    path: &str,
    visit: &mut impl FnMut(&mut Value, &str) -> Result<(), Error>,
) -> Result<(), Error> {
    let values = value
        .as_array_mut()
        .ok_or_else(|| shape(path, "must be an array"))?;
    for (position, value) in values.iter_mut().enumerate() {
        if !value.is_null() {
            visit(value, &format!("{path}[{position}]"))?;
        }
    }
    Ok(())
}

fn row_path(position: usize) -> String {
    format!("$.hol.defs[{position}]")
}
fn shape(path: impl Into<String>, message: impl Into<String>) -> Error {
    Error::Shape {
        path: path.into(),
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile_init_slice;
    use covalence_logic_hol::init;

    #[cfg(not(feature = "buck-test-fixtures"))]
    const SOURCE: &str = include_str!("../theories/init.dag.json");
    #[cfg(feature = "buck-test-fixtures")]
    const SOURCE: &str = include_str!("init.dag.json");
    #[cfg(not(feature = "buck-test-fixtures"))]
    const LOGICAL_INIT: &str = include_str!("../../../../theories/init-boolean.checked.json");
    #[cfg(feature = "buck-test-fixtures")]
    const LOGICAL_INIT: &str = include_str!("init-boolean.checked.json");

    fn current_slice() -> crate::InitSlice {
        let manifest: init::Manifest = covalence_lib_json::from_str(LOGICAL_INIT).unwrap();
        let logical = init::compile(&manifest).unwrap();
        compile_init_slice(&logical).unwrap()
    }

    #[test]
    fn checked_in_json_compiles_to_the_current_exact_cbor_init_segment() {
        let source: Value = covalence_lib_json::from_str(SOURCE).unwrap();
        let actual = compile(&source).unwrap();
        let slice = current_slice();
        let mut expected = Vec::new();
        wire::serialize(slice.prefix().arena(), &mut expected).unwrap();

        assert_eq!(actual, expected);
        assert_eq!(
            wire::deserialize(actual.as_slice()).unwrap(),
            *slice.prefix().arena()
        );
        assert_eq!(render_cbor(&actual, slice.symbols()).unwrap(), source);
    }

    #[test]
    fn names_are_local_metadata_and_numeric_references_remain_valid() {
        let mut source: Value = covalence_lib_json::from_str(SOURCE).unwrap();
        let expected = compile(&source).unwrap();
        let defs = defs_mut(&mut source).unwrap();
        defs[0]
            .as_object_mut()
            .unwrap()
            .insert("name".into(), Value::String("renamed-star".into()));
        visit_ref_fields(&mut source, &mut |reference, _| {
            if reference == "star" {
                *reference = Value::from(1);
            }
            Ok(())
        })
        .unwrap();
        assert_eq!(compile(&source).unwrap(), expected);
    }

    #[test]
    fn malformed_names_are_rejected_before_arena_deserialization() {
        let mut source: Value = covalence_lib_json::from_str(SOURCE).unwrap();
        defs_mut(&mut source).unwrap()[1]
            .as_object_mut()
            .unwrap()
            .insert("name".into(), Value::String("star".into()));
        assert!(matches!(compile(&source), Err(Error::DuplicateName { .. })));

        let mut source: Value = covalence_lib_json::from_str(SOURCE).unwrap();
        defs_mut(&mut source).unwrap()[2]["ixs"][0] = Value::String("missing".into());
        assert!(matches!(compile(&source), Err(Error::UnknownName { .. })));
    }
}
