//! The constructor vocabulary of minimal locally nameless HOL.
//!
//! These are the tags and payloads of the `Nucleus.HolLN` syntax, flattened
//! into a single tag set: the sort a tag belongs to is part of its spelling
//! (`ty.` or `tm.`) rather than a separate field.

use covalence_lib_serde::{Deserialize, Serialize};

/// A constructor of minimal locally nameless HOL.
///
/// The JSON spelling of each tag is fixed here and nowhere else. `Eqn` is
/// spelled `tm.eq`, because `Eq` is taken by the standard library.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(crate = "covalence_lib_serde::serde")]
pub enum CoreTag {
    /// An uninterpreted base type, named by [`CoreData::Base`].
    #[serde(rename = "ty.base")]
    Base,

    /// The type of Booleans.
    #[serde(rename = "ty.bool")]
    BoolTy,

    /// The distinguished infinite type of individuals.
    #[serde(rename = "ty.ind")]
    Ind,

    /// A function type, over its domain and codomain.
    #[serde(rename = "ty.arr")]
    Arr,

    /// A subtype, over its carrier and its one-variable predicate.
    #[serde(rename = "ty.sub")]
    Sub,

    /// A bound variable, by the de Bruijn index in [`CoreData::Bound`].
    #[serde(rename = "tm.bound")]
    Bound,

    /// A free variable, by the stable name in [`CoreData::Free`].
    #[serde(rename = "tm.free")]
    Free,

    /// An application, over its function and argument.
    #[serde(rename = "tm.app")]
    App,

    /// A lambda, over its domain type and its body.
    #[serde(rename = "tm.lam")]
    Lam,

    /// A Boolean literal, valued by [`CoreData::Bool`].
    #[serde(rename = "tm.bool")]
    Bool,

    /// Zero.
    #[serde(rename = "tm.zero")]
    Zero,

    /// A successor, over its predecessor.
    #[serde(rename = "tm.succ")]
    Succ,

    /// An equation, over its type and its two sides.
    #[serde(rename = "tm.eq")]
    Eqn,

    /// A choice term, over its type and its predicate.
    #[serde(rename = "tm.eps")]
    Eps,

    /// A subtype abstraction, over its carrier, predicate, and value.
    #[serde(rename = "tm.abs")]
    Abs,

    /// A subtype representation, over its carrier, predicate, and value.
    #[serde(rename = "tm.rep")]
    Rep,
}

/// The payload of the constructors that carry one.
///
/// Every case is a one-field object, and each is distinguished by that field's
/// name and type, so the JSON form needs no discriminant of its own. Indices
/// and names are exact integers; nothing here is ever a JSON floating-point
/// value.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(
    crate = "covalence_lib_serde::serde",
    untagged,
    deny_unknown_fields,
    expecting = "a HOL node payload: {\"name\": string}, {\"index\": integer}, {\"name\": integer}, or {\"value\": boolean}"
)]
pub enum CoreData {
    /// The name of an uninterpreted base type, for [`CoreTag::Base`].
    Base {
        /// The base type's name.
        name: String,
    },

    /// A de Bruijn index, for [`CoreTag::Bound`].
    Bound {
        /// How many binders separate the variable from its own.
        index: u64,
    },

    /// A free variable's stable name, for [`CoreTag::Free`].
    Free {
        /// The variable's name.
        name: u64,
    },

    /// A Boolean literal's value, for [`CoreTag::Bool`].
    Bool {
        /// The literal.
        value: bool,
    },
}

#[cfg(test)]
mod tests {
    use super::{CoreData, CoreTag};

    use covalence_lib_json::{from_str, to_string};

    const TAGS: [(CoreTag, &str); 16] = [
        (CoreTag::Base, "ty.base"),
        (CoreTag::BoolTy, "ty.bool"),
        (CoreTag::Ind, "ty.ind"),
        (CoreTag::Arr, "ty.arr"),
        (CoreTag::Sub, "ty.sub"),
        (CoreTag::Bound, "tm.bound"),
        (CoreTag::Free, "tm.free"),
        (CoreTag::App, "tm.app"),
        (CoreTag::Lam, "tm.lam"),
        (CoreTag::Bool, "tm.bool"),
        (CoreTag::Zero, "tm.zero"),
        (CoreTag::Succ, "tm.succ"),
        (CoreTag::Eqn, "tm.eq"),
        (CoreTag::Eps, "tm.eps"),
        (CoreTag::Abs, "tm.abs"),
        (CoreTag::Rep, "tm.rep"),
    ];

    #[test]
    fn tags_use_their_dotted_spelling() {
        for (tag, spelling) in TAGS {
            let rendered = to_string(&tag).unwrap();

            assert_eq!(rendered, format!("\"{spelling}\""));
            assert_eq!(from_str::<CoreTag>(&rendered).unwrap(), tag);
        }
    }

    #[test]
    fn unknown_tags_are_rejected() {
        assert!(from_str::<CoreTag>("\"tm.eqn\"").is_err());
        assert!(from_str::<CoreTag>("\"ty.nat\"").is_err());
    }

    #[test]
    fn payloads_are_untagged_objects() {
        let cases = [
            (
                CoreData::Base {
                    name: "unit".to_owned(),
                },
                r#"{"name":"unit"}"#,
            ),
            (CoreData::Bound { index: 0 }, r#"{"index":0}"#),
            (CoreData::Free { name: 7 }, r#"{"name":7}"#),
            (CoreData::Bool { value: true }, r#"{"value":true}"#),
        ];

        for (data, rendered) in cases {
            assert_eq!(to_string(&data).unwrap(), rendered);
            assert_eq!(from_str::<CoreData>(rendered).unwrap(), data);
        }
    }

    #[test]
    fn payload_fields_are_exact() {
        assert!(from_str::<CoreData>(r#"{"index":-1}"#).is_err());
        assert!(from_str::<CoreData>(r#"{"index":1.5}"#).is_err());
        assert!(from_str::<CoreData>(r#"{"index":"0"}"#).is_err());
        assert!(from_str::<CoreData>(r#"{"name":true}"#).is_err());
        assert!(from_str::<CoreData>(r#"{"value":1}"#).is_err());
        assert!(from_str::<CoreData>(r#"{"index":0,"extra":0}"#).is_err());
    }
}
