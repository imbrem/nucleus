//! The direct JSON encoding of [`Tree`].
//!
//! A node is one object: its tag, then the parts it actually has.
//!
//! ```json
//! {
//!   "tag": "tm.app",
//!   "children": [
//!     {
//!       "tag": "tm.lam",
//!       "children": [
//!         { "tag": "ty.bool" },
//!         { "tag": "tm.bound", "data": { "index": 0 } }
//!       ]
//!     },
//!     { "tag": "tm.bool", "data": { "value": true } }
//!   ]
//! }
//! ```
//!
//! Empty children, absent payloads, and absent annotations are omitted rather
//! than written as `[]` or `null`, and reading accepts either spelling.
//! Unknown members are rejected.
//!
//! Deserialization builds the shared tree directly, with no intermediate
//! representation. It does not preserve sharing: a subtree reachable twice is
//! written twice and read back as two nodes. Recovering that sharing is the
//! job of a content-addressed representation, not of this format. The format
//! is experimental and may change without notice.

use std::fmt;
use std::marker::PhantomData;

use covalence_lib_serde::de::{Error as _, MapAccess, Visitor};
use covalence_lib_serde::ser::SerializeStruct;
use covalence_lib_serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{CoreData, CoreTag, Hol, Tree, TreeNode};

/// The name reported to self-describing formats.
const NAME: &str = "Hol";

/// Every member a node may carry, in the order they are written.
const FIELDS: &[&str] = &["tag", "children", "data", "meta"];

impl<M: Serialize> Serialize for TreeNode<M> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let children = self.children();
        let data = self.data().as_ref();
        let meta = self.meta().as_ref();

        let present = 1
            + usize::from(!children.is_empty())
            + usize::from(data.is_some())
            + usize::from(meta.is_some());
        let mut node = serializer.serialize_struct(NAME, present)?;

        node.serialize_field("tag", self.tag())?;
        if children.is_empty() {
            node.skip_field("children")?;
        } else {
            node.serialize_field("children", children)?;
        }
        if let Some(data) = data {
            node.serialize_field("data", data)?;
        } else {
            node.skip_field("data")?;
        }
        if let Some(meta) = meta {
            node.serialize_field("meta", meta)?;
        } else {
            node.skip_field("meta")?;
        }

        node.end()
    }
}

impl<M: Serialize> Serialize for Tree<M> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.node().serialize(serializer)
    }
}

impl<'de, M: Deserialize<'de>> Deserialize<'de> for TreeNode<M> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_struct(NAME, FIELDS, NodeVisitor(PhantomData))
    }
}

impl<'de, M: Deserialize<'de>> Deserialize<'de> for Tree<M> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        TreeNode::deserialize(deserializer).map(Self::from_node)
    }
}

/// A member of the node object; anything else is an error.
#[derive(Deserialize)]
#[serde(
    crate = "covalence_lib_serde::serde",
    field_identifier,
    rename_all = "lowercase"
)]
enum Field {
    Tag,
    Children,
    Data,
    Meta,
}

/// Reads one node, and through its children the whole tree beneath it.
struct NodeVisitor<M>(PhantomData<M>);

impl<'de, M: Deserialize<'de>> Visitor<'de> for NodeVisitor<M> {
    type Value = TreeNode<M>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a HOL syntax node")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut tag: Option<CoreTag> = None;
        let mut children: Option<Vec<Tree<M>>> = None;
        let mut data: Option<Option<CoreData>> = None;
        let mut meta: Option<Option<M>> = None;

        while let Some(field) = map.next_key()? {
            match field {
                Field::Tag => {
                    if tag.is_some() {
                        return Err(A::Error::duplicate_field("tag"));
                    }
                    tag = Some(map.next_value()?);
                }
                Field::Children => {
                    if children.is_some() {
                        return Err(A::Error::duplicate_field("children"));
                    }
                    children = Some(map.next_value()?);
                }
                Field::Data => {
                    if data.is_some() {
                        return Err(A::Error::duplicate_field("data"));
                    }
                    data = Some(map.next_value()?);
                }
                Field::Meta => {
                    if meta.is_some() {
                        return Err(A::Error::duplicate_field("meta"));
                    }
                    meta = Some(map.next_value()?);
                }
            }
        }

        Ok(Hol::new(
            tag.ok_or_else(|| A::Error::missing_field("tag"))?,
            children.unwrap_or_default(),
            data.flatten(),
            meta.flatten(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::{CoreTag, Tree};
    use crate::TreeRepr;

    use covalence_lib_json::{from_str, to_string};
    use covalence_lib_serde::{Deserialize, Serialize};

    /// A caller-defined annotation, to show metadata really is generic.
    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    #[serde(crate = "covalence_lib_serde::serde")]
    struct Span {
        start: u32,
        end: u32,
    }

    /// One tree per tag, each in a shape that tag would really appear in.
    fn every_tag() -> Vec<(CoreTag, Tree)> {
        vec![
            (CoreTag::Base, Tree::base("addr")),
            (CoreTag::BoolTy, Tree::bool_ty()),
            (CoreTag::Ind, Tree::ind()),
            (CoreTag::Arr, Tree::arr(Tree::bool_ty(), Tree::ind())),
            (CoreTag::Sub, Tree::subtype(Tree::ind(), Tree::bound(0))),
            (CoreTag::Bound, Tree::bound(0)),
            (CoreTag::Free, Tree::free(3)),
            (CoreTag::App, Tree::app(Tree::bound(0), Tree::bool(true))),
            (CoreTag::Lam, Tree::lam(Tree::bool_ty(), Tree::bound(0))),
            (CoreTag::Bool, Tree::bool(false)),
            (CoreTag::Zero, Tree::zero()),
            (CoreTag::Succ, Tree::succ(Tree::zero())),
            (
                CoreTag::Eqn,
                Tree::eqn(Tree::ind(), Tree::zero(), Tree::succ(Tree::zero())),
            ),
            (CoreTag::Eps, Tree::eps(Tree::ind(), Tree::bool(true))),
            (
                CoreTag::Abs,
                Tree::abs(Tree::ind(), Tree::bool(true), Tree::zero()),
            ),
            (
                CoreTag::Rep,
                Tree::rep(Tree::ind(), Tree::bool(true), Tree::zero()),
            ),
        ]
    }

    #[test]
    fn every_tag_round_trips() {
        for (tag, tree) in every_tag() {
            let rendered = to_string(&tree).unwrap();
            let parsed: Tree = from_str(&rendered).unwrap_or_else(|error| {
                panic!("{tag:?} did not parse back from {rendered}: {error}")
            });

            assert_eq!(parsed.tag(), tag);
            assert_eq!(parsed, tree, "{tag:?} did not round-trip");
        }
    }

    #[test]
    fn absent_parts_are_omitted() {
        assert_eq!(
            to_string(&Tree::<()>::zero()).unwrap(),
            r#"{"tag":"tm.zero"}"#
        );
        assert_eq!(
            to_string(&Tree::<()>::bound(0)).unwrap(),
            r#"{"tag":"tm.bound","data":{"index":0}}"#
        );
        assert_eq!(
            to_string(&Tree::<()>::succ(Tree::zero())).unwrap(),
            r#"{"tag":"tm.succ","children":[{"tag":"tm.zero"}]}"#
        );
    }

    #[test]
    fn omitted_and_null_parts_read_the_same() {
        let bare: Tree = from_str(r#"{"tag":"tm.zero"}"#).unwrap();
        let spelled_out: Tree =
            from_str(r#"{"tag":"tm.zero","children":[],"data":null,"meta":null}"#).unwrap();

        assert_eq!(bare, spelled_out);
        assert_eq!(bare.children(), &[] as &[Tree]);
        assert_eq!(bare.data(), None);
        assert_eq!(bare.meta(), None);
    }

    #[test]
    fn metadata_round_trips_and_stays_optional() {
        let annotated =
            Tree::app(Tree::bound(0), Tree::bool(true)).with_meta(Span { start: 0, end: 11 });
        let rendered = to_string(&annotated).unwrap();

        assert_eq!(
            rendered,
            concat!(
                r#"{"tag":"tm.app","children":["#,
                r#"{"tag":"tm.bound","data":{"index":0}},"#,
                r#"{"tag":"tm.bool","data":{"value":true}}"#,
                r#"],"meta":{"start":0,"end":11}}"#
            )
        );
        assert_eq!(from_str::<Tree<Span>>(&rendered).unwrap(), annotated);

        let unannotated: Tree<Span> = Tree::zero();
        assert_eq!(to_string(&unannotated).unwrap(), r#"{"tag":"tm.zero"}"#);
        assert_eq!(
            from_str::<Tree<Span>>(r#"{"tag":"tm.zero"}"#)
                .unwrap()
                .meta(),
            None
        );
    }

    #[test]
    fn indices_and_names_are_exact_integers() {
        let large = Tree::<()>::bound(u64::MAX);
        let rendered = to_string(&large).unwrap();

        assert_eq!(
            rendered,
            r#"{"tag":"tm.bound","data":{"index":18446744073709551615}}"#
        );
        assert_eq!(from_str::<Tree>(&rendered).unwrap(), large);
        assert_eq!(
            to_string(&Tree::<()>::free(u64::MAX)).unwrap(),
            r#"{"tag":"tm.free","data":{"name":18446744073709551615}}"#
        );
    }

    #[test]
    fn non_integral_indices_are_rejected() {
        for payload in [
            r#"{"index":-1}"#,
            r#"{"index":1.5}"#,
            r#"{"index":1.0}"#,
            r#"{"index":1e2}"#,
            r#"{"index":18446744073709551616}"#,
        ] {
            let document = format!(r#"{{"tag":"tm.bound","data":{payload}}}"#);
            assert!(
                from_str::<Tree>(&document).is_err(),
                "{document} should not have parsed"
            );
        }
    }

    #[test]
    fn malformed_nodes_are_rejected() {
        assert!(from_str::<Tree>(r#"{"children":[]}"#).is_err(), "no tag");
        assert!(
            from_str::<Tree>(r#"{"tag":"tm.zero","tag":"tm.zero"}"#).is_err(),
            "duplicate tag"
        );
        assert!(
            from_str::<Tree>(r#"{"tag":"tm.zero","depth":0}"#).is_err(),
            "unknown member"
        );
        assert!(
            from_str::<Tree>(r#"{"tag":"tm.zero","meta":{"start":0}}"#).is_err(),
            "annotation where none is expected"
        );
        assert!(from_str::<Tree>(r#"["tm.zero"]"#).is_err(), "not an object");
    }

    #[test]
    fn reading_does_not_preserve_sharing() {
        let shared = Tree::<()>::zero();
        let tree = Tree::eqn(Tree::ind(), shared.clone(), shared.clone());
        let parsed: Tree = from_str(&to_string(&tree).unwrap()).unwrap();

        assert_eq!(parsed, tree);
        assert!(Tree::ptr_eq(&tree.children()[1], &tree.children()[2]));
        assert!(!Tree::ptr_eq(&parsed.children()[1], &parsed.children()[2]));
    }

    #[test]
    fn nodes_serialize_the_same_as_the_trees_holding_them() {
        let tree = Tree::<()>::succ(Tree::zero());

        assert_eq!(
            to_string(tree.node()).unwrap(),
            to_string(&tree).unwrap(),
            "a bare node and a shared one agree"
        );
    }

    #[test]
    fn the_representation_is_the_documented_one() {
        fn assert_repr<M>()
        where
            TreeRepr<M>: crate::Repr<
                    Tag = CoreTag,
                    Index = Tree<M>,
                    Children = Vec<Tree<M>>,
                    Data = Option<crate::CoreData>,
                    Meta = Option<M>,
                >,
        {
        }

        assert_repr::<()>();
        assert_repr::<Span>();
    }
}
