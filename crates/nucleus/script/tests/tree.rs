use std::collections::BTreeMap;

use covalence_data_vfs::{Bytes, MemoryVfs, ResourceVfs};
use covalence_nucleus_script::{TreeError, compile_tree};

fn library(extra: &[(&str, &[u8])]) -> MemoryVfs {
    let mut files = BTreeMap::from([
        (
            "logic.defs".to_owned(),
            Bytes::from_static(include_bytes!("../library/logic/defs.cov")),
        ),
        (
            "logic".to_owned(),
            Bytes::from_static(include_bytes!("../library/logic.cov")),
        ),
        (
            "logic.basic".to_owned(),
            Bytes::from_static(include_bytes!("../library/logic/basic.cov")),
        ),
        (
            "data.coprod.defs".to_owned(),
            Bytes::from_static(include_bytes!("../library/data/coprod/defs.cov")),
        ),
        (
            "data.prod.defs".to_owned(),
            Bytes::from_static(include_bytes!("../library/data/prod/defs.cov")),
        ),
        (
            "nat.defs".to_owned(),
            Bytes::from_static(include_bytes!("../library/nat/defs.cov")),
        ),
        (
            "nat.spec".to_owned(),
            Bytes::from_static(include_bytes!("../library/nat/spec.cov")),
        ),
        (
            "nat.rec".to_owned(),
            Bytes::from_static(include_bytes!("../library/nat/rec.cov")),
        ),
        (
            "nat.arithmetic".to_owned(),
            Bytes::from_static(include_bytes!("../library/nat/arithmetic.cov")),
        ),
    ]);
    files.extend(
        extra
            .iter()
            .map(|(path, data)| ((*path).to_owned(), Bytes::copy_from_slice(data))),
    );
    MemoryVfs::new(files)
}

#[test]
fn library_tree_compiles_once_in_dependency_order() {
    let resources = library(&[("tactics/cache.sqlite", b"SQLite format 3\0")]);
    let tree = compile_tree("nat.defs", &resources).expect("compile source tree");
    assert_eq!(tree.root(), "nat.defs");
    assert_eq!(
        tree.sources()
            .iter()
            .map(covalence_nucleus_script::SourceUnit::resource)
            .collect::<Vec<_>>(),
        [
            "logic.defs",
            "logic.basic",
            "logic",
            "nat.spec",
            "nat.rec",
            "nat.arithmetic",
            "nat.defs",
        ]
    );
    assert!(tree.module().namespace().get("logic.defs.and").is_some());
    assert!(tree.namespace().get("nat.defs.NatRecSpec").is_some());
    assert!(tree.namespace().get("nat.defs.NatSpec").is_some());
    assert!(tree.namespace().get("nat.defs.AddSpec").is_some());
    assert!(tree.namespace().get("nat.defs.DivModSpec").is_some());
    assert!(
        tree.module()
            .namespace()
            .get("logic.basic.and.comm")
            .is_some()
    );
    assert!(tree.namespace().get("logic.and").is_none());
    assert!(
        tree.module()
            .namespace()
            .get("nat.rec.NatRecSpec")
            .is_some()
    );

    let whole = ResourceVfs::read(&resources, "tactics/cache.sqlite").expect("resource bytes");
    assert_eq!(&whole[..6], b"SQLite");

    let coproduct = compile_tree("data.coprod.defs", &resources).expect("coproduct theory");
    assert!(
        coproduct
            .namespace()
            .get("data.coprod.defs.IsCoprod")
            .is_some()
    );
    let product = compile_tree("data.prod.defs", &resources).expect("product theory");
    assert!(product.namespace().get("data.prod.defs.IsProd").is_some());
}

#[test]
fn imports_are_private_until_explicitly_reexported() {
    let resources = library(&[
        ("hidden.defs", b"(define value () bool true)"),
        ("private", b"(import hidden.defs)"),
        (
            "module-export",
            b"(import hidden.defs) (export hidden.defs)",
        ),
        (
            "renamed",
            b"(import hidden.defs) (export (hidden.defs implementation))",
        ),
        ("opened", b"(import hidden.defs) (include hidden.defs)"),
        (
            "snoop",
            b"(import private) (define bad () bool hidden.defs.value)",
        ),
    ]);

    let private = compile_tree("private", &resources).expect("private import");
    assert!(private.namespace().get("hidden.defs.value").is_none());

    let module = compile_tree("module-export", &resources).expect("module export");
    assert!(module.namespace().get("hidden.defs.value").is_some());

    let renamed = compile_tree("renamed", &resources).expect("renamed export");
    assert!(
        renamed
            .namespace()
            .get("renamed.implementation.value")
            .is_some()
    );
    assert!(renamed.namespace().get("hidden.defs.value").is_none());

    let opened = compile_tree("opened", &resources).expect("open export");
    assert!(opened.namespace().get("opened.value").is_some());
    assert!(opened.namespace().get("hidden.defs.value").is_none());

    assert!(matches!(
        compile_tree("snoop", &resources),
        Err(TreeError::PrivateName { .. })
    ));
}

#[test]
fn cycles_missing_files_and_binary_cov_sources_are_rejected() {
    let cycle = library(&[
        ("cycle.a", b"(import cycle.b)"),
        ("cycle.b", b"(import cycle.a)"),
    ]);
    assert!(matches!(
        compile_tree("cycle.a", &cycle),
        Err(TreeError::Cycle { .. })
    ));
    assert!(matches!(
        compile_tree("absent.defs", &cycle),
        Err(TreeError::Resource { .. })
    ));

    let binary = library(&[("binary.defs", &[0xff, 0x00])]);
    assert!(matches!(
        compile_tree("binary.defs", &binary),
        Err(TreeError::Utf8 { .. })
    ));
}
