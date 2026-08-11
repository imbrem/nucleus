//! The pinned JSON of one small application term.
//!
//! The fixture is the readable form of the encoding: what a person reads to
//! learn the shape, and what changes visibly in review if the shape changes.
//! The format carries no stability promise, so updating the fixture is a
//! legitimate thing for a change to do — deliberately, and in the diff.

use covalence_kernel_hol::{CoreData, CoreTag, Tree};
use covalence_lib_json::{from_str, to_string_pretty};

/// `(fun (x : bool) => x) true`
fn applied_identity() -> Tree {
    Tree::app(Tree::lam(Tree::bool_ty(), Tree::bound(0)), Tree::bool(true))
}

/// The fixture, with the trailing newline every text file ends with removed.
fn golden() -> &'static str {
    include_str!("golden/tm_app.json").trim_end()
}

#[test]
fn the_application_example_writes_the_pinned_json() {
    assert_eq!(to_string_pretty(&applied_identity()).unwrap(), golden());
}

#[test]
fn the_pinned_json_reads_back_as_the_example() {
    let parsed: Tree = from_str(golden()).unwrap();

    assert_eq!(parsed, applied_identity());
    assert_eq!(parsed.tag(), CoreTag::App);

    let function = &parsed.children()[0];
    assert_eq!(function.tag(), CoreTag::Lam);
    assert_eq!(function.children()[0].tag(), CoreTag::BoolTy);
    assert_eq!(
        function.children()[1].data(),
        Some(&CoreData::Bound { index: 0 })
    );
    assert_eq!(
        parsed.children()[1].data(),
        Some(&CoreData::Bool { value: true })
    );
}
