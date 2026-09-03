//! Opt-in validation of the pinned upstream Metamath corpus.

use std::path::Path;

use covalence_logic_metamath::axiom_sets::{GT, HOL, IZF, PA, PROP, ZF, ZFC};
use covalence_logic_metamath::{FileResolver, parse_with_resolver, verify_all};

const DATABASES: &[&str] = &[
    "big-unifier.mm",
    "demo0.mm",
    "hol.mm",
    "iset.mm",
    "miu.mm",
    "nf.mm",
    "peano.mm",
    "ql.mm",
    "set.mm",
];

#[test]
#[ignore = "requires NUCLEUS_METAMATH_CORPUS=/path/to/metamath/set.mm checkout"]
fn upstream_databases_parse_and_validate() {
    let root = std::env::var("NUCLEUS_METAMATH_CORPUS")
        .expect("set NUCLEUS_METAMATH_CORPUS to a checkout of metamath/set.mm");
    let resolver = FileResolver::new(&root);

    for filename in DATABASES {
        assert!(
            Path::new(&root).join(filename).is_file(),
            "missing {filename}"
        );
        let database = parse_with_resolver(filename, &resolver)
            .unwrap_or_else(|error| panic!("{filename} did not parse: {error}"));
        verify_all(&database)
            .unwrap_or_else(|error| panic!("{filename} did not validate: {error}"));
        let named_sets = match *filename {
            "set.mm" => &[&PROP, &ZF, &ZFC, &GT][..],
            "iset.mm" => &[&IZF][..],
            "peano.mm" => &[&PA][..],
            "hol.mm" => &[&HOL][..],
            _ => &[],
        };
        for set in named_sets {
            set.resolve(&database).unwrap_or_else(|error| {
                panic!("{} did not resolve against {filename}: {error}", set.name)
            });
        }
    }
}
