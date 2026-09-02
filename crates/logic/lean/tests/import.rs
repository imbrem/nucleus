use std::convert::Infallible;
use std::io::Cursor;

use covalence_logic_lean::direct::{DirectDerivation, DirectHol, DirectProofStep};
use covalence_logic_lean::syntax::{Declaration, DefinitionSafety, LeanSyntax, Record, Tables};
use covalence_logic_lean::{Artifacts, Backend, BackendArtifacts, ImportError, Metadata, import};

const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"lean":{"githash":"411dce7db58a3afc60ecab2d211acd1042b593dc","version":"4.34.0-rc2"},"format":{"version":"3.1.0"}}}"#;

#[derive(Default)]
struct RecordingBackend {
    next_object: u32,
    next_theorem: u32,
}

impl Backend for RecordingBackend {
    type Object = u32;
    type Theorem = u32;
    type Derivation = LeanSyntax;
    type Error = Infallible;

    fn begin(
        &mut self,
        _metadata: &Metadata,
        _tables: &Tables,
    ) -> Result<BackendArtifacts<Self>, Self::Error> {
        Ok(Artifacts::default())
    }

    fn lower(
        &mut self,
        record: &Record,
        tables: &Tables,
    ) -> Result<BackendArtifacts<Self>, Self::Error> {
        let syntax = record.syntax(tables);
        let object = self.next_object;
        self.next_object += 1;
        let theorems = if matches!(record, Record::Declaration(_)) {
            let theorem = self.next_theorem;
            self.next_theorem += 1;
            vec![(theorem, syntax.clone())]
        } else {
            Vec::new()
        };
        Ok(Artifacts {
            objects: vec![(object, syntax)],
            theorems,
        })
    }
}

#[test]
fn backend_receives_partial_definition_and_emits_both_mappings() {
    let input = format!(
        "{META}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
         {{\"il\":1,\"succ\":0}}\n\
         {{\"ie\":0,\"sort\":1}}\n\
         {{\"def\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"value\":0,\"hints\":\"abbrev\",\"safety\":\"partial\",\"all\":[]}}}}\n"
    );
    let imported = import(Cursor::new(input), RecordingBackend::default()).unwrap();

    assert_eq!(imported.hol_to_lean().len(), 4);
    assert_eq!(imported.theorem_derivations().len(), 1);
    let Declaration::Definition { safety, .. } = &imported.tables().declarations[0] else {
        panic!("expected definition")
    };
    assert_eq!(*safety, DefinitionSafety::Partial);
}

#[test]
fn direct_backend_lowers_a_small_monomorphic_fragment() {
    let input = format!(
        "{META}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
         {{\"in\":2,\"str\":{{\"pre\":0,\"str\":\"x\"}}}}\n\
         {{\"in\":3,\"str\":{{\"pre\":0,\"str\":\"f\"}}}}\n\
         {{\"in\":4,\"str\":{{\"pre\":0,\"str\":\"z\"}}}}\n\
         {{\"in\":5,\"str\":{{\"pre\":0,\"str\":\"y\"}}}}\n\
         {{\"il\":1,\"succ\":0}}\n\
         {{\"ie\":0,\"sort\":1}}\n\
         {{\"axiom\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n\
         {{\"ie\":1,\"const\":{{\"name\":1,\"us\":[]}}}}\n\
         {{\"axiom\":{{\"name\":2,\"levelParams\":[],\"type\":1,\"isUnsafe\":true}}}}\n\
         {{\"ie\":2,\"forallE\":{{\"name\":0,\"type\":1,\"body\":1,\"binderInfo\":\"default\"}}}}\n\
         {{\"axiom\":{{\"name\":3,\"levelParams\":[],\"type\":2,\"isUnsafe\":false}}}}\n\
         {{\"ie\":3,\"const\":{{\"name\":3,\"us\":[]}}}}\n\
         {{\"ie\":4,\"const\":{{\"name\":2,\"us\":[]}}}}\n\
         {{\"ie\":5,\"app\":{{\"fn\":3,\"arg\":4}}}}\n\
         {{\"def\":{{\"name\":4,\"levelParams\":[],\"type\":1,\"value\":5,\"hints\":\"opaque\",\"safety\":\"partial\",\"all\":[]}}}}\n\
         {{\"def\":{{\"name\":5,\"levelParams\":[],\"type\":1,\"value\":4,\"hints\":\"abbrev\",\"safety\":\"safe\",\"all\":[]}}}}\n"
    );

    let imported = import(Cursor::new(input), DirectHol::new()).unwrap();
    assert_eq!(imported.tables().declarations.len(), 5);
    assert_eq!(imported.hol_to_lean().len(), 4);
    assert_eq!(
        imported.hol_to_lean().values().map(Vec::len).sum::<usize>(),
        5
    );
}

fn projection_proof(bound_variable: usize) -> String {
    format!(
        "{META}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"P\"}}}}\n\
         {{\"in\":2,\"str\":{{\"pre\":0,\"str\":\"Q\"}}}}\n\
         {{\"in\":3,\"str\":{{\"pre\":0,\"str\":\"proof\"}}}}\n\
         {{\"in\":4,\"str\":{{\"pre\":0,\"str\":\"proofAgain\"}}}}\n\
         {{\"ie\":0,\"sort\":0}}\n\
         {{\"axiom\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n\
         {{\"ie\":1,\"const\":{{\"name\":1,\"us\":[]}}}}\n\
         {{\"axiom\":{{\"name\":2,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n\
         {{\"ie\":2,\"const\":{{\"name\":2,\"us\":[]}}}}\n\
         {{\"ie\":3,\"forallE\":{{\"name\":0,\"type\":2,\"body\":1,\"binderInfo\":\"default\"}}}}\n\
         {{\"ie\":4,\"forallE\":{{\"name\":0,\"type\":1,\"body\":3,\"binderInfo\":\"default\"}}}}\n\
         {{\"ie\":5,\"bvar\":{bound_variable}}}\n\
         {{\"ie\":6,\"lam\":{{\"name\":0,\"type\":2,\"body\":5,\"binderInfo\":\"default\"}}}}\n\
         {{\"ie\":7,\"lam\":{{\"name\":0,\"type\":1,\"body\":6,\"binderInfo\":\"default\"}}}}\n\
         {{\"thm\":{{\"name\":3,\"levelParams\":[],\"type\":4,\"value\":7,\"all\":[]}}}}\n\
         {{\"ie\":8,\"const\":{{\"name\":3,\"us\":[]}}}}\n\
         {{\"thm\":{{\"name\":4,\"levelParams\":[],\"type\":4,\"value\":8,\"all\":[]}}}}\n"
    )
}

#[test]
fn direct_backend_checks_an_implication_projection_proof() {
    let imported = import(Cursor::new(projection_proof(1)), DirectHol::new()).unwrap();
    assert_eq!(imported.theorem_derivations().len(), 2);
    for (theorem, derivation) in imported.theorem_derivations() {
        let DirectDerivation::Proof { steps, .. } = derivation else {
            panic!("expected checked proof derivation")
        };
        assert!(!steps.is_empty());
        let resident = imported.backend().kernel().thm().get(*theorem).unwrap();
        assert!(resident.lhs.rows().next().is_none());
        assert!(resident.rhs.rows().next().is_some());
    }
}

#[test]
fn direct_backend_rejects_a_proof_of_the_wrong_proposition() {
    let error = import(Cursor::new(projection_proof(0)), DirectHol::new()).unwrap_err();
    assert!(matches!(error, ImportError::Backend { .. }));
}

fn equality_proof(reflexive: bool) -> String {
    let right = if reflexive { 2 } else { 3 };
    format!(
        "{META}\n\
         {{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"A\"}}}}\n\
         {{\"in\":2,\"str\":{{\"pre\":0,\"str\":\"x\"}}}}\n\
         {{\"in\":3,\"str\":{{\"pre\":0,\"str\":\"y\"}}}}\n\
         {{\"in\":4,\"str\":{{\"pre\":0,\"str\":\"Eq\"}}}}\n\
         {{\"in\":5,\"str\":{{\"pre\":4,\"str\":\"refl\"}}}}\n\
         {{\"in\":6,\"str\":{{\"pre\":0,\"str\":\"proof\"}}}}\n\
         {{\"il\":1,\"succ\":0}}\n\
         {{\"ie\":0,\"sort\":1}}\n\
         {{\"axiom\":{{\"name\":1,\"levelParams\":[],\"type\":0,\"isUnsafe\":false}}}}\n\
         {{\"ie\":1,\"const\":{{\"name\":1,\"us\":[]}}}}\n\
         {{\"axiom\":{{\"name\":2,\"levelParams\":[],\"type\":1,\"isUnsafe\":false}}}}\n\
         {{\"axiom\":{{\"name\":3,\"levelParams\":[],\"type\":1,\"isUnsafe\":false}}}}\n\
         {{\"ie\":2,\"const\":{{\"name\":2,\"us\":[]}}}}\n\
         {{\"ie\":3,\"const\":{{\"name\":3,\"us\":[]}}}}\n\
         {{\"ie\":4,\"const\":{{\"name\":4,\"us\":[0]}}}}\n\
         {{\"ie\":5,\"app\":{{\"fn\":4,\"arg\":1}}}}\n\
         {{\"ie\":6,\"app\":{{\"fn\":5,\"arg\":2}}}}\n\
         {{\"ie\":7,\"app\":{{\"fn\":6,\"arg\":{right}}}}}\n\
         {{\"ie\":8,\"const\":{{\"name\":5,\"us\":[0]}}}}\n\
         {{\"ie\":9,\"app\":{{\"fn\":8,\"arg\":1}}}}\n\
         {{\"ie\":10,\"app\":{{\"fn\":9,\"arg\":2}}}}\n\
         {{\"thm\":{{\"name\":6,\"levelParams\":[],\"type\":7,\"value\":10,\"all\":[]}}}}\n"
    )
}

#[test]
fn direct_backend_checks_lean_equality_reflexivity() {
    let imported = import(Cursor::new(equality_proof(true)), DirectHol::new()).unwrap();
    let (theorem, derivation) = imported.theorem_derivations().iter().next().unwrap();
    let DirectDerivation::Proof {
        proposition, steps, ..
    } = derivation
    else {
        panic!("expected proof derivation")
    };
    assert!(matches!(
        steps.as_slice(),
        [DirectProofStep::EqualityReflexivity { equality, theorem: step, .. }]
            if equality == proposition && step == theorem
    ));
    assert!(imported.backend().kernel().thm().get(*theorem).is_some());
}

#[test]
fn direct_backend_rejects_nonreflexive_equality_as_refl() {
    let error = import(Cursor::new(equality_proof(false)), DirectHol::new()).unwrap_err();
    assert!(matches!(error, ImportError::Backend { .. }));
}
