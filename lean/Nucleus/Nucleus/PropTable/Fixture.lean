import Nucleus.PropTable
import Lean

/-!
# Shared proposition-table fixture

This module makes the language-neutral local corpus a Lean build input.  The
Rust/SQLite test performs the semantic admission checks; Lean checks that the
same records remain parseable as the logical four-word row shape.  This is
differential evidence, not a refinement proof.
-/

namespace Nucleus.PropTable.Fixture

set_option linter.style.nativeDecide false in
section

open Lean Elab Term

syntax "fixture_str% " str : term

elab_rules : term
  | `(fixture_str% $path:str) => do
      let source := System.FilePath.mk (← getFileName)
      let propTable := source.parent.getD source
      let namespaceDir := propTable.parent.getD propTable
      let project := namespaceDir.parent.getD namespaceDir
      let lean := project.parent.getD project
      let root := lean.parent.getD lean
      let contents ← IO.FS.readFile (root / path.getString)
      elabTerm (Syntax.mkStrLit contents) none

private def corpus : String :=
  fixture_str% "crates/nucleus/fixtures/local_prop_v1.tsv"

private def queryCorpus : String :=
  fixture_str% "crates/nucleus/fixtures/local_prop_queries_v1.tsv"

private def deletionCorpus : String :=
  fixture_str% "crates/nucleus/fixtures/local_prop_deletion_v1.tsv"

private def satCorpus : String :=
  fixture_str% "crates/nucleus/fixtures/local_prop_sat_v1.tsv"

private def dataLines (contents : String) : List String :=
  (contents.splitOn "\n").filter fun line =>
    !line.isEmpty && !(line.startsWith "#")

private def records : List String :=
  dataLines corpus

private def parseRecord (line : String) : Option (String × String × Int × Int × Option Int × Int) :=
  match line.splitOn "\t" with
  | [name, outcome, premise, source, conclusion, reason] => do
      let premise ← premise.toInt?
      let source ← source.toInt?
      let conclusion ← if conclusion = "." then some none else conclusion.toInt?.map some
      let reason ← reason.toInt?
      some (name, outcome, premise, source, conclusion, reason)
  | _ => none

example : records.length = 19 := by native_decide

example : records.all (parseRecord · |>.isSome) := by native_decide

example : (records.filter fun (line : String) =>
    (String.splitOn line "\t").getD 1 "" == "accept").length = 5 := by
  native_decide

example : (records.filter fun line => line.startsWith "reason-conflict\t").length = 2 := by
  native_decide

example : (dataLines queryCorpus).length = 9 := by native_decide

example : (dataLines queryCorpus).all fun line => (line.splitOn "\t").length == 4 := by
  native_decide

example : (dataLines deletionCorpus).length = 8 := by native_decide

example : (dataLines deletionCorpus).all fun line => (line.splitOn "\t").length == 4 := by
  native_decide

example : (dataLines satCorpus).length = 16 := by native_decide

example : (dataLines satCorpus).all fun line => (line.splitOn "\t").length == 5 := by
  native_decide

example : (dataLines satCorpus).all fun line =>
    ["definition", "problem", "clause", "reject"].contains
      ((line.splitOn "\t").getD 1 "") := by
  native_decide

end

end Nucleus.PropTable.Fixture
