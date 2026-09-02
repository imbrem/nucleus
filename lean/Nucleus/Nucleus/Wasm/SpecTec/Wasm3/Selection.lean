/-!
# Audit selectors for the first Wasm 3.0 execution slice

These constants record exact locations consulted while constructing the Lean
reference models. They are unverified metadata: no theorem in this module reads
the artifacts, checks the selectors, or assigns them semantics.
-/

namespace Nucleus.Wasm.SpecTec.Wasm3.Selection

/-- An exact root and optional nested-rule name in the pinned elaborated IL. -/
structure RootSelector where
  artifactCid : String
  rootOrdinal : Nat
  rootName : String
  nestedRule : Option String := none
  deriving DecidableEq, Repr

/-- SHA-256 CID of the pinned SpecTec 0.5 elaborated S-expression. -/
def elaboratedArtifactCid : String :=
  "bafkreigdboqqahicaabxsoziya7gxzu4goh7hay66b4p2xs4loiagjoiay"

private def root (ordinal : Nat) (name : String)
    (nestedRule : Option String := none) : RootSelector :=
  ⟨elaboratedArtifactCid, ordinal, name, nestedRule⟩

/-- Direct numeric, state-access, and execution roots used by this slice.

This is deliberately not a transitive dependency closure of the selected IL.
Root and nested-rule names are copied exactly from the pinned S-expression.
-/
def executionRoots : List RootSelector :=
  [ root 425 "iadd_"
  , root 498 "binop_"
  , root 602 "local"
  , root 628 "Step_pure" (some "binop-val")
  , root 628 "Step_pure" (some "frame-vals")
  , root 628 "Step_pure" (some "return-frame")
  , root 630 "Step_read" (some "local.get")
  , root 631 "Step"
  , root 632 "Steps"
  ]

/-- A line range in one exact raw SpecTec source artifact. -/
structure SourceSelector where
  artifactCid : String
  path : String
  startLine : Nat
  endLine : Nat
  name : String
  deriving DecidableEq, Repr

private def scalarCid : String :=
  "bafkreihycbg24hwukd2twmcovbvn6wi43xf4bbkaio7dahyxv2k4ncx424"

private def executionCid : String :=
  "bafkreih26cp72nzar4ytpu32rnzup3tlmwhj56ywnjy23ybxlruh7ukpwy"

/-- Exact raw-source declarations and rules abstracted by this slice. -/
def executionSources : List SourceSelector :=
  [ ⟨scalarCid, "source/3.1-numerics.scalar.spectec", 165, 165, "$iadd_"⟩
  , ⟨scalarCid, "source/3.1-numerics.scalar.spectec", 388, 388,
      "$binop_(Inn, ADD, ...)"⟩
  , ⟨executionCid, "source/4.3-execution.instructions.spectec", 13, 19,
      "Step/pure and Step/read"⟩
  , ⟨executionCid, "source/4.3-execution.instructions.spectec", 212, 213,
      "Step_pure/frame-vals"⟩
  , ⟨executionCid, "source/4.3-execution.instructions.spectec", 215, 216,
      "Step_pure/return-frame"⟩
  , ⟨executionCid, "source/4.3-execution.instructions.spectec", 298, 300,
      "Step_read/local.get"⟩
  , ⟨executionCid, "source/4.3-execution.instructions.spectec", 948, 950,
      "Step_pure/binop-val"⟩
  ]

end Nucleus.Wasm.SpecTec.Wasm3.Selection
