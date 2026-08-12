import Nucleus.Json.CasMap
import Nucleus.Json.Ipld
import Nucleus.Json.RfcParser

/-!
# A serialized IPLD JSON store

This module closes the loop between storage, parsing, slash-link recognition,
and gas-bounded dereferencing. Store blocks are RFC JSON texts. Fetching parses
a block into integer-only IPLD, recognizes singleton `{ "/": "name" }` objects
as links, and recursively resolves those links through the same store.

Malformed RFC JSON, non-`Int64` numbers, invalid names, missing blocks, and gas
exhaustion all mean `Unknown.unknown`: they reveal no result, but are not confused
with the known JSON value `null`.
-/

namespace Nucleus

universe u

/-- A finite map from content names to serialized RFC JSON blocks. -/
structure IpldJsonStore (Name : Type) where
  names : Finset Name
  blocks : {name // name ∈ names} → String

namespace IpldJsonStore

variable {Name : Type} [DecidableEq Name]

/-- Look up a serialized block. -/
def get? (store : IpldJsonStore Name) (name : Name) : Unknown String :=
  if h : name ∈ store.names then .known (store.blocks ⟨name, h⟩) else .unknown

/-- Translate the linked IPLD scalar vocabulary into the generic CAS link
vocabulary used by `JsonCas.derefWith`. -/
def scalarToLink : IpldLinkedScalar Name → Link IpldJsonScalar Name
  | .value value => .inl value
  | .link name => .inr name

/-- Parse one serialized block and expose its slash-object links as generic CAS
links. Parsing/profile/name failures are epistemic unknown. -/
noncomputable def parseBlock (parseName : String → Option Name) (text : String) :
    Unknown (Json (Link IpldJsonScalar Name)) :=
  match RfcJson.parse? text with
  | none => .unknown
  | some rfc =>
      match IpldLinkedJson.ofRfc? parseName rfc with
      | none => .unknown
      | some linked => .known (linked.mapScalar scalarToLink)

/-- Interpret a serialized block using a resolver for its parsed links. -/
noncomputable def interpretBlock (parseName : String → Option Name)
    (resolve : Name → Unknown IpldJson) (text : String) : Unknown IpldJson :=
  (parseBlock parseName text).bind (JsonCas.derefWith resolve)

/-- Parse and recursively dereference a named IPLD block. Each followed block
consumes one unit of gas. -/
noncomputable def fetch (store : IpldJsonStore Name) (parseName : String → Option Name) :
    Nat → Name → Unknown IpldJson
  | 0, _ => .unknown
  | gas + 1, name =>
      (store.get? name).bind (interpretBlock parseName (store.fetch parseName gas))

/-- The name-indexed IPLD view induced at a fixed gas level. -/
noncomputable def dereference (store : IpldJsonStore Name)
    (parseName : String → Option Name) (gas : Nat) : Name → Unknown IpldJson :=
  store.fetch parseName gas

@[simp] theorem fetch_zero (store : IpldJsonStore Name)
    (parseName : String → Option Name) (name : Name) :
    store.fetch parseName 0 name = .unknown := rfl

theorem fetch_succ_of_known {store : IpldJsonStore Name}
    {parseName : String → Option Name} {gas : Nat} {name : Name}
    {text : String} (hlookup : store.get? name = .known text) :
    store.fetch parseName (gas + 1) name =
      interpretBlock parseName (store.fetch parseName gas) text := by
  simp [fetch, hlookup, Unknown.bind]

theorem fetch_succ_of_missing {store : IpldJsonStore Name}
    {parseName : String → Option Name} {gas : Nat} {name : Name}
    (hlookup : store.get? name = .unknown) :
    store.fetch parseName (gas + 1) name = .unknown := by
  simp [fetch, hlookup, Unknown.bind]

omit [DecidableEq Name] in
theorem interpretBlock_of_parsed {parseName : String → Option Name}
    {resolve : Name → Unknown IpldJson} {text : String}
    {parsed : Json (Link IpldJsonScalar Name)}
    (hparse : parseBlock parseName text = .known parsed) :
    interpretBlock parseName resolve text = JsonCas.derefWith resolve parsed := by
  simp [interpretBlock, hparse, Unknown.bind]

omit [DecidableEq Name] in
theorem interpretBlock_of_invalid {parseName : String → Option Name}
    {resolve : Name → Unknown IpldJson} {text : String}
    (hparse : parseBlock parseName text = .unknown) :
    interpretBlock parseName resolve text = .unknown := by
  simp [interpretBlock, hparse, Unknown.bind]

omit [DecidableEq Name] in
/-- A parsed link-free IPLD tree resolves to itself under every resolver. -/
theorem derefWith_values (resolve : Name → Unknown IpldJson) :
    ∀ j : IpldJson,
      JsonCas.derefWith resolve (j.mapScalar Sum.inl) = .known j := by
  intro j
  induction j with
  | scalar value => rfl
  | list n elems ih =>
      simp only [Json.mapScalar, JsonCas.derefWith]
      rw [dif_pos fun i => by simp [ih i, Unknown.isKnown]]
      congr 2
      funext i
      apply Unknown.get_eq_get_of_le (Or.inr (ih i))
      rfl
  | map keys vals ih =>
      simp only [Json.mapScalar, JsonCas.derefWith]
      rw [dif_pos fun k => by simp [ih k, Unknown.isKnown]]
      congr 2
      funext k
      apply Unknown.get_eq_get_of_le (Or.inr (ih k))
      rfl

/-- End-to-end two-block behavior: a parsed slash link in one serialized block
is followed to a second parsed block when two units of gas are available. -/
theorem fetch_two_block_link {store : IpldJsonStore Name}
    {parseName : String → Option Name} {root child : Name}
    {rootText childText : String} {childJson : IpldJson}
    (hrootLookup : store.get? root = .known rootText)
    (hrootParse : parseBlock parseName rootText = .known (.scalar (.inr child)))
    (hchildLookup : store.get? child = .known childText)
    (hchildParse : parseBlock parseName childText = .known
      (childJson.mapScalar Sum.inl)) :
    store.fetch parseName 2 root = .known childJson := by
  rw [show 2 = 1 + 1 by omega, fetch_succ_of_known hrootLookup,
    interpretBlock_of_parsed hrootParse]
  simp only [JsonCas.derefWith]
  rw [show 1 = 0 + 1 by omega, fetch_succ_of_known hchildLookup,
    interpretBlock_of_parsed hchildParse]
  exact derefWith_values _ childJson

/-- Store extension in the flat information order. Existing serialized blocks
cannot change, while missing blocks may become known. -/
def InformationLe (a b : IpldJsonStore Name) : Prop :=
  ∀ name, Unknown.Le (a.get? name) (b.get? name)

instance : LE (IpldJsonStore Name) := ⟨InformationLe⟩

theorem informationLe_def {a b : IpldJsonStore Name} :
    a ≤ b ↔ ∀ name, Unknown.Le (a.get? name) (b.get? name) := Iff.rfl

/-- Serialized stores are determined extensionally by lookup. -/
theorem ext_get? {a b : IpldJsonStore Name}
    (h : ∀ name, a.get? name = b.get? name) : a = b := by
  have hnames : a.names = b.names := Finset.ext fun name => by
    constructor
    · intro ha
      by_contra hb
      simpa [get?, ha, hb] using h name
    · intro hb
      by_contra ha
      simpa [get?, ha, hb] using h name
  cases a with
  | mk namesA blocksA =>
      cases b with
      | mk namesB blocksB =>
          simp only at hnames
          subst namesB
          congr 1
          funext name
          have heq := h name.1
          simpa [get?, name.2] using heq

instance : PartialOrder (IpldJsonStore Name) where
  le_refl _ _ := Unknown.le_refl _
  le_trans _ _ _ hab hbc name := Unknown.le_trans (hab name) (hbc name)
  le_antisymm a b hab hba := ext_get? fun name =>
    Unknown.le_antisymm (hab name) (hba name)

omit [DecidableEq Name] in
theorem interpretBlock_mono (parseName : String → Option Name)
    {resolve₁ resolve₂ : Name → Unknown IpldJson}
    (hresolve : ∀ name, Unknown.Le (resolve₁ name) (resolve₂ name)) (text : String) :
    Unknown.Le (interpretBlock parseName resolve₁ text)
      (interpretBlock parseName resolve₂ text) :=
  Unknown.bind_mono (Unknown.le_refl _) fun parsed =>
    JsonCas.derefWith_mono hresolve parsed

/-- Parsed IPLD fetching is monotone under store extension. -/
theorem fetch_mono {a b : IpldJsonStore Name} (hab : a ≤ b)
    (parseName : String → Option Name) :
    ∀ gas name, Unknown.Le (a.fetch parseName gas name) (b.fetch parseName gas name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      simp only [fetch]
      exact Unknown.bind_mono (hab name)
        (interpretBlock_mono parseName ih)

/-- Therefore the induced name-indexed functions are pointwise monotone. -/
theorem dereference_mono {a b : IpldJsonStore Name} (hab : a ≤ b)
    (parseName : String → Option Name) (gas : Nat) :
    ∀ name, Unknown.Le (a.dereference parseName gas name)
      (b.dereference parseName gas name) :=
  fetch_mono hab parseName gas

/-- More gas can only reveal more parsed IPLD information. -/
theorem fetch_succ_mono (store : IpldJsonStore Name)
    (parseName : String → Option Name) :
    ∀ gas name, Unknown.Le (store.fetch parseName gas name)
      (store.fetch parseName (gas + 1) name) := by
  intro gas
  induction gas with
  | zero => intro name; exact Unknown.unknown_le _
  | succ gas ih =>
      intro name
      simp only [fetch]
      exact Unknown.bind_mono (Unknown.le_refl _)
        (interpretBlock_mono parseName ih)

/-- Parsed IPLD fetching is monotone in gas. -/
theorem fetch_gas_mono (store : IpldJsonStore Name)
    (parseName : String → Option Name) {gas₁ gas₂ : Nat}
    (hgas : gas₁ ≤ gas₂) (name : Name) :
    Unknown.Le (store.fetch parseName gas₁ name) (store.fetch parseName gas₂ name) := by
  induction gas₂, hgas using Nat.le_induction with
  | base => exact Unknown.le_refl _
  | succ gas₂ _ ih =>
      exact Unknown.le_trans ih (fetch_succ_mono store parseName gas₂ name)

/-- A parsed slash link from `parent` to `child`. -/
def DependsOn (store : IpldJsonStore Name) (parseName : String → Option Name)
    (child parent : Name) : Prop :=
  ∃ text parsed, store.get? parent = .known text ∧
    parseBlock parseName text = .known parsed ∧ Sum.inr child ∈ parsed.scalars

/-- A serialized IPLD store with a rank decreasing along every successfully
parsed slash link. Invalid blocks have no dependency edges. -/
structure Acyclic (Name : Type) [DecidableEq Name] extends IpldJsonStore Name where
  parseName : String → Option Name
  rank : Name → Nat
  decreases : ∀ {child parent},
    toIpldJsonStore.DependsOn parseName child parent → rank child < rank parent

namespace Acyclic

variable (store : Acyclic Name)

/-- A finite acyclic serialized IPLD store has a maximum link depth. -/
theorem exists_maximumDereferenceDepth :
    ∃ depth, ∀ name ∈ store.names, store.rank name < depth := by
  refine ⟨store.names.sup store.rank + 1, ?_⟩
  intro name hname
  exact Nat.lt_succ_of_le (Finset.le_sup (f := store.rank) hname)

/-- Once gas exceeds a name's rank, parsing and link resolution have stabilized. -/
theorem fetch_stable_of_rank : ∀ name gas extra,
    store.rank name < gas →
    store.toIpldJsonStore.fetch store.parseName gas name =
      store.toIpldJsonStore.fetch store.parseName (gas + extra) name := by
  intro name
  induction hrank : store.rank name using Nat.strong_induction_on generalizing name with
  | h _rank ih =>
      intro gas extra hgas
      subst hrank
      cases gas with
      | zero => omega
      | succ fuel =>
          rw [Nat.succ_add]
          simp only [fetch]
          cases hlookup : store.toIpldJsonStore.get? name with
          | unknown => simp [Unknown.bind]
          | known text =>
              simp only [Unknown.bind]
              unfold interpretBlock
              cases hparse : parseBlock store.parseName text with
              | unknown => simp [Unknown.bind]
              | known parsed =>
                  simp only [Unknown.bind]
                  apply JsonCas.derefWith_congr
                  intro child hchild
                  have hdep : store.toIpldJsonStore.DependsOn store.parseName child name :=
                    ⟨text, parsed, hlookup, hparse, hchild⟩
                  have hdecrease : store.rank child < store.rank name :=
                    store.decreases hdep
                  have hchildFuel : store.rank child < fuel := by omega
                  simpa [Nat.succ_add] using
                    ih (store.rank child) hdecrease child rfl fuel extra hchildFuel

/-- The maximum rank is a global gas level after which the complete IPLD view
is stable for every name, including missing and invalid blocks. -/
theorem dereference_stable_at_maximum :
    ∃ depth, ∀ extra name,
      store.toIpldJsonStore.dereference store.parseName depth name =
        store.toIpldJsonStore.dereference store.parseName (depth + extra) name := by
  refine ⟨store.names.sup store.rank + 1, ?_⟩
  intro extra name
  by_cases hname : name ∈ store.names
  · apply fetch_stable_of_rank store
    exact Nat.lt_succ_of_le (Finset.le_sup (f := store.rank) hname)
  · rw [Nat.succ_add]
    simp [dereference, fetch, get?, hname, Unknown.bind]

end Acyclic

end IpldJsonStore

end Nucleus
