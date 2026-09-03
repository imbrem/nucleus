import Nucleus.Classical.Packed.Block

/-!
# Reference-counted live blocks

Live headers carry constructor, size class, and reference count. References
carry sign and aligned address; literals remain immediate. Mutation is
copy-on-write and count overflow is rejected.

Header-format validity is local: a header containing the maximum count is a
valid 32-bit header. Whole-store validity permits a conservative overcount,
which can leak but cannot reclaim live storage; undercounts are rejected. The
size class is retained because a zero tail has
no local boundary marker; capacity lookup must not scan neighboring storage.
-/

namespace Nucleus.Classical.Tagged.Runtime.Shared

universe u
variable {State : Type u}

def classBits : Nat := 5
def classLimit : Nat := 30
def refcountShift : Nat := 7
def refcountLimit : Nat := 2 ^ 25
def refcountMax : Nat := refcountLimit - 1

inductive Constructor where
  | and | or | sat
  deriving DecidableEq, Repr

def Constructor.code : Constructor → Nat
  | .and => 0
  | .or => 1
  | .sat => 2

structure Header where
  constructor : Constructor
  sizeClass : Nat
  refcount : Nat
  classBound : sizeClass < classLimit
  countPositive : 0 < refcount
  countBound : refcount < refcountLimit

def Header.raw (header : Header) : Nat :=
  header.refcount * 2 ^ refcountShift + header.sizeClass * 4 +
    header.constructor.code

theorem Constructor.code_lt_four (constructor : Constructor) :
    constructor.code < 4 := by cases constructor <;> decide

theorem Header.tag (header : Header) :
    header.raw % 4 = header.constructor.code := by
  unfold Header.raw refcountShift
  have bound := Constructor.code_lt_four header.constructor
  omega

theorem Header.decodeClass (header : Header) :
    (header.raw / 4) % 2 ^ classBits = header.sizeClass := by
  have classBound : header.sizeClass < 30 := by
    simpa [classLimit] using header.classBound
  simp only [Header.raw, refcountShift, classBits]
  have bound := Constructor.code_lt_four header.constructor
  omega

theorem Header.decodeRefcount (header : Header) :
    header.raw / 2 ^ refcountShift = header.refcount := by
  have classBound : header.sizeClass < 30 := by
    simpa [classLimit] using header.classBound
  simp only [Header.raw, refcountShift]
  have bound := Constructor.code_lt_four header.constructor
  omega

theorem Header.fitsWord (header : Header) : header.raw < 2 ^ 32 := by
  have classBound : header.sizeClass < 30 := by
    simpa [classLimit] using header.classBound
  have countBound : header.refcount < 2 ^ 25 := by
    simpa [refcountLimit] using header.countBound
  simp only [Header.raw, refcountShift]
  have bound := Constructor.code_lt_four header.constructor
  omega

/-- Capacity is available from the local header without scanning its tail. -/
def Header.capacity (header : Header) : Nat := 4 * 2 ^ header.sizeClass

theorem Header.nextClassDoubles (constructor : Constructor) (sizeClass count : Nat)
    (classBound : sizeClass + 1 < classLimit) (countPositive : 0 < count)
    (countBound : count < refcountLimit) :
    (Header.mk constructor (sizeClass + 1) count classBound countPositive countBound).capacity =
      2 * (Header.mk constructor sizeClass count (by omega)
        countPositive countBound).capacity := by
  simp [Header.capacity, pow_succ]
  omega

/-- The all-ones count field is locally well-formed. -/
def maxHeader (constructor : Constructor) (sizeClass : Nat)
    (classBound : sizeClass < classLimit) : Header where
  constructor := constructor
  sizeClass := sizeClass
  refcount := refcountMax
  classBound := classBound
  countPositive := by simp [refcountMax, refcountLimit]
  countBound := by simp [refcountMax, refcountLimit]

theorem maxHeader_count (constructor : Constructor) (sizeClass : Nat)
    (classBound : sizeClass < classLimit) :
    (maxHeader constructor sizeClass classBound).refcount = refcountMax := rfl

inductive ReferenceKind where
  | block
  | literal
  deriving DecidableEq, Repr

/-- Tags `01` and `10` are invalid in reference positions. -/
def referenceKind? (raw : Nat) : Option ReferenceKind :=
  match raw % 4 with
  | 0 => if raw % (2 ^ 31) = 0 then none else some .block
  | 3 => some .literal
  | _ => none

theorem referenceKind?_rejects_tag_one {raw : Nat} (tag : raw % 4 = 1) :
    referenceKind? raw = none := by simp [referenceKind?, tag]

theorem referenceKind?_rejects_tag_two {raw : Nat} (tag : raw % 4 = 2) :
    referenceKind? raw = none := by simp [referenceKind?, tag]

theorem referenceKind?_block_nonzero {raw : Nat}
    (decoded : referenceKind? raw = some .block) : raw % (2 ^ 31) ≠ 0 := by
  unfold referenceKind? at decoded
  split at decoded <;> try contradiction
  split at decoded <;> simp_all

inductive Reference where
  | literal (atom : Nat) (negative : Bool)
  | block (address : Nat) (negative : Bool)
  deriving DecidableEq, Repr

structure Node where
  header : Header
  children : List Reference

structure Store where
  roots : List Reference
  nodes : List (Nat × Node)

def Reference.address? : Reference → Option Nat
  | .literal _ _ => none
  | .block address _ => some address

def Store.references (store : Store) : List Reference :=
  store.roots ++ store.nodes.flatMap fun entry ↦ entry.2.children

def Store.incoming (store : Store) (address : Nat) : Nat :=
  store.references.countP fun reference ↦ reference.address? = some address

def Store.Edge (store : Store) (parent child : Nat) : Prop :=
  ∃ node negative, (parent, node) ∈ store.nodes ∧
    Reference.block child negative ∈ node.children

def Store.RootAddress (store : Store) (address : Nat) : Prop :=
  ∃ negative, Reference.block address negative ∈ store.roots

inductive Store.Reachable (store : Store) : Nat → Prop
  | root {address} : store.RootAddress address → store.Reachable address
  | child {parent address} : store.Reachable parent → store.Edge parent address →
      store.Reachable address

/-- Every live address is unique, every reference resolves, and the stored
count covers all incoming roots and child edges. -/
structure Store.Valid (store : Store) : Prop where
  addressesUnique : store.nodes.map Prod.fst |>.Nodup
  referencesResolve : ∀ reference ∈ store.references,
    ∀ address, reference.address? = some address →
      ∃ node, (address, node) ∈ store.nodes
  countsEnough : ∀ address node, (address, node) ∈ store.nodes →
    store.incoming address ≤ node.header.refcount
  reachableAcyclic : ∃ rank : Nat → Nat, ∀ parent child,
    store.Reachable parent → store.Edge parent child →
      rank child < rank parent

theorem Store.Valid.refcountPositive {store : Store} (_valid : store.Valid)
    {address : Nat} {node : Node} (_member : (address, node) ∈ store.nodes) :
    0 < node.header.refcount := by
  exact node.header.countPositive

def CountValid (incoming : Nat) (header : Header) : Prop :=
  incoming ≤ header.refcount

theorem maxHeader_validWithOneEdge (constructor : Constructor) (sizeClass : Nat)
    (classBound : sizeClass < classLimit) :
    CountValid 1 (maxHeader constructor sizeClass classBound) := by
  simp [CountValid, maxHeader, refcountMax, refcountLimit]

/-- Allocated storage distinguishes reachable nodes from conservative garbage.
Garbage is allocator-ineligible. -/
structure StoragePartition where
  reachable : List Nat
  garbage : List Nat
  free : List Nat
  reachableGarbage : reachable.Disjoint garbage
  reachableFree : reachable.Disjoint free
  garbageFree : garbage.Disjoint free

def increment? (count : Nat) : Option Nat :=
  if count + 1 < refcountLimit then some (count + 1) else none

theorem increment?_result {count next : Nat} (ran : increment? count = some next) :
    next = count + 1 ∧ next < refcountLimit := by
  unfold increment? at ran
  split at ran <;> simp_all

theorem increment?_rejectsOverflow {count : Nat}
    (full : refcountLimit ≤ count + 1) : increment? count = none := by
  simp [increment?, Nat.not_lt.mpr full]

theorem increment?_rejectsMax : increment? refcountMax = none := by
  simp [increment?, refcountMax, refcountLimit]

def preflight (counts : List Nat) : Bool :=
  counts.all fun count ↦ count + 1 < refcountLimit

theorem preflight_eq_true {counts : List Nat} : preflight counts = true ↔
    ∀ count ∈ counts, ∃ next, increment? count = some next := by
  simp [preflight, increment?]

/-- One entry per target after duplicate references have been aggregated. -/
structure Demand where
  current : Nat
  required : Nat
  deriving DecidableEq, Repr

def Demand.accepts (demand : Demand) : Bool :=
  demand.current + demand.required < refcountLimit

def aggregatePreflight (demands : List Demand) : Bool :=
  demands.all Demand.accepts

theorem aggregatePreflight_eq_true {demands : List Demand} :
    aggregatePreflight demands = true ↔
      ∀ demand ∈ demands,
        demand.current + demand.required < refcountLimit := by
  simp [aggregatePreflight, Demand.accepts]

/-- Two references to the same child consume two count units. -/
theorem duplicateDemand (current : Nat) :
    Demand.accepts ⟨current, 2⟩ =
      decide (current + 2 < refcountLimit) := rfl

structure CloneArena where
  demands : List Demand
  root : Nat
  deriving DecidableEq, Repr

def cloneCandidate? (arena : CloneArena) : Option CloneArena := do
  if aggregatePreflight arena.demands then pure () else none
  let incremented := arena.demands.map fun demand ↦
    { demand with current := demand.current + demand.required, required := 0 }
  some { arena with demands := incremented, root := arena.root + 1 }

/-- All child increments are checked before a clone candidate is produced. -/
theorem cloneCandidate?_preflight {before after : CloneArena}
    (cloned : cloneCandidate? before = some after) :
    aggregatePreflight before.demands = true := by
  unfold cloneCandidate? at cloned
  split at cloned
  · assumption
  · contradiction

/-- Failed clone construction commits no partial count or root update. -/
def cloneCommit (arena : CloneArena) : CloneArena :=
  (cloneCandidate? arena).getD arena

theorem cloneCommit_failure {arena : CloneArena}
    (failed : cloneCandidate? arena = none) : cloneCommit arena = arena := by
  simp [cloneCommit, failed]

theorem maxChildClone_rejected (tail : List Demand) (root : Nat) :
    cloneCandidate? ⟨⟨refcountMax, 1⟩ :: tail, root⟩ = none := by
  simp [cloneCandidate?, aggregatePreflight, Demand.accepts,
    refcountMax, refcountLimit]

theorem maxChildClone_unchanged (tail : List Demand) (root : Nat) :
    cloneCommit ⟨⟨refcountMax, 1⟩ :: tail, root⟩ =
      ⟨⟨refcountMax, 1⟩ :: tail, root⟩ := by
  exact cloneCommit_failure (maxChildClone_rejected tail root)

structure MachineArena where
  words : List Nat
  freeRoot : Nat
  roots : List (Nat × Nat)
  clone : CloneArena
  deriving DecidableEq, Repr

def cloneMachine (arena : MachineArena) : MachineArena :=
  match cloneCandidate? arena.clone with
  | none => arena
  | some cloned => { arena with clone := cloned }

/-- Rejected aggregate preflight preserves bytes and both root structures. -/
theorem cloneMachine_rejected {arena : MachineArena}
    (rejected : cloneCandidate? arena.clone = none) :
    cloneMachine arena = arena := by
  simp [cloneMachine, rejected]

theorem cloneMachine_maxChild_unchanged (words : List Nat) (freeRoot : Nat)
    (roots : List (Nat × Nat)) (tail : List Demand) (root : Nat) :
    cloneMachine ⟨words, freeRoot, roots,
      ⟨⟨refcountMax, 1⟩ :: tail, root⟩⟩ =
    ⟨words, freeRoot, roots, ⟨⟨refcountMax, 1⟩ :: tail, root⟩⟩ := by
  exact cloneMachine_rejected (maxChildClone_rejected tail root)

/-- Logical view of the intrusive root. `largestRing` includes `root`; the
directory contains representatives for smaller classes. -/
structure FreeDirectory where
  root : Nat
  rootClass : Nat
  directory : Nat → Option Nat
  smallerRings : Nat → List Nat
  largestRing : List Nat

/-- Promote a freed block above the current largest class. The former largest
ring is not rewired; its old root becomes the new directory representative. -/
def FreeDirectory.promote (state : FreeDirectory) (newRoot newClass : Nat) :
    FreeDirectory where
  root := newRoot
  rootClass := newClass
  directory := fun sizeClass ↦
    if sizeClass = state.rootClass then some state.root
    else if sizeClass < state.rootClass then state.directory sizeClass else none
  smallerRings := fun sizeClass ↦
    if sizeClass = state.rootClass then state.largestRing
    else if sizeClass < state.rootClass then state.smallerRings sizeClass else []
  largestRing := [newRoot]

theorem FreeDirectory.promote_oldLargestHead (state : FreeDirectory)
    (newRoot newClass : Nat) :
    (state.promote newRoot newClass).directory state.rootClass = some state.root := by
  simp [FreeDirectory.promote]

theorem FreeDirectory.promote_preservesSmaller (state : FreeDirectory)
    (newRoot newClass sizeClass : Nat) (smaller : sizeClass < state.rootClass) :
    (state.promote newRoot newClass).directory sizeClass = state.directory sizeClass := by
  simp [FreeDirectory.promote, Nat.ne_of_lt smaller, smaller]

/-- Promotion preserves every member of a multi-node former largest ring;
only its representative moves into the new root directory. -/
theorem FreeDirectory.promote_preservesOldRingMembers (state : FreeDirectory)
    {member newRoot newClass : Nat} (inRing : member ∈ state.largestRing) :
    member ∈ (state.promote newRoot newClass).smallerRings state.rootClass := by
  simpa [FreeDirectory.promote] using inRing

/-- The Boolean result says that the last reference was removed. -/
def decrement? (count : Nat) : Option (Nat × Bool) :=
  if count = 0 then none else some (count - 1, count = 1)

theorem decrement?_result {count next : Nat} {reclaim : Bool}
    (ran : decrement? count = some (next, reclaim)) :
    0 < count ∧ next = count - 1 ∧ (reclaim = true ↔ count = 1) := by
  by_cases zero : count = 0
  · simp [decrement?, zero] at ran
  · have equal : (count - 1, decide (count = 1)) = (next, reclaim) := by
      exact Option.some.inj (by simpa [decrement?, zero] using ran)
    cases equal
    constructor
    · omega
    constructor
    · rfl
    · simp

/-- A conservative overcount does not reclaim the block when its sole actual
incoming edge is removed. It may leak until compaction, but cannot free live
storage. -/
theorem overcount_doesNotReclaim {stored : Nat} (overcount : 1 < stored) :
    ∃ next, decrement? stored = some (next, false) := by
  refine ⟨stored - 1, ?_⟩
  simp [decrement?, Nat.ne_of_gt (by omega : 0 < stored), Nat.ne_of_gt overcount]

/-- Once the last real edge disappears, an overcount remains allocated as
garbage and cannot enter a free ring. -/
theorem decrementedOvercount_remainsAllocated {stored next : Nat}
    (overcount : 1 < stored)
    (decremented : decrement? stored = some (next, false)) : 0 < next := by
  have result := decrement?_result decremented
  omega

inductive CowAction where
  | inPlace
  | copy
  deriving DecidableEq, Repr

def cow? (count : Nat) : Option CowAction :=
  if count = 0 ∨ refcountLimit ≤ count then none
  else if count = 1 then some .inPlace else some .copy

theorem cow?_inPlace_iff {count : Nat} :
    cow? count = some .inPlace ↔ count = 1 := by
  unfold cow?
  by_cases one : count = 1
  · subst count; simp [refcountLimit]
  · by_cases invalid : count = 0 ∨ refcountLimit ≤ count <;> simp [one, invalid]

theorem cow?_copy_iff {count : Nat} :
    cow? count = some .copy ↔ 1 < count ∧ count < refcountLimit := by
  unfold cow?
  by_cases zero : count = 0
  · simp [zero]
  · by_cases full : refcountLimit ≤ count
    · simp [zero, full]
    · have positive : 0 < count := Nat.pos_of_ne_zero zero
      by_cases one : count = 1 <;> simp [zero, full, one]
      omega

/-- Growth moves an array to the next size class. -/
def growClass (sizeClass : Nat) : Nat := sizeClass + 1

theorem growClass_doubles (base sizeClass : Nat) :
    Nucleus.Classical.Packed.Block.capacity ⟨base, growClass sizeClass⟩ =
      2 * Nucleus.Classical.Packed.Block.capacity ⟨base, sizeClass⟩ := by
  simp [growClass, Nucleus.Classical.Packed.Block.capacity, pow_succ]
  omega

/-- Commit exposes a candidate only after its complete postcheck succeeds. -/
def commit (accept : State → Bool) (before candidate : State) : State :=
  if accept candidate then candidate else before

theorem commit_rejected {accept : State → Bool} {before candidate : State}
    (rejected : accept candidate = false) :
    commit accept before candidate = before := by
  simp [commit, rejected]

theorem commit_accepted {accept : State → Bool} {before candidate : State}
    (accepted : accept candidate = true) :
    commit accept before candidate = candidate := by
  simp [commit, accepted]

end Nucleus.Classical.Tagged.Runtime.Shared
