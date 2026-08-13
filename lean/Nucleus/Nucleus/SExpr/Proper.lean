import Nucleus.SExpr.Basic
import Mathlib.Data.List.OfFn

/-!
# Proper S-expressions

The n-ary representation makes properness intrinsic. Its embedding into
`SExpr2` uses a nil-terminated cons spine; the image is exactly the structural
`SExpr2.Proper` predicate.
-/

namespace Nucleus

universe u v

/-- Proper S-expressions: atoms and finite lists. -/
inductive SExpr (Atom : Type u) where
  | atom (value : Atom)
  | list (n : Nat) (children : Fin n → SExpr Atom)

instance : EmptyCollection (SExpr α) := ⟨.list 0 Fin.elim0⟩
instance : Inhabited (SExpr α) := ⟨∅⟩

namespace SExpr

/-- The intrinsic proper empty list. -/
def nil : SExpr α := ∅

def isNil : SExpr α → Bool
  | .list 0 _ => true
  | _ => false

/-- Lisp spelling retained as an alias. -/
abbrev isnil := @isNil

def map (f : α → β) : SExpr α → SExpr β
  | .atom value => .atom (f value)
  | .list n children => .list n fun i => map f (children i)

def bind (expr : SExpr α) (f : α → SExpr β) : SExpr β :=
  match expr with
  | .atom value => f value
  | .list n children => .list n fun i => bind (children i) f

@[simp] theorem bind_pure : ∀ expr : SExpr α, bind expr .atom = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | list n children ih =>
      apply congrArg (SExpr.list n)
      funext i
      exact ih i

theorem bind_assoc (expr : SExpr α) (f : α → SExpr β)
    (g : β → SExpr γ) : bind (bind expr f) g = bind expr fun x => bind (f x) g := by
  induction expr with
  | atom => rfl
  | list n children ih =>
      apply congrArg (SExpr.list n)
      funext i
      exact ih i

instance : Monad SExpr where
  pure := .atom
  bind := bind

instance : LawfulMonad SExpr := LawfulMonad.mk' _
  (fun expr => by change bind expr (fun x => .atom (id x)) = expr; simp)
  (fun _ _ => rfl)
  (fun expr f g => bind_assoc expr f g)

/-- Construct a list expression from an ordinary list of children. -/
def ofList (children : List (SExpr α)) : SExpr α :=
  .list children.length fun i => children[i]

/-- Extract children when the expression is a list. -/
def children? : SExpr α → Option (List (SExpr α))
  | .atom _ => none
  | .list _ children => some (List.ofFn children)

@[simp] theorem children?_ofList (children : List (SExpr α)) :
    children? (ofList children) = some children := by
  simp [children?, ofList]

/-- Proper-list construction is an embedding, not an equivalence with all
proper expressions: atoms form the other summand. -/
theorem ofList_injective : Function.Injective (ofList : List (SExpr α) → SExpr α) := by
  intro a b h
  have := congrArg children? h
  simpa using this

/-- Lists of proper expressions embed as list nodes. -/
def ofListEmbedding (α : Type u) : List (SExpr α) ↪ SExpr α :=
  ⟨ofList, ofList_injective⟩

/-- Embed a list of atoms as a proper list of atom nodes. -/
def ofAtoms (values : List α) : SExpr α := ofList (values.map .atom)

theorem ofAtoms_injective : Function.Injective (ofAtoms : List α → SExpr α) := by
  intro xs ys h
  have hm := ofList_injective h
  exact ((List.map_injective_iff).2 fun _ _ h => SExpr.atom.inj h) hm

def ofAtomsEmbedding (α : Type u) : List α ↪ SExpr α :=
  ⟨ofAtoms, ofAtoms_injective⟩

/-- First child, or `nil` for atoms and the empty list. -/
def car : SExpr α → SExpr α
  | .atom _ => nil
  | .list 0 _ => nil
  | .list (_ + 1) children => children 0

/-- Remaining children as a list expression, or `nil` for atoms. -/
def cdr : SExpr α → SExpr α
  | .atom _ => nil
  | .list _ children => ofList (List.ofFn children).tail

@[simp] theorem car_nil : car (nil : SExpr α) = nil := rfl
@[simp] theorem cdr_nil : cdr (nil : SExpr α) = nil := by
  change SExpr.list 0 _ = SExpr.list 0 Fin.elim0
  apply congrArg (SExpr.list 0)
  funext i
  exact Fin.elim0 i
@[simp] theorem isNil_eq_true (expr : SExpr α) : isNil expr = true ↔ expr = nil := by
  cases expr with
  | atom => simp [isNil, nil]
  | list n children =>
      cases n with
      | zero =>
          constructor
          · intro _
            apply congrArg (SExpr.list 0)
            funext i
            exact Fin.elim0 i
          · intro _; rfl
      | succ n =>
          constructor
          · intro h; cases h
          · intro h; injection h with hlen; omega

/-- The actual one-layer destructor equivalence. -/
def equivAtomOrList (α : Type u) : SExpr α ≃ α ⊕ List (SExpr α) where
  toFun
    | .atom value => .inl value
    | .list _ children => .inr (List.ofFn children)
  invFun
    | .inl value => .atom value
    | .inr children => ofList children
  left_inv expr := by
    cases expr with
    | atom => rfl
    | list n children =>
        change SExpr.list (List.ofFn children).length
          (List.get (List.ofFn children)) = .list n children
        have hlen : (List.ofFn children).length = n := by simp
        have hchildren : List.get (List.ofFn children) ≍ children :=
          (Fin.heq_fun_iff hlen).2 (by intro i; simp)
        let a : Σ n, Fin n → SExpr α := ⟨(List.ofFn children).length,
          List.get (List.ofFn children)⟩
        let b : Σ n, Fin n → SExpr α := ⟨n, children⟩
        have hab : a = b := Sigma.ext hlen hchildren
        exact congrArg (fun p : Σ n, Fin n → SExpr α => SExpr.list p.1 p.2)
          hab
  right_inv value := by cases value <;> simp [ofList]

/-- Embed proper expressions into the dotted representation. -/
def toSExpr2 : SExpr α → SExpr2 α
  | .atom value => .atom value
  | .list _ children => SExpr2.ofList (List.ofFn fun i => toSExpr2 (children i))

private theorem ofList2_injective :
    Function.Injective (SExpr2.ofList : List (SExpr2 α) → SExpr2 α) := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> cases h; rfl
  | cons head tail ih =>
      intro b h
      cases b with
      | nil => cases h
      | cons head' tail' =>
          injection h with hh ht
          exact congrArg₂ List.cons hh (ih ht)

/-- The proper-to-dotted embedding loses no information. -/
theorem toSExpr2_injective : Function.Injective (toSExpr2 : SExpr α → SExpr2 α) := by
  intro a
  induction a with
  | atom value =>
      intro b h
      cases b with
      | atom value' => injection h with hv; exact congrArg SExpr.atom hv
      | list n children =>
          cases n with
          | zero => simp [toSExpr2, SExpr2.ofList] at h
          | succ n => simp [toSExpr2, SExpr2.ofList] at h
  | list n children ih =>
      intro b h
      cases b with
      | atom value =>
          cases n with
          | zero => simp [toSExpr2, SExpr2.ofList] at h
          | succ n => simp [toSExpr2, SExpr2.ofList] at h
      | list m children' =>
          have hl := ofList2_injective h
          have hlen : n = m := by simpa using congrArg List.length hl
          subst m
          apply congrArg (SExpr.list n)
          funext i
          apply ih i
          simpa using congrArg (fun xs => xs[i.1]?) hl

theorem toSExpr2_proper : ∀ expr : SExpr α, SExpr2.IsProper expr.toSExpr2 := by
  intro expr
  induction expr with
  | atom value => exact Or.inl (.atom value)
  | list n children ih =>
      exact Or.inr (SExpr2.properList_ofList fun child hchild => by
        obtain ⟨i, -, rfl⟩ := List.mem_ofFn.mp hchild
        exact ih i)

private theorem proper_has_preimage_indexed {kind : SExpr2.ProperKind}
    {value : SExpr2 α} (h : SExpr2.Proper kind value) :
    match kind with
    | .atom => ∃ expr : SExpr α, toSExpr2 expr = value
    | .list => ∃ xs : List (SExpr α), SExpr2.ofList (xs.map toSExpr2) = value := by
  induction h with
  | atom value => exact ⟨.atom value, rfl⟩
  | nil => exact ⟨[], rfl⟩
  | @cons car cdr carKind hcar htail ihCar ihTail =>
      cases carKind with
      | atom =>
          obtain ⟨car, hcarEq⟩ := ihCar
          obtain ⟨tail, htailEq⟩ := ihTail
          exact ⟨car :: tail, by simp [SExpr2.ofList, hcarEq, htailEq]⟩
      | list =>
          obtain ⟨carChildren, hcarEq⟩ := ihCar
          obtain ⟨tail, htailEq⟩ := ihTail
          let carExpr := ofList carChildren
          have hcar' : toSExpr2 carExpr = car := by
            change SExpr2.ofList (List.ofFn (toSExpr2 ∘ List.get carChildren)) = _
            rw [← hcarEq]
            apply congrArg SExpr2.ofList
            exact List.ofFn_getElem_eq_map carChildren toSExpr2
          exact ⟨carExpr :: tail, by simp [SExpr2.ofList, hcar', htailEq]⟩

private theorem proper_has_preimage {value : SExpr2 α}
    (h : SExpr2.IsProper value) : ∃ expr, toSExpr2 expr = value := by
  rcases h with hatom | hlist
  · exact proper_has_preimage_indexed hatom
  · obtain ⟨children, hchildren⟩ := proper_has_preimage_indexed hlist
    refine ⟨ofList children, ?_⟩
    change SExpr2.ofList (List.ofFn (toSExpr2 ∘ List.get children)) = _
    rw [← hchildren]
    apply congrArg SExpr2.ofList
    exact List.ofFn_getElem_eq_map children toSExpr2

/-- The structural properness predicate is precisely the image of `SExpr`. -/
theorem proper_iff_exists (value : SExpr2 α) :
    SExpr2.IsProper value ↔ ∃ expr : SExpr α, expr.toSExpr2 = value := by
  constructor
  · exact proper_has_preimage
  · rintro ⟨expr, rfl⟩
    exact toSExpr2_proper expr

/-- Proper dotted expressions are isomorphic to intrinsically proper ones. -/
noncomputable def equivProperSubtype (α : Type u) :
    SExpr α ≃ {value : SExpr2 α // SExpr2.IsProper value} where
  toFun expr := ⟨expr.toSExpr2, toSExpr2_proper expr⟩
  invFun value := Classical.choose (proper_has_preimage value.property)
  left_inv expr := toSExpr2_injective (Classical.choose_spec
    (proper_has_preimage (toSExpr2_proper expr)))
  right_inv value := Subtype.ext (Classical.choose_spec (proper_has_preimage value.property))

/-- Embedding commutes with monadic substitution. -/
theorem toSExpr2_bind (expr : SExpr α) (f : α → SExpr β) :
    toSExpr2 (bind expr f) = SExpr2.bind expr.toSExpr2 (toSExpr2 ∘ f) := by
  induction expr with
  | atom => rfl
  | list n children ih =>
      simp only [bind, toSExpr2]
      rw [SExpr2.bind_ofList]
      rw [List.map_ofFn]
      congr 2
      funext i
      exact ih i

end SExpr
end Nucleus
