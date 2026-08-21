import Nucleus.Hash.Basic
import Nucleus.Probability.FiniteUniform

/-! # Probability distributions on fixed-width hashes -/

namespace Nucleus

structure HashPMF (width : Nat) where
  pmf : PMF (Hash width)

namespace HashPMF

variable {width prefixWidth : Nat}

instance : Coe (HashPMF width) (PMF (Hash width)) := ⟨HashPMF.pmf⟩

instance : CoeFun (HashPMF width) fun _ => Hash width → ENNReal :=
  ⟨fun distribution => distribution.pmf⟩

@[ext] theorem ext {left right : HashPMF width} (equal : left.pmf = right.pmf) :
    left = right := by
  cases left
  cases right
  simp_all

structure HashEMF (width : Nat) extends HashPMF width where
  values : Finset (Hash width)
  nonempty : values.Nonempty
  pmf_eq : pmf = PMF.uniformOfFinset values nonempty

instance : Coe (HashEMF width) (HashPMF width) := ⟨HashEMF.toHashPMF⟩

noncomputable def constant (value : Hash width) : HashEMF width where
  pmf := PMF.pure value
  values := {value}
  nonempty := Finset.singleton_nonempty value
  pmf_eq := by
    apply PMF.ext
    intro candidate
    simp [PMF.uniformOfFinset_apply]

noncomputable def uniform (width : Nat) : HashEMF width where
  pmf := FiniteUniform.pmf (Hash width)
  values := Finset.univ
  nonempty := Finset.univ_nonempty
  pmf_eq := rfl

noncomputable def prefixValues (fixed : Hash prefixWidth) (suffixWidth : Nat) :
    Finset (Hash (prefixWidth + suffixWidth)) :=
  Finset.univ.image fun suffix : Hash suffixWidth => fixed ++ suffix

@[simp] theorem prefixValues_card (fixed : Hash prefixWidth) (suffixWidth : Nat) :
    (prefixValues fixed suffixWidth).card = 2 ^ suffixWidth := by
  rw [prefixValues, Finset.card_image_of_injective]
  · simp
  · intro left right equal
    have suffixes := congrArg (BitVec.extractLsb' 0 suffixWidth) equal
    simpa only [BitVec.extractLsb'_append_eq_right] using suffixes

private theorem prefixValues_nonempty (fixed : Hash prefixWidth) (suffixWidth : Nat) :
    (prefixValues fixed suffixWidth).Nonempty := by
  refine ⟨fixed ++ 0#suffixWidth, ?_⟩
  simp [prefixValues]

noncomputable def uniformPrefix (fixed : Hash prefixWidth) (suffixWidth : Nat) :
    HashEMF (prefixWidth + suffixWidth) where
  pmf := PMF.uniformOfFinset (prefixValues fixed suffixWidth)
    (prefixValues_nonempty fixed suffixWidth)
  values := prefixValues fixed suffixWidth
  nonempty := prefixValues_nonempty fixed suffixWidth
  pmf_eq := rfl

noncomputable def support (distribution : HashPMF width) : Finset (Hash width) :=
  Finset.univ.filter fun value => distribution value ≠ 0

noncomputable def supportCard (distribution : HashPMF width) : Nat :=
  (support distribution).card

theorem support_nonempty (distribution : HashPMF width) :
    (support distribution).Nonempty := by
  obtain ⟨value, present⟩ := distribution.pmf.support_nonempty
  exact ⟨value, by simpa [support] using present⟩

theorem apply_eq_inv_card (distribution : HashEMF width) {value : Hash width}
    (present : value ∈ support distribution.toHashPMF) :
    distribution.pmf value = (supportCard distribution.toHashPMF : ENNReal)⁻¹ := by
  rw [distribution.pmf_eq]
  have member : value ∈ distribution.values := by
    simpa [support, distribution.pmf_eq, PMF.uniformOfFinset_apply] using present
  simp [supportCard, support, distribution.pmf_eq, PMF.uniformOfFinset_apply, member]

noncomputable def map₂ (operation : Hash width → Hash width → Hash width)
    (left right : HashPMF width) : HashPMF width where
  pmf := left.pmf.bind fun x => right.pmf.map fun y => operation x y

noncomputable def map (operation : Hash width → Hash width)
    (distribution : HashPMF width) : HashPMF width where
  pmf := distribution.pmf.map operation

noncomputable def HashEMF.mapEquiv (equivalence : Hash width ≃ Hash width)
    (distribution : HashEMF width) : HashEMF width where
  pmf := distribution.pmf.map equivalence
  values := distribution.values.image equivalence
  nonempty := distribution.nonempty.image equivalence
  pmf_eq := by
    rw [distribution.pmf_eq]
    apply PMF.ext
    intro output
    rw [PMF.map_apply, tsum_eq_single (equivalence.symm output)]
    · have exists_iff :
          (∃ value ∈ distribution.values, equivalence value = output) ↔
            equivalence.symm output ∈ distribution.values := by
        constructor
        · rintro ⟨value, member, rfl⟩
          simpa using member
        · intro member
          exact ⟨equivalence.symm output, member, equivalence.apply_symm_apply output⟩
      simp only [PMF.uniformOfFinset_apply]
      rw [Finset.card_image_of_injective _ equivalence.injective]
      simp [exists_iff]
    · intro other different
      have unequal : output ≠ equivalence other := by
        intro equal
        exact different (equivalence.injective (by simpa using equal.symm))
      simp [unequal]

noncomputable instance : HXor (HashPMF width) (HashPMF width) (HashPMF width) :=
  ⟨map₂ (· ^^^ ·)⟩

noncomputable instance : HAnd (HashPMF width) (HashPMF width) (HashPMF width) :=
  ⟨map₂ (· &&& ·)⟩

noncomputable instance : HOr (HashPMF width) (HashPMF width) (HashPMF width) :=
  ⟨map₂ (· ||| ·)⟩

noncomputable instance : Complement (HashPMF width) := ⟨map (~~~ ·)⟩

private def complementEquiv (width : Nat) : Hash width ≃ Hash width where
  toFun := (~~~ ·)
  invFun := (~~~ ·)
  left_inv value := by simp
  right_inv value := by simp

noncomputable instance : Complement (HashEMF width) :=
  ⟨HashEMF.mapEquiv (complementEquiv width)⟩

@[simp] theorem complement_toHashPMF (distribution : HashEMF width) :
    (~~~distribution : HashEMF width).toHashPMF = ~~~distribution.toHashPMF := rfl

noncomputable instance : Add (HashPMF width) := ⟨map₂ (· + ·)⟩

noncomputable instance : Sub (HashPMF width) := ⟨map₂ (· - ·)⟩

noncomputable instance : Neg (HashPMF width) := ⟨map (- ·)⟩

theorem map_uniform_xor (mask : Hash width) :
    (uniform width).pmf.map (fun value => value ^^^ mask) = (uniform width).pmf := by
  apply PMF.ext
  intro output
  rw [PMF.map_apply]
  rw [tsum_eq_single (output ^^^ mask)]
  · simp [uniform, FiniteUniform.pmf, BitVec.xor_assoc]
  · intro other hne
    simp only [ite_eq_right_iff]
    intro equal
    exfalso
    apply hne
    apply (BitVec.xor_left_inj mask).mp
    simpa [BitVec.xor_assoc] using equal.symm

theorem xor_uniform_right (distribution : HashPMF width) :
    distribution ^^^ (uniform width : HashPMF width) = uniform width := by
  apply ext
  change (distribution.pmf.bind fun x =>
    (uniform width).pmf.map fun y => x ^^^ y) = (uniform width).pmf
  simp_rw [show ∀ x : Hash width,
    (uniform width).pmf.map (fun y => x ^^^ y) = (uniform width).pmf by
      intro x
      simpa [BitVec.xor_comm] using map_uniform_xor x]
  exact PMF.bind_const _ _

@[simp] theorem xor_uniform_uniform :
    (uniform width).toHashPMF ^^^ (uniform width : HashPMF width) = uniform width :=
  xor_uniform_right _

end HashPMF

end Nucleus
