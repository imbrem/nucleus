import Nucleus.Hash.PMF

/-! # Fair binary choices between hash distributions -/

namespace Nucleus.HashPMF

variable {width : Nat}

/-- Choose either distribution with equal probability, then sample it. -/
noncomputable def fairChoice (left right : HashPMF width) : HashPMF width where
  pmf := (FiniteUniform.pmf Bool).bind fun chooseLeft =>
    if chooseLeft then left.pmf else right.pmf

set_option linter.flexible false in
theorem fairChoice_apply (left right : HashPMF width) (value : Hash width) :
    fairChoice left right value = 2⁻¹ * left value + 2⁻¹ * right value := by
  simp [fairChoice, PMF.bind_apply, FiniteUniform.pmf,
    PMF.uniformOfFintype, PMF.uniformOfFinset_apply]

theorem fairChoice_comm (left right : HashPMF width) :
    fairChoice left right = fairChoice right left := by
  apply ext
  apply PMF.ext
  intro value
  simp [fairChoice_apply, add_comm]

@[simp] theorem fairChoice_self (distribution : HashPMF width) :
    fairChoice distribution distribution = distribution := by
  apply ext
  apply PMF.ext
  intro value
  rw [fairChoice_apply, ← add_mul]
  rw [ENNReal.inv_two_add_inv_two, one_mul]

theorem support_fairChoice (left right : HashPMF width) :
    support (fairChoice left right) = support left ∪ support right := by
  ext value
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
    fairChoice_apply, Finset.mem_union]
  by_cases leftZero : left value = 0 <;>
    by_cases rightZero : right value = 0 <;> simp [leftZero, rightZero]

set_option linter.flexible false in
theorem fairChoice_not_associative : ¬ Std.Associative (@fairChoice 1) := by
  intro associative
  let zero : HashPMF 1 := constant 0#1
  let one : HashPMF 1 := constant 1#1
  have equal := associative.assoc zero zero one
  have mass := congrArg (fun distribution : HashPMF 1 => distribution 0#1) equal
  simp [zero, one, fairChoice_apply, constant] at mass
  have realMass := congrArg ENNReal.toReal mass
  rw [ENNReal.toReal_add (by simp) (ENNReal.mul_ne_top (by simp) (by simp)),
    ENNReal.toReal_mul, ENNReal.toReal_inv] at realMass
  norm_num at realMass

end Nucleus.HashPMF
