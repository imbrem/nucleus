import Nucleus.HolOmega.Consistency

/-! # Kernel-facing raw HOL-omega specification -/

universe u v

namespace Nucleus.HolOmega.Spec

abbrev Kind := HolOmega.Kind
abbrev RKind := HolOmega.RKind
abbrev Ty (Base : Type u) := HolOmega.Ty Base
abbrev Tm (Base : Type u) := HolOmega.Tm Base
abbrev KindCtx := HolOmega.KindCtx
abbrev TermCtx (Base : Type u) := HolOmega.TmCtx Base
abbrev Assumptions (Base : Type u) := HolOmega.Hyps Base
abbrev Goal (Base : Type u) := HolOmega.JudgementIndex Base
abbrev Certificate {Base : Type u} := @HolOmega.Judgement Base
abbrev EqualityCertificate {Base : Type u} := @HolOmega.EqTm Base
abbrev ProofCertificate {Base : Type u} := @HolOmega.Proves Base

abbrev Universe := HolOmega.Kernel.Universe
abbrev Omega (U : Universe) := HolOmega.Omega U
abbrev BaseSemantics (Base : Type u) (U : Universe.{v}) :=
  HolOmega.BaseSemantics Base U
abbrev Denotes := @HolOmega.Denotes
abbrev CtxValid := @HolOmega.CtxValid
abbrev Entails := @HolOmega.Entails

theorem certificateSound {Base : Type u} {U : Universe.{v}}
    (B : BaseSemantics Base U) {i : Goal Base} (d : Certificate i) :
    HolOmega.Sound B i := d.sound B

theorem equalitySound {Base : Type u} {U : Universe.{v}}
    (B : BaseSemantics Base U) {Δ Γ t u A}
    (d : @HolOmega.EqTm Base Δ Γ t u A) :
    HolOmega.EqTm.SemanticallyEqual B t u A := d.sound B

theorem proofSound {Base : Type u} {U : Universe.{v}}
    (B : BaseSemantics Base U) {Δ Γ H p}
    (d : @HolOmega.Proves Base Δ Γ H p) : HolOmega.Entails B Δ Γ H p :=
  d.sound B

theorem consistency :
    ¬HolOmega.Proves ([] : KindCtx) ([] : TermCtx Empty) [] (.tmBool false) :=
  HolOmega.raw_not_proves_false

end Nucleus.HolOmega.Spec
