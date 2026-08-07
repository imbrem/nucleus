/-
SPDX-FileCopyrightText: 2026 Nucleus contributors
SPDX-License-Identifier: CC0-1.0
-/

/-!
# Typed environments

The intrinsically-typed variable and environment machinery shared by every
layer below. Nothing here is specific to HOL-omega; it is the ordinary
de Bruijn machinery, kept separate so the syntax modules do not have to
restate it.
-/

universe u v

namespace Nucleus.HolOmega

/-- A de Bruijn index proving membership in a context. -/
inductive Var {Ty : Type u} : List Ty → Ty → Type u
  | here : Var (A :: Γ) A
  | there : Var Γ A → Var (B :: Γ) A

/-- A pointwise environment: one element of `El A` for each `A` in the
context. -/
def Env {Ty : Type u} (El : Ty → Type v) : List Ty → Type (max u v)
  | [] => PUnit
  | A :: Γ => El A × Env El Γ

def Var.lookup {Ty : Type u} {El : Ty → Type v} {Γ : List Ty} {A : Ty} :
    Var Γ A → Env El Γ → El A
  | .here, env => env.1
  | .there v, env => v.lookup env.2

end Nucleus.HolOmega
