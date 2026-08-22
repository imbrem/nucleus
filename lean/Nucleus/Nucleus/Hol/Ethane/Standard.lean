import Nucleus.Hol.Ethane.Logic
import Nucleus.Hol.Ethane.Semantics
import Nucleus.HolE.Peano

/-!
# Ordinary Ethane definitions

This is the syntax-level specification of the standard initialization arena.
The Rust builder emits a shared dense graph for these definitions; sharing is
an encoding choice and does not add natural-number primitives to Ethane.
-/

namespace Nucleus.Hol.Ethane.Standard

open Nucleus.Hol.Ethane

abbrev EmptySig := Nucleus.HolE.EmptySig

private def typeName : Nat := 1
private def functionName : Nat := 2
private def zeroName : Nat := 3
private def xName : Nat := 4
private def yName : Nat := 5
private def predicateName : Nat := 7
private def valueName : Nat := 8
private def logicFunctionName : Nat := 102

def truth : Tm EmptySig := .bool true
def falsehood : Tm EmptySig := .bool false

def not : Tm EmptySig :=
  .lam 100 .boolTy (.not (.tmFv 100 .boolTy))

def and : Tm EmptySig :=
  .lam 100 .boolTy <|
    .lam 101 .boolTy <|
      .and logicFunctionName (.tmFv 100 .boolTy) (.tmFv 101 .boolTy)

private def app₂ (function left right : Tm EmptySig) : Tm EmptySig :=
  .app (.app function left) right

private def notTm (proposition : Tm EmptySig) : Tm EmptySig :=
  .app not proposition

private def andTm (left right : Tm EmptySig) : Tm EmptySig :=
  app₂ and left right

def or : Tm EmptySig :=
  .lam 100 .boolTy <|
    .lam 101 .boolTy <|
      notTm <| andTm (notTm (.tmFv 100 .boolTy)) (notTm (.tmFv 101 .boolTy))

def imp : Tm EmptySig :=
  .lam 100 .boolTy <|
    .lam 101 .boolTy <|
      notTm <| andTm (.tmFv 100 .boolTy) (notTm (.tmFv 101 .boolTy))

private def impTm (antecedent consequent : Tm EmptySig) : Tm EmptySig :=
  app₂ imp antecedent consequent

def reflectsEquality (carrier : Ty EmptySig) (function : Tm EmptySig) :
    Tm EmptySig :=
  let x := Expr.tmFv xName carrier
  let y := Expr.tmFv yName carrier
  .forallTm xName carrier <| .forallTm yName carrier <|
    .eq .boolTy (.eq carrier (.app function x) (.app function y))
      (.eq carrier x y)

def missesPoint (carrier : Ty EmptySig) (function zero : Tm EmptySig) :
    Tm EmptySig :=
  let x := Expr.tmFv xName carrier
  .forallTm xName carrier <| notTm (.eq carrier (.app function x) zero)

def infinityStructure (carrier : Ty EmptySig) (function zero : Tm EmptySig) :
    Tm EmptySig :=
  andTm (reflectsEquality carrier function)
    (missesPoint carrier function zero)

def peanoStructure (carrier : Ty EmptySig) (function zero : Tm EmptySig) :
    Tm EmptySig :=
  let predicateTy := Expr.arr carrier .boolTy
  let predicate := Expr.tmFv predicateName predicateTy
  let value := Expr.tmFv valueName carrier
  let base := Expr.app predicate zero
  let step := .forallTm valueName carrier <|
    impTm (.app predicate value)
      (.app predicate (.app function value))
  let cases := andTm base step
  let all := .forallTm valueName carrier (.app predicate value)
  let induction := .forallTm predicateName predicateTy <|
    impTm cases all
  andTm (infinityStructure carrier function zero) induction

def infinityTypePredicate (carrier : Ty EmptySig) : Tm EmptySig :=
  let endomap := Expr.arr carrier carrier
  let function := Expr.tmFv functionName endomap
  let zero := Expr.tmFv zeroName carrier
  .existsTm functionName endomap <| .existsTm zeroName carrier <|
    infinityStructure carrier function zero

def peanoTypePredicate (carrier : Ty EmptySig) : Tm EmptySig :=
  let endomap := Expr.arr carrier carrier
  let function := Expr.tmFv functionName endomap
  let zero := Expr.tmFv zeroName carrier
  .existsTm functionName endomap <| .existsTm zeroName carrier <|
    peanoStructure carrier function zero

def carrier : Ty EmptySig := .tyFv typeName .star

def infinity : Tm EmptySig := .tyExists typeName (infinityTypePredicate carrier)

def natExists : Tm EmptySig := .tyExists typeName (peanoTypePredicate carrier)

def nat : Ty EmptySig := .model typeName (peanoTypePredicate carrier)

def succ : Tm EmptySig :=
  let endomap := Expr.arr nat nat
  let function := Expr.tmFv functionName endomap
  let zero := Expr.tmFv zeroName nat
  let predicate := .lam functionName endomap <|
    .existsTm zeroName nat (peanoStructure nat function zero)
  .eps endomap predicate

def zero : Tm EmptySig :=
  let zero := Expr.tmFv zeroName nat
  .eps nat (.lam zeroName nat (peanoStructure nat succ zero))

end Nucleus.Hol.Ethane.Standard
