/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Algebra.Number
import Algebra.Util
import Lean

namespace Algebra
namespace NormNum

universes u
variable {α : Type u} [Zero α] [One α] [Add α] [Mul α]

axiom nat2bits.zero : nat2bits α 0 = Zero.zero
axiom nat2bits.one  : nat2bits α 1 = One.one

axiom nat2bits.add (m n : Nat) (x y : α) : x = nat2bits α m → y = nat2bits α n → x + y = nat2bits α (m + n)
axiom nat2bits.mul (m n : Nat) (x y : α) : x = nat2bits α m → y = nat2bits α n → x * y = nat2bits α (m * n)

open Lean

structure Result where
  number : Nat
  term   : Expr
  proof  : Expr

-- TODO: several opportunities for perf
partial def normNumCore (type e : Expr) : MetaM Result := do
  match isNum? e with
  | some n => pure ⟨n, e, ← Meta.mkEqRefl e⟩
  | none =>
  match isAdd? e with
  | some (x, y) => hbin (.+.) `Algebra.NormNum.nat2bits.add x y
  | none =>
  match isMul? e with
  | some (x, y) => hbin (.*.) `Algebra.NormNum.nat2bits.mul x y
  | none => throwError! "normNum failed, number/add/mul expected, found: {e}"
  where
    hbin op thm x y := do
      let ⟨m, x', px⟩ ← normNumCore type x
      let ⟨n, y', py⟩ ← normNumCore type y
      let k : Nat := op m n
      let z  ← Meta.mkAppM `Algebra.nat2bits #[type, mkNatLit k]
      -- PERF: some of these might be refl
      -- in which case `Result`/custom-builder could pay off
      let pf ← Meta.mkAppM thm #[mkNatLit m, mkNatLit n, x, y, px, py]
      pure ⟨k, z, pf⟩

syntax (name := normNum) "normNum" : tactic

open Lean.Elab.Tactic

@[tactic normNum] def evalNormNum : Tactic := fun stx => do
  let (g, gs) ← getMainGoal
  Meta.withMVarContext g do
    let goal := (← getMCtx).getDecl g |>.type
    if goal.isAppOfArity `Eq 3 then
      let #[type, x, y] ← (pure goal.getAppArgs) | throwError "foo"
      let ⟨m, x', px⟩ ← normNumCore type x
      let ⟨n, y', py⟩ ← normNumCore type y
      let pf ← Meta.mkEqTrans px (← Meta.mkEqSymm py)
      Meta.assignExprMVar g pf

example : (2 : α) + 2 = 4                          := by normNum
example : (2000000 : α) + 2000000 = 4000000        := by normNum
example : (2000 : α) * 2000 = 4000000              := by normNum
example : ((1 : α) + 1) * (2 * 2) * (4 + 10) = 112 := by normNum

end NormNum
end Algebra
