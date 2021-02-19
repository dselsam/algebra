import Algebra.Ring

open Algebra.Ring

variable (α : Type u) [CRing α] (x1 x2 x3 x4 x5 x6 x7 x8 : α)

--set_option interpreter.prefer_native true

--theorem n8d15 : (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8)^(15 : Nat) = (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 0)^(15 : Nat) := by
--  ringNative

def main : IO Unit := do
  println! "Algebra"
