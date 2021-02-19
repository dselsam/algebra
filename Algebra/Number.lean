/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
namespace Algebra

class Zero (α : Type u) := (zero : α)
class One  (α : Type u) := (one : α)

universes u

variable {α : Type u} [Zero α] [One α] [Add α] [Mul α]

def bit0 (x : α) : α := x + x
def bit1 (x : α) : α := bit0 x + One.one

instance instOne2Inhabited [One α] : Inhabited α := ⟨One.one⟩

variable (α : Type u) [Zero α] [One α] [Add α] [Mul α]

instance instNat0 : OfNat α (noindex! 0) := ⟨Zero.zero⟩
instance instNat1 : OfNat α (noindex! 1) := ⟨One.one⟩

partial def nat2bits (n : Nat) : α :=
  if n = 0 then Zero.zero
  else if n = 1 then One.one
  else (if n % 2 == 1 then bit1 else bit0) (nat2bits $ n / 2)

instance instNat2Bits (n : Nat) : OfNat α n := ⟨nat2bits α n⟩

end Algebra
