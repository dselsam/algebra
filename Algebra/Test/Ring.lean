/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Algebra.Ring
import Lean
import Std.Data.HashMap

namespace Algebra
namespace Ring

namespace Test

variable {α : Type u} [CRing α] (x y z w : α)

theorem t00 : (0 : α) = 0          := by ring
theorem t01 : (0 : α) + 0 = 0      := by ring
theorem t02 : (1 : α) + 0 = 1      := by ring
theorem t03 : (1 : α) + 1 = 2      := by ring
theorem t04 : (5 : α) + 7 = 12     := by ring
theorem t05 : (5 : α) * 7 = 35     := by ring

theorem t10 : x = x                := by ring
theorem t11 : x - x = 0            := by ring
theorem t12 : x + y = y + x        := by ring
theorem t13 : 2 * x = x + x        := by ring

theorem t21 : x^(2:Nat) = x*x       := by ring
theorem t22 : x^(3:Nat) = x*x*x     := by ring
theorem t23 : x^(4:Nat) = x*x*x*x   := by ring

theorem t30 : x^(2:Nat) * x^(3:Nat) = x^(5:Nat) := by ring
theorem t31 : x^(2:Nat) * (x^(3:Nat) + 1) = x^(5:Nat) + x^(2:Nat) := by ring

theorem t32 : (x + y) * x^(2:Nat) * (x^(3:Nat) + 1) = x^(6:Nat) + x^(3:Nat) + y * x^(5:Nat) + y * x^(2:Nat) := by ring

theorem t33 : (x + y)^(2:Nat) = x^(2:Nat) + y^(2:Nat) + 2 * x * y := by ring

theorem t34 : (x + y + z)^(2:Nat) = x^(2:Nat) + y^(2:Nat) + z^(2:Nat) + 2*x*y + 2*y*z + 2*x*z := by ring
theorem t35 : x^(2:Nat) + 2*x*y + y^(2:Nat) = (x + y)^(2:Nat) := by ring
theorem t36 : x^(2:Nat) + 2*x*y + y^(2:Nat) = (x + y)^(2:Nat) := by ring

theorem t37 :(x + 1) * y = x * y + 1 * y := by ring
theorem t38 : x^(2:Nat) * (x + 1) * y = x^(3:Nat) * y + 1 * y * x^(2:Nat) := by ring

end Test

namespace Perf

variable {α : Type u} [CRing α] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ : α)

--theorem perf05 : (x₁ + x₂ + x₃ + x₄ + x₅)^(10:Nat) = 0 := by ring

end Perf


end Ring
end Algebra
