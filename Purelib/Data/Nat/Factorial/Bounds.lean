module
public import Purelib.Data.Nat.Factorial.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.Group.Nat.Defs

section
public section

/-! Data Nat Factorial Bounds and its finite structural certificates. -/

namespace Purelib.Data.Nat.Factorial.Bounds

open Purelib.Data.Nat.Factorial

/-- The factorial of index + 1 bounds two raised to index.

Starting from the zero exponent, each successor factorial contributes a factor at
least two, preserving the inductive lower bound. -/
theorem two_pow_le_factorial_succ : ∀ index,
    Nat.pow 2 index ≤
      Basic.factorial (index + 1)
  | 0 => by decide
  | index + 1 => by
      change Nat.pow 2 index * 2 ≤ Basic.factorial (index + 1 + 1)
      rw [Basic.factorial_succ]
      exact Nat.mul_le_mul
        (Data.Nat.Factorial.Bounds.two_pow_le_factorial_succ index) (by omega)
end Purelib.Data.Nat.Factorial.Bounds

end
