module

import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Nat.Factorial.Basic

/-! ## The finite Horner program as a bounded Taylor polynomial -/

/-- Compute the factorial of a natural number by finite multiplication.

The value at zero is one, and each successor multiplies the previous factorial by
that successor. -/
def factorial : Nat → Nat
  | 0 => 1
  | degree + 1 => factorial degree * (degree + 1)

open Purelib.Data.Nat.Factorial
/-- The factorial of zero is one. -/
@[simp] theorem factorial_zero : factorial 0 = 1 := rfl

/-- A successor factorial multiplies the preceding factorial by its new index. -/
@[simp] theorem factorial_succ (degree : Nat) :
    factorial (degree + 1) = factorial degree * (degree + 1) := rfl

/-- Every natural factorial is strictly positive. -/
theorem factorial_pos : ∀ degree : Nat, 0 < factorial degree
  | 0 => by decide
  | degree + 1 =>
      Nat.mul_pos (factorial_pos degree) (Nat.zero_lt_succ degree)
end Purelib.Data.Nat.Factorial.Basic

end
