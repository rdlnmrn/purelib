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

namespace Purelib.Data.Nat.Odd

/-! ## The finite complex-log program as an odd polynomial -/

/-- Compute the truncated natural expression 2 * index - 1.

For a positive index this is its preceding positive odd number; at index zero natural
subtraction returns zero. -/
def priorOdd (index : Nat) : Nat := 2 * index - 1

open Purelib.Data.Nat in
/-- The preceding odd expression is positive at every index at least one. -/
theorem priorOdd_pos {index : Nat} (positive : 1 ≤ index) :
    0 < priorOdd index := by
  unfold priorOdd
  omega
end Purelib.Data.Nat.Odd

end
