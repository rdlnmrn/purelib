module

import Purelib.Data.Nat.Subtraction

namespace Purelib.Data.Nat.Addition

/-- Equal natural sums with the same left summand have equal right summands.

Subtracting the retained common summand recovers each original right summand.
Scalar transport of the supplied sum equality identifies those two results. -/
public theorem add_left_cancel {common left right : Nat}
    (equal : common + left = common + right) : left = right := by
  calc
    left = common + left - common := (Subtraction.add_sub_cancel_left common left).symm
    _ = common + right - common := congrArg (fun value => value - common) equal
    _ = right := Subtraction.add_sub_cancel_left common right

/-- Equal natural sums with the same right summand have equal left summands.

Commuting each scalar sum exposes the common summand on the left. Cancellation
then retains and identifies the original two left summands. -/
public theorem add_right_cancel {left right common : Nat}
    (equal : left + common = right + common) : left = right := by
  apply add_left_cancel (common := common)
  exact (Nat.add_comm common left).trans (equal.trans (Nat.add_comm right common))

end Purelib.Data.Nat.Addition

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

namespace Purelib.Data.Nat.Addition

/-- Move a successor increment past the final summand in a natural sum. -/
public theorem add_one_add (left right : Nat) :
    left + 1 + right = left + right + 1 := by
  calc
    left + 1 + right = left + (1 + right) := Nat.add_assoc _ _ _
    _ = left + (right + 1) := by rw [Nat.add_comm 1 right]
    _ = left + right + 1 := (Nat.add_assoc _ _ _).symm

end Purelib.Data.Nat.Addition

end
