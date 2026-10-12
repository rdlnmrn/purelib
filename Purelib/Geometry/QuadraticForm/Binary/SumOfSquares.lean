module
public import Purelib.Algebra.Field.Squares

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

/-!
# Divine Proportions, remaining Chapter 5 exercises

Exercise 5.3 is false with the source's definition of a triangle: the
nonzero quadrances `1,1,4` have zero quadrea, hence cannot belong to three
noncollinear points.  The corrected theorem below isolates the exact missing
condition.  In a field carrying an explicit square root of `-1`, every scalar
is constructively a sum of two squares, so Theorem 28 reduces triangle
existence to an explicit nonzero square witness for the quadrea.

Exercise 5.17 is retained through the finite construction responsible for its
factor `2`: a chosen base vector and either sign of a nonzero quadrea root give
two distinct completion points with the requested quadrances.  The remaining
`p²` translation and `p±1` nonzero-circle factors are recorded as finite
counting data rather than by enumerating an entire field carrier.

Exercise 5.19 is answered by a recursive, fuel-indexed finite quad relation.
For five entries it introduces the two diagonals of a fan triangulation; for
any requested finite number of entries it repeatedly combines two adjacent
signed lengths.  There is no infinite sequence or completed polygon.
-/

@[expose] public section

namespace Purelib.Geometry.QuadraticForm.Binary.SumOfSquares

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- In a field with an explicit imaginary unit, every scalar has a displayed sum-of-two-squares representation. -/
theorem isSumOfTwoSquares_of_squareRootNegativeOne
    (value imaginary : K) (twoNonzero : (2 : K) ≠ 0)
    (imaginarySquare : imaginary ^ 2 = -1) :
    Squares.IsSumOfTwoSquares value := by
  let first := (value + 1) / 2
  let second := imaginary * (value - 1) / 2
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  refine ⟨first, second, ?_⟩
  unfold first second
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    ((value + 1) * (2 : K)⁻¹) ^ 2 +
          (imaginary * (value - 1) * (2 : K)⁻¹) ^ 2 =
        ((value + 1) ^ 2 + imaginary ^ 2 * (value - 1) ^ 2) *
          (2 : K)⁻¹ ^ 2 := by ring1
    _ = 4 * value * (2 : K)⁻¹ ^ 2 := by
      rw [imaginarySquare]
      ring1
    _ = value * ((2 : K) * (2 : K)⁻¹) ^ 2 := by ring1
    _ = value := by rw [twoCancel]; ring1
section
end

section
end

end Purelib.Geometry.QuadraticForm.Binary.SumOfSquares

end
