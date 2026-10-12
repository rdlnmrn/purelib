module
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.InclinedPlane.Spread.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Problem 11. The three quotient-free equations are respectively the maximum-slope right triangle, the turn by spread
`r`, and the final line-to-horizontal spread. -/
theorem problem_11
    (S r maximumPath insectPath answer : K)
    (insectPathNonzero : insectPath ≠ 0)
    (maximumSlope : S * maximumPath = 1)
    (pathTurn : (1 - r) * insectPath = maximumPath)
    (answerSpread : answer * insectPath = 1) :
    answer = S * (1 - r) := by
  apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right insectPathNonzero
  calc
    answer * insectPath = 1 := answerSpread
    _ = S * maximumPath := maximumSlope.symm
    _ = (S * (1 - r)) * insectPath := by rw [← pathTurn]; ring1
end
end Purelib.Geometry.Space.InclinedPlane.Spread.Cleared

end
