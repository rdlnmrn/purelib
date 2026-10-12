module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Geometry.Trigonometry

/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.QuadTriple.Null

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- First clause of Exercise 6.4: setting the null-side quadrance to zero reduces quadrea to the negative square
`-(q₁-q₂)²`. -/
theorem archimedesFunction_third_zero (q₁ q₂ : K) :
    QuadTriple.Basic.archimedesFunction q₁ q₂ 0 = -(q₁ - q₂) ^ 2 := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

/-- Exercise 6.5: if the other two quadrances vanish, quadrea is `-q₁²`. The source's premise `q₁≠0` is unnecessary for
this polynomial identity. -/
theorem archimedesFunction_second_third_zero (q₁ : K) :
    QuadTriple.Basic.archimedesFunction q₁ 0 0 = -q₁ ^ 2 := by
  unfold QuadTriple.Basic.archimedesFunction
  ring1

end Purelib.Geometry.Trigonometry.QuadTriple.Null

end
