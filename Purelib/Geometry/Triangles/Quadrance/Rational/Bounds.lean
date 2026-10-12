module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Triangles.Quadrance.Rational.Bounds

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Exercise 6.6 (Triangle inequality): for any three constructive-rational points, the Cross-law square is at most
`4Q₁Q₂`. -/
theorem cross_law_square_le (first second third :
  Purelib.Geometry.Plane.Point Fraction.Rational) :
    (Quadrance.quadrance second third + Quadrance.quadrance first third -
        Quadrance.quadrance first second) ^ 2 ≤
      4 * Quadrance.quadrance second third * Quadrance.quadrance first third := by
  have fourNonnegative : (0 : Fraction.Rational) ≤ 4 := by decide
  have determinantSquareNonnegative :
      (0 : Fraction.Rational) ≤ Incidence.pointDeterminant first second third ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have areaNonnegative : (0 : Fraction.Rational) ≤ Quadrea.Basic.quadrea first second third := by
    rw [Quadrea.Basic.quadrea_coordinate_formula]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      fourNonnegative determinantSquareNonnegative
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    (0 : Fraction.Rational) ≤ Quadrea.Basic.quadrea first second third := areaNonnegative
    _ = 4 * Quadrance.quadrance second third * Quadrance.quadrance first third -
        (Quadrance.quadrance second third + Quadrance.quadrance first third -
          Quadrance.quadrance first second) ^ 2 := by
            unfold Quadrea.Basic.quadrea Trigonometry.QuadTriple.Basic.archimedesFunction
            ring1

end

end Purelib.Geometry.Triangles.Quadrance.Rational.Bounds

end
