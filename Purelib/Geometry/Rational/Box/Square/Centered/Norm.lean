module

public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Group.Defs

/-! # A rational square enclosing a displayed quadrance budget

The half-width one plus the nonnegative quadrance bound requires no square
root. Its original centred-square constructor and containment theorem give
an explicit enclosure of every point paying that same bound.
-/

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The computed half-width one plus a nonnegative quadrance bound is itself nonnegative. -/
theorem normRadius_nonnegative {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) : 0 ≤ 1 + bound := by
  have result := Fraction.Order.Arithmetic.add_le_add_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1) nonnegative
  rewrite [Fraction.Field.zero_add] at result
  exact result

/-- The square of the computed half-width bounds the original nonnegative quadrance budget. -/
theorem normRadius_square_lower {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) : bound ≤ (1 + bound) ^ 2 := by
  have boundLe : bound ≤ 1 + bound := by
    have result := Fraction.Order.Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
      (Fraction.Order.Basic.le_refl bound)
    rewrite [Fraction.Field.zero_add] at result
    exact result
  have oneLe : (1 : Fraction.Rational) ≤ 1 + bound := by
    have result := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) nonnegative
    rewrite [Fraction.Field.add_comm (1 : Fraction.Rational) 0, Fraction.Field.zero_add] at result
    exact result
  have squared := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe (normRadius_nonnegative nonnegative)
  rewrite [Fraction.Field.one_mul] at squared
  rewrite [pow_two]
  exact boundLe.trans squared

/-- Construct the original zero-centred rational square with half-width one plus the retained quadrance bound. -/
@[expose] def normBox (bound : Fraction.Rational) (nonnegative : 0 ≤ bound) : Rational.Box :=
  BoxTransport.centeredBox 0 (1 + bound) (normRadius_nonnegative nonnegative)

/-- Equal quadrance budgets give the same complete centered box with either retained nonnegativity proof. -/
theorem normBox_congr {left right : Fraction.Rational} (leftNonnegative : 0 ≤ left)
    (rightNonnegative : 0 ≤ right) (same : left = right) :
    normBox left leftNonnegative = normBox right rightNonnegative := by
  cases same
  rfl

/-- Every original point paying the displayed quadrance budget belongs to that same computed rational square. -/
theorem normBox_contains {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) {value : Canonical}
    (bounded : Norm.Basic.normSq value ≤ bound) : (normBox bound nonnegative).Contains value := by
  apply centeredBox_contains_of_normSq_sub_le (normRadius_nonnegative nonnegative)
  rewrite [Gaussian.Basic.sub_zero]
  exact bounded.trans (normRadius_square_lower nonnegative)

end Purelib.Geometry.Rational.Box.Square.Centered
