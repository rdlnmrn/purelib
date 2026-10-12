module
public import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.SquareRoot.Radius

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.Data.Rat

@[expose] public section

/-!
# Rational radii for squared variation budgets

The finite dyadic square-radius selector pays a squared error directly.
Unlike replacing `r²` by `r`, this does not lose another power of a small
clearance.  The selector inspects rational bounds only, not a mesh or owner.
-/

namespace Purelib.Approximation.Budget.SquaredVariationRadius

/-- The canonical rational coordinate type for squared-variation radii. -/
abbrev RadiusCoordinate := Fraction.Rational

/-- Select a dyadic radius for the target divided by eight times the incremented scale.

For a positive target and nonnegative scale, this retains a square-based error margin without extracting a square root.
-/
def squaredVariationRadius (target scale : RadiusCoordinate) :
  RadiusCoordinate :=
  Geometric.dyadicSquareRadius (target / (8 * (scale + 1)))

/-- The selected squared-variation radius is strictly positive. -/
theorem squaredVariationRadius_positive (target scale : RadiusCoordinate) :
    0 < squaredVariationRadius target scale :=
  Geometric.dyadicSquareRadius_positive _

/-- The selected squared-variation radius is at most one. -/
theorem squaredVariationRadius_le_one (target scale : RadiusCoordinate) :
    squaredVariationRadius target scale ≤ 1 :=
  Dyadic.dyadicSquareRadius_le_one _

/-- Any smaller nonnegative radius retains the exact squared-error budget.

The original selected dyadic radius pays the target divided by eight times
the incremented nonnegative scale. Monotonicity of the displayed square and
exact positive-denominator cancellation retain that strict target payment. -/
theorem squaredVariation_error_lt {target scale radius : RadiusCoordinate}
    (targetPositive : 0 < target) (scaleNonnegative : 0 ≤ scale)
    (radiusNonnegative : 0 ≤ radius)
    (radiusBound : radius ≤ squaredVariationRadius target scale) :
    scale * (8 * radius ^ 2) < target := by
  have denominatorPositive : 0 < 8 * (scale + 1) :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide))
  have squareSmall : radius ^ 2 < target / (8 * (scale + 1)) :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusNonnegative radiusBound 2).trans_lt
      (Geometric.dyadicSquareRadius_sq_lt
        (Fraction.Order.Field.div_pos_direct targetPositive denominatorPositive))
  have enlarged : scale ≤ scale + 1 := by
    calc
      scale = scale + 0 := (_root_.add_zero scale).symm
      _ ≤ scale + 1 := Fraction.Order.Arithmetic.add_le_add_direct le_rfl (by decide)
  calc
    _ ≤ (scale + 1) * (8 * radius ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        enlarged
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    _ = radius ^ 2 * (8 * (scale + 1)) := by ring1
    _ < target := (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).1 squareSmall

end Purelib.Approximation.Budget.SquaredVariationRadius

end
