module
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Square.Centered

section
@[expose] public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.Geometry.Rational.Box.Square.Centered.Interior

/-- A center within squared distance `r²` of the source anchor produces a strictly interior radius-`r` square whenever
the source avoids the four `4ρ` strips and `r ≤ ρ`. -/
theorem centeredSquare_strictInterior
    {outer source : Rational.Box} {center : Data.Gaussian.Basic.Canonical} {r rho : Fraction.Rational}
    (radiusPositive : 0 < r) (radiusLeProtected : r ≤ rho)
    (stripBounds :
      outer.xLower + 4 * rho < source.xLower ∧
        source.xUpper < outer.xUpper - 4 * rho ∧
        outer.yLower + 4 * rho < source.yLower ∧
        source.yUpper < outer.yUpper - 4 * rho)
    (near : Data.Gaussian.Norm.Basic.normSq (center - source.anchor) ≤ r ^ 2) :
    (Affine.centeredSquare center r radiusPositive.le).StrictInterior outer := by
  have coordinateBounds := Data.Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
    radiusPositive.le near
  have realLower : -r ≤ center.re - source.xLower := by
    exact coordinateBounds.1
  have realUpper : center.re - source.xLower ≤ r := by
    exact coordinateBounds.2.1
  have imaginaryLower : -r ≤ center.im - source.yLower := by
    exact coordinateBounds.2.2.1
  have imaginaryUpper : center.im - source.yLower ≤ r := by
    exact coordinateBounds.2.2.2
  have centerRealLower : source.xLower - r ≤ center.re := by
    calc
      source.xLower - r = -r + source.xLower := by ring1
      _ ≤ (center.re - source.xLower) + source.xLower :=
        add_le_add_left realLower source.xLower
      _ = center.re := by ring1
  have centerRealUpper : center.re ≤ source.xLower + r := by
    calc
      center.re = (center.re - source.xLower) + source.xLower := by ring1
      _ ≤ r + source.xLower := add_le_add_left realUpper source.xLower
      _ = source.xLower + r := by ring1
  have centerImaginaryLower : source.yLower - r ≤ center.im := by
    calc
      source.yLower - r = -r + source.yLower := by ring1
      _ ≤ (center.im - source.yLower) + source.yLower :=
        add_le_add_left imaginaryLower source.yLower
      _ = center.im := by ring1
  have centerImaginaryUpper : center.im ≤ source.yLower + r := by
    calc
      center.im = (center.im - source.yLower) + source.yLower := by ring1
      _ ≤ r + source.yLower :=
        add_le_add_left imaginaryUpper source.yLower
      _ = source.yLower + r := by ring1
  have twoRadiusLeFourProtected : 2 * r ≤ 4 * rho := by
    calc
      2 * r ≤ 2 * rho :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusLeProtected
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 2) (by decide)).le
      _ ≤ 4 * rho :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Cast.Order.natCast_le_direct
            (m := 2) (n := 4) (by decide))
          (radiusPositive.le.trans radiusLeProtected)
  have leftGap : outer.xLower + 2 * r < source.xLower :=
    (add_le_add_right twoRadiusLeFourProtected outer.xLower).trans_lt
      stripBounds.1
  have bottomGap : outer.yLower + 2 * r < source.yLower :=
    (add_le_add_right twoRadiusLeFourProtected outer.yLower).trans_lt
      stripBounds.2.2.1
  have rightGap : source.xUpper + 2 * r < outer.xUpper := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      stripBounds.2.1 (4 * rho)
    have fullGap : source.xUpper + 4 * rho < outer.xUpper := by
      calc
        source.xUpper + 4 * rho <
            (outer.xUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.xUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.xUpper).trans_lt
      fullGap
  have topGap : source.yUpper + 2 * r < outer.yUpper := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      stripBounds.2.2.2 (4 * rho)
    have fullGap : source.yUpper + 4 * rho < outer.yUpper := by
      calc
        source.yUpper + 4 * rho <
            (outer.yUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.yUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.yUpper).trans_lt
      fullGap
  constructor
  · have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      leftGap (-2 * r)
    calc
      outer.xLower = (outer.xLower + 2 * r) + (-2 * r) := by ring1
      _ < source.xLower + (-2 * r) := shifted
      _ = (source.xLower - r) - r := by ring1
      _ ≤ center.re - r := add_le_add_left centerRealLower (-r)
  · calc
      center.re + r ≤ source.xLower + 2 * r := by
        have shifted := add_le_add_left centerRealUpper r
        calc
          center.re + r ≤ (source.xLower + r) + r := shifted
          _ = source.xLower + 2 * r := by ring1
      _ ≤ source.xUpper + 2 * r :=
        add_le_add_left source.x_valid (2 * r)
      _ < outer.xUpper := rightGap
  · have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
      bottomGap (-2 * r)
    calc
      outer.yLower = (outer.yLower + 2 * r) + (-2 * r) := by ring1
      _ < source.yLower + (-2 * r) := shifted
      _ = (source.yLower - r) - r := by ring1
      _ ≤ center.im - r := add_le_add_left centerImaginaryLower (-r)
  · calc
      center.im + r ≤ source.yLower + 2 * r := by
        have shifted := add_le_add_left centerImaginaryUpper r
        calc
          center.im + r ≤ (source.yLower + r) + r := shifted
          _ = source.yLower + 2 * r := by ring1
      _ ≤ source.yUpper + 2 * r :=
        add_le_add_left source.y_valid (2 * r)
      _ < outer.yUpper := topGap
end Purelib.Geometry.Rational.Box.Square.Centered.Interior

end
