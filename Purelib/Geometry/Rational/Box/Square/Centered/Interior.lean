module
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Interior
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

open Purelib.Data.Rat.Fraction.Order

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
    {outer source : Box} {center : Data.Gaussian.Basic.Canonical} {r rho : Fraction.Rational}
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
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusLeProtected
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 2) (by decide)).le
      _ ≤ 4 * rho :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
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
    have shifted := Arithmetic.add_lt_add_right_direct
      stripBounds.2.1 (4 * rho)
    have fullGap : source.xUpper + 4 * rho < outer.xUpper := by
      calc
        source.xUpper + 4 * rho <
            (outer.xUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.xUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.xUpper).trans_lt
      fullGap
  have topGap : source.yUpper + 2 * r < outer.yUpper := by
    have shifted := Arithmetic.add_lt_add_right_direct
      stripBounds.2.2.2 (4 * rho)
    have fullGap : source.yUpper + 4 * rho < outer.yUpper := by
      calc
        source.yUpper + 4 * rho <
            (outer.yUpper - 4 * rho) + 4 * rho := shifted
        _ = outer.yUpper := by ring1
    exact (add_le_add_right twoRadiusLeFourProtected source.yUpper).trans_lt
      fullGap
  constructor
  · have shifted := Arithmetic.add_lt_add_right_direct
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
  · have shifted := Arithmetic.add_lt_add_right_direct
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

public section

namespace Purelib.Geometry.Rational.Box.Square.Centered.Interior

open Fraction.Order

/-- The minimum interior coordinate gap at the center of an original centered square equals its radius. -/
theorem centeredSquare_gap (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational)
    (nonnegative : 0 ≤ radius) :
    Rational.Box.Interior.strictCoordinateGap (Affine.centeredSquare center radius nonnegative) center = radius := by
  unfold Rational.Box.Interior.strictCoordinateGap
  change min (center.re - (center.re - radius)) (min (center.re + radius - center.re)
    (min (center.im - (center.im - radius)) (center.im + radius - center.im))) = radius
  rewrite [show center.re - (center.re - radius) = radius by ring1,
    show center.re + radius - center.re = radius by ring1,
    show center.im - (center.im - radius) = radius by ring1,
    show center.im + radius - center.im = radius by ring1,
    Basic.min_eq_left le_rfl, Basic.min_eq_left le_rfl, Basic.min_eq_left le_rfl]
  rfl

/-- A centered square whose radius fits the original minimum side gap refines that same outer box.

The original coordinate-gap minimum bounds each side separately. Translating
those four retained scalar bounds places the computed square endpoints
inside the same original outer endpoints. -/
theorem centeredSquare_refines_of_radius_le_gap {outer : Rational.Box}
    (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (small : radius ≤ Rational.Box.Interior.strictCoordinateGap outer center) :
    (Affine.centeredSquare center radius nonnegative).Refines outer := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (center.re - outer.xLower) - radius := Arithmetic.sub_nonneg_direct
        (small.trans (Basic.min_le_left _ _))
      _ = (center.re - radius) - outer.xLower := by ring1
  · apply Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (outer.xUpper - center.re) - radius := Arithmetic.sub_nonneg_direct
        (small.trans ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)))
      _ = outer.xUpper - (center.re + radius) := by ring1
  · apply Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (center.im - outer.yLower) - radius := Arithmetic.sub_nonneg_direct
        (small.trans ((Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))))
      _ = (center.im - radius) - outer.yLower := by ring1
  · apply Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (outer.yUpper - center.im) - radius := Arithmetic.sub_nonneg_direct
        (small.trans ((Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))))
      _ = outer.yUpper - (center.im + radius) := by ring1

/-- A centered square with radius below the original minimum side gap is strictly interior to that same outer box. -/
theorem centeredSquare_strictInterior_of_radius_lt_gap {outer : Rational.Box}
    (center : Data.Gaussian.Basic.Canonical) (radius : Fraction.Rational) (nonnegative : 0 ≤ radius)
    (small : radius < Rational.Box.Interior.strictCoordinateGap outer center) :
    (Affine.centeredSquare center radius nonnegative).StrictInterior outer := by
  constructor
  · apply Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (center.re - outer.xLower) - radius := Arithmetic.sub_pos_direct
        (small.trans_le (Basic.min_le_left _ _))
      _ = (center.re - radius) - outer.xLower := by ring1
  · apply Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (outer.xUpper - center.re) - radius := Arithmetic.sub_pos_direct
        (small.trans_le ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _)))
      _ = outer.xUpper - (center.re + radius) := by ring1
  · apply Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (center.im - outer.yLower) - radius := Arithmetic.sub_pos_direct
        (small.trans_le ((Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_left _ _))))
      _ = (center.im - radius) - outer.yLower := by ring1
  · apply Arithmetic.lt_of_sub_pos_direct
    calc
      0 < (outer.yUpper - center.im) - radius := Arithmetic.sub_pos_direct
        (small.trans_le ((Basic.min_le_right _ _).trans
          ((Basic.min_le_right _ _).trans (Basic.min_le_right _ _))))
      _ = outer.yUpper - (center.im + radius) := by ring1

end Purelib.Geometry.Rational.Box.Square.Centered.Interior
