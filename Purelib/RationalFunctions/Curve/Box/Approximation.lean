module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite box conditions along a rational curve

A rational curve is stored homogeneously as `N(t) / D(t)`.  On every
displayed parameter where `D(t)` is nonzero, membership of the affine point
in a rational box is equivalent to four nonnegative univariate polynomial
evaluations.  The common positive factor is the explicitly displayed
quadrance `normSq (D(t))`, so no denominator sign choice or square root is
needed.

The nonzero members of the four-polynomial family are also collected into a
single finite product guard.  A later common Sturm subdivision can therefore
cut once while preserving all box-edge signs; identically-zero edge
conditions remain explicit instead of making the guard vanish.
-/

namespace Purelib.RationalFunctions.Curve.Box

open Purelib.Data in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Cleared box-condition lower bounds place a curve point within the given coordinate radius of the box.

The denominator is nonzero, the radius is nonnegative, and the supplied lower bound is at most denominator quadrance.
Each cleared condition is strictly greater than minus that lower bound times the radius. -/
theorem point_within_radius_of_condition_lower
    (curve : Curve.RationalCurve) (box : Rational.Box) (parameter radius lower : Rat.Fraction.Rational)
    (radiusNonnegative : 0 ≤ radius)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (lowerLeDenominator : lower ≤
      Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter))
    (xLower : -(lower * radius) <
      (Curve.Box.xLowerPolynomial curve box).eval parameter)
    (xUpper : -(lower * radius) <
      (Curve.Box.xUpperPolynomial curve box).eval parameter)
    (yLower : -(lower * radius) <
      (Curve.Box.yLowerPolynomial curve box).eval parameter)
    (yUpper : -(lower * radius) <
      (Curve.Box.yUpperPolynomial curve box).eval parameter) :
    box.xLower - radius < (curve.point parameter).re ∧
      (curve.point parameter).re < box.xUpper + radius ∧
      box.yLower - radius < (curve.point parameter).im ∧
      (curve.point parameter).im < box.yUpper + radius := by
  let denominatorNorm := Gaussian.Norm.Basic.normSq (curve.denominatorAt parameter)
  have denominatorPositive : 0 < denominatorNorm := by
    simpa only [denominatorNorm] using Gaussian.Norm.Basic.normSq_pos denominatorNonzero
  have scaledLower : lower * radius ≤ denominatorNorm * radius :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      lowerLeDenominator radiusNonnegative
  have cancelLower {delta condition : Rat.Fraction.Rational}
      (conditionEq : condition = denominatorNorm * delta)
      (conditionLower : -(lower * radius) < condition) :
      -radius < delta := by
    apply Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := denominatorNorm) _ denominatorPositive
    calc
      -radius * denominatorNorm = -(denominatorNorm * radius) := by ring1
      _ ≤ -(lower * radius) :=
        Rat.Fraction.Order.Arithmetic.neg_le_neg_direct scaledLower
      _ < condition := conditionLower
      _ = delta * denominatorNorm := by rw [conditionEq]; ring1
  have leftDelta : -radius < (curve.point parameter).re - box.xLower :=
    cancelLower
      (Curve.Box.eval_xLowerPolynomial curve box parameter denominatorNonzero) xLower
  have rightDelta : -radius < box.xUpper - (curve.point parameter).re :=
    cancelLower
      (Curve.Box.eval_xUpperPolynomial curve box parameter denominatorNonzero) xUpper
  have bottomDelta : -radius < (curve.point parameter).im - box.yLower :=
    cancelLower
      (Curve.Box.eval_yLowerPolynomial curve box parameter denominatorNonzero) yLower
  have topDelta : -radius < box.yUpper - (curve.point parameter).im :=
    cancelLower
      (Curve.Box.eval_yUpperPolynomial curve box parameter denominatorNonzero) yUpper
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      box.xLower - radius = -radius + box.xLower := by ring1
      _ < ((curve.point parameter).re - box.xLower) + box.xLower :=
        Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct leftDelta box.xLower
      _ = (curve.point parameter).re := by ring1
  · have shifted := Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct
      rightDelta (curve.point parameter).re
    calc
      (curve.point parameter).re =
          (-radius + (curve.point parameter).re) + radius := by ring1
      _ < (box.xUpper - (curve.point parameter).re +
          (curve.point parameter).re) + radius :=
        Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct shifted radius
      _ = box.xUpper + radius := by ring1
  · calc
      box.yLower - radius = -radius + box.yLower := by ring1
      _ < ((curve.point parameter).im - box.yLower) + box.yLower :=
        Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct bottomDelta box.yLower
      _ = (curve.point parameter).im := by ring1
  · have shifted := Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct
      topDelta (curve.point parameter).im
    calc
      (curve.point parameter).im =
          (-radius + (curve.point parameter).im) + radius := by ring1
      _ < (box.yUpper - (curve.point parameter).im +
          (curve.point parameter).im) + radius :=
        Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct shifted radius
      _ = box.yUpper + radius := by ring1
end Purelib.RationalFunctions.Curve.Box

end
