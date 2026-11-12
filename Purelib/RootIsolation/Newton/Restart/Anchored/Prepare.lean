module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
public import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian.Derivative.Separation

/-!
# Anchored inputs from bounded residuals

The computed rational radius satisfies the four strict box margins and the
retained displacement and Taylor budgets. A sufficiently small residual at
the displayed point then constructs the complete anchored input.
-/

namespace Purelib.RootIsolation.Newton.Restart.Anchored.Prepare

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Construct an anchored input from a residual below the computed target.

The original displayed point and computed radius retain four strict box
margins, the source threshold, displacement budget and Taylor remainder bound. -/
@[expose] public def anchoredInputOfResidual
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (strict : current.box.StrictContains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (residual : Gaussian.Norm.Basic.normSq (p.eval point) <
      Budget.anchoredResidualTarget squarefree current point cap) :
    Basic.AnchoredInput squarefree current := by
  let radius := Budget.anchoredRadius squarefree current point cap
  have radiusPositive : 0 < radius :=
    Budget.anchoredRadius_pos squarefree current point strict capPositive
  have bounds := Budget.anchoredRadius_bounds squarefree current point cap
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    have scaled :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct bounds.1
        radiusPositive.le
    exact scaled.trans_eq (_root_.one_mul radius)
  have leftGapPositive : 0 < point.re - current.box.xLower :=
    Arithmetic.sub_pos_direct strict.1
  have rightGapPositive : 0 < current.box.xUpper - point.re :=
    Arithmetic.sub_pos_direct strict.2.1
  have bottomGapPositive : 0 < point.im - current.box.yLower :=
    Arithmetic.sub_pos_direct strict.2.2.1
  have topGapPositive : 0 < current.box.yUpper - point.im :=
    Arithmetic.sub_pos_direct strict.2.2.2
  have sixPositive : (0 : Fraction.Rational) < 6 := by decide
  have threePositive : (0 : Fraction.Rational) < 3 := by decide
  have threeRadiusLtSix : 3 * radius < 6 * radius :=
    Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide) radiusPositive
  have scaledGap {gap : Fraction.Rational} (gapPositive : 0 < gap)
      (radiusLe : radius ≤ gap / 6) : 3 * radius < gap := by
    have radiusScaled : radius * 6 ≤ gap :=
      (Field.le_div_iff_pos sixPositive).1 radiusLe
    calc
      3 * radius < 6 * radius := threeRadiusLtSix
      _ = radius * 6 := by ring1
      _ ≤ gap := radiusScaled
  have leftThree := scaledGap leftGapPositive bounds.2.1
  have rightThree := scaledGap rightGapPositive bounds.2.2.1
  have bottomThree := scaledGap bottomGapPositive bounds.2.2.2.1
  have topThree := scaledGap topGapPositive bounds.2.2.2.2.1
  have leftMargin : current.box.xLower + 3 * radius < point.re := by
    have shifted :=
      Arithmetic.add_lt_add_right_direct leftThree
        current.box.xLower
    calc
      current.box.xLower + 3 * radius =
          3 * radius + current.box.xLower := by ring1
      _ < (point.re - current.box.xLower) + current.box.xLower := shifted
      _ = point.re := by ring1
  have rightMargin : point.re + 3 * radius < current.box.xUpper := by
    have shifted :=
      Arithmetic.add_lt_add_right_direct rightThree point.re
    calc
      point.re + 3 * radius = 3 * radius + point.re := by ring1
      _ < (current.box.xUpper - point.re) + point.re := shifted
      _ = current.box.xUpper := by ring1
  have bottomMargin : current.box.yLower + 3 * radius < point.im := by
    have shifted :=
      Arithmetic.add_lt_add_right_direct bottomThree
        current.box.yLower
    calc
      current.box.yLower + 3 * radius =
          3 * radius + current.box.yLower := by ring1
      _ < (point.im - current.box.yLower) + current.box.yLower := shifted
      _ = point.im := by ring1
  have topMargin : point.im + 3 * radius < current.box.yUpper := by
    have shifted :=
      Arithmetic.add_lt_add_right_direct topThree point.im
    calc
      point.im + 3 * radius = 3 * radius + point.im := by ring1
      _ < (current.box.yUpper - point.im) + point.im := shifted
      _ = current.box.yUpper := by ring1
  let lipschitz := Bounds.Box.denseLipschitzBound p current.box
  have lipschitzPositive : 0 < lipschitz :=
    Bounds.Box.denseLipschitzBound_pos p current.box
  have fourLipschitzPositive : 0 < 4 * lipschitz :=
    Arithmetic.mul_pos_direct (by decide) lipschitzPositive
  have thresholdScaled : radius * (4 * lipschitz) ≤
      Squarefree.derivativeThreshold squarefree current.box :=
    (Field.le_div_iff_pos fourLipschitzPositive).1
      bounds.2.2.2.2.2.2.1
  have sourceThreshold : lipschitz * (2 * radius ^ 2) ≤
      Squarefree.derivativeThreshold squarefree current.box := by
    have twoLipschitzNonnegative : 0 ≤ 2 * lipschitz :=
      (Arithmetic.mul_pos_direct (by decide)
        lipschitzPositive).le
    calc
      lipschitz * (2 * radius ^ 2) =
          (2 * lipschitz) * radius ^ 2 := by ring1
      _ ≤ (2 * lipschitz) * radius :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe twoLipschitzNonnegative
      _ ≤ (4 * lipschitz) * radius := by
        have coefficient : 2 * lipschitz ≤ 4 * lipschitz :=
          Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) lipschitzPositive.le
        exact Arithmetic.mul_le_mul_of_nonneg_right_direct
          coefficient radiusPositive.le
      _ = radius * (4 * lipschitz) := by ring1
      _ ≤ Squarefree.derivativeThreshold squarefree current.box := thresholdScaled
  let taylorCoefficient :=
    2 * (Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
      Bounds.Box.Taylor.denseTaylorRemainderBound p current.box)
  have taylorPositive : 0 < taylorCoefficient := by
    have twoPositive : (0 : Fraction.Rational) < 2 := by decide
    have fourPositive : (0 : Fraction.Rational) < 4 := by decide
    have ninePositive : (0 : Fraction.Rational) < 9 := by decide
    have extractionPositive :
        0 < Newton.Box.Band.Parameters.extractionBandTaylorCoefficient := by
      unfold Newton.Box.Band.Parameters.extractionBandTaylorCoefficient
      exact Arithmetic.mul_pos_direct
        (Arithmetic.mul_pos_direct fourPositive ninePositive)
        ninePositive
    exact Arithmetic.mul_pos_direct twoPositive
      (Arithmetic.mul_pos_direct extractionPositive
        (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p current.box))
  have taylorScaled : radius * taylorCoefficient ≤
      Squarefree.derivativeMargin squarefree current.box :=
    (Field.le_div_iff_pos taylorPositive).1
      bounds.2.2.2.2.2.2.2
  have taylorSmall :
      2 * (Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
          Squarefree.derivativeMargin squarefree current.box := by
    calc
      2 * (Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
          Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) =
          taylorCoefficient * radius ^ 2 := by
        dsimp only [taylorCoefficient]
        ring1
      _ ≤ taylorCoefficient * radius :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSquareLe taylorPositive.le
      _ = radius * taylorCoefficient := by ring1
      _ ≤ Squarefree.derivativeMargin squarefree current.box := taylorScaled
  have residualSource : Gaussian.Norm.Basic.normSq (p.eval point) ≤
      lipschitz * (2 * radius ^ 2) :=
    residual.le.trans (Basic.min_le_left _ _)
  have residualDisplacement : Gaussian.Norm.Basic.normSq (p.eval point) /
      Squarefree.derivativeMargin squarefree current.box ≤ radius ^ 2 := by
    have residualMargin : Gaussian.Norm.Basic.normSq (p.eval point) ≤
        Squarefree.derivativeMargin squarefree current.box * radius ^ 2 :=
      residual.le.trans (Basic.min_le_right _ _)
    apply (Field.div_le_iff_pos
      (Squarefree.derivativeMargin_pos squarefree current.box)).2
    calc
      Gaussian.Norm.Basic.normSq (p.eval point) ≤
          Squarefree.derivativeMargin squarefree current.box * radius ^ 2 :=
        residualMargin
      _ = radius ^ 2 * Squarefree.derivativeMargin squarefree current.box := by
        ring1
  exact
    { point := point
      radius := radius
      radiusPositive := radiusPositive
      leftMargin := leftMargin
      rightMargin := rightMargin
      bottomMargin := bottomMargin
      topMargin := topMargin
      residual := by simpa only [lipschitz] using residualSource
      threshold := by simpa only [lipschitz] using sourceThreshold
      displacementBudget := residualDisplacement
      taylorSmall := taylorSmall }

end Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
