module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Square.Anchored
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Separated Newton restart data

A retained source box, derivative separation and positive radius certify the
Newton displacement and a centered square strictly inside the original ambient.
-/

public section

namespace Purelib.RootIsolation.Newton.Restart.Separated.Basic

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-! ## Direct restarts from an explicit derivative separation -/

set_option genInjectivity false in
/-- Retain the finite data certifying a separated Newton restart.

The original source box and supplied derivative separation certify its
residual and Newton displacement. The positive radius gives a centered target
strictly inside the ambient box and pays its doubled Taylor budget. -/
structure SeparatedRestartInput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient) where
  /-- The retained source box supplying the rational anchor. -/ source : Box
  /-- The retained source box refines the original ambient box. -/ sourceRefines : source.Refines ambient
  /-- The source anchor's squared residual norm is bounded by its whole-box variation budget. -/ residual :
    Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) <=
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient source
  /-- The actual squared residual is below the supplied derivative-separation threshold. -/ threshold :
    Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) <= separation.threshold
  /-- The retained radius of the predictable centered target square. -/ radius : Fraction.Rational
  /-- The retained target radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The actual squared residual divided by the retained derivative margin fits within the squared radius. -/
    displacementBudget :
    Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) / separation.margin <= radius ^ 2
  /-- The exact square centered at the Newton update lies strictly inside the original ambient box. -/ targetStrict :
    (Box.Square.Centered.Affine.centeredSquare
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) radius radiusPositive.le).StrictInterior
        ambient
  /-- The target radius makes the Taylor remainder budget fit the supplied derivative margin. -/ taylorSmall :
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * radius ^ 2) <=
      separation.margin

constructive_injectivity SeparatedRestartInput

namespace SeparatedRestartInput

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}

open Purelib.RootIsolation
/-- Build a separated restart from one rational anchor and doubled radius margins.

The original anchor and radius determine the source square. One radius pays
for the Newton displacement and the other for the centered target square;
all supplied residual, threshold and Taylor certificates are retained. -/
@[expose] def ofAnchored
    (point : Gaussian.Basic.Canonical) (radius : Fraction.Rational) (radiusPositive : 0 < radius)
    (leftMargin : ambient.xLower + 2 * radius < point.re)
    (rightMargin : point.re + 2 * radius < ambient.xUpper)
    (bottomMargin : ambient.yLower + 2 * radius < point.im)
    (topMargin : point.im + 2 * radius < ambient.yUpper)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <=
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient * (2 * radius ^ 2))
    (threshold : Data.Gaussian.Norm.Basic.normSq (p.eval point) <= separation.threshold)
    (displacementBudget : Data.Gaussian.Norm.Basic.normSq (p.eval point) / separation.margin <=
      radius ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * radius ^ 2) <=
        separation.margin) :
    Newton.Restart.Separated.Basic.SeparatedRestartInput separation := by
  let source := Box.Square.Anchored.anchoredSquare point radius radiusPositive.le
  have radiusLeTwo : radius <= 2 * radius := by
    calc
      radius = 0 + radius := by ring1
      _ <= radius + radius :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          radiusPositive.le radius
      _ = 2 * radius := by ring1
  have twiceRadiusPositive : 0 < 2 * radius :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) radiusPositive
  have sourceRefines : source.Refines ambient := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have beforeMargin : ambient.xLower < ambient.xLower + 2 * radius := by
        calc
          ambient.xLower = 0 + ambient.xLower := by ring1
          _ < 2 * radius + ambient.xLower :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct
              twiceRadiusPositive ambient.xLower
          _ = ambient.xLower + 2 * radius := by ring1
      exact (beforeMargin.trans leftMargin).le
    · change point.re + radius <= ambient.xUpper
      exact (calc
        point.re + radius <= point.re + 2 * radius := by
          rw [Fraction.Field.add_comm point.re radius,
            Fraction.Field.add_comm point.re (2 * radius)]
          exact Fraction.Order.Arithmetic.add_le_add_right_direct radiusLeTwo
            point.re
        _ < ambient.xUpper := rightMargin).le
    · have beforeMargin : ambient.yLower < ambient.yLower + 2 * radius := by
        calc
          ambient.yLower = 0 + ambient.yLower := by ring1
          _ < 2 * radius + ambient.yLower :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct
              twiceRadiusPositive ambient.yLower
          _ = ambient.yLower + 2 * radius := by ring1
      exact (beforeMargin.trans bottomMargin).le
    · change point.im + radius <= ambient.yUpper
      exact (calc
        point.im + radius <= point.im + 2 * radius := by
          rw [Fraction.Field.add_comm point.im radius,
            Fraction.Field.add_comm point.im (2 * radius)]
          exact Fraction.Order.Arithmetic.add_le_add_right_direct radiusLeTwo
            point.im
        _ < ambient.yUpper := topMargin).le
  have sourceResidual : Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) <=
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient source := by
    simpa only [source, Box.Square.Anchored.anchoredSquare_anchor,
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound,
      Box.Square.Anchored.anchoredSquare_diagonalSq] using residual
  have sourceThreshold : Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) <=
      separation.threshold := by
    simpa only [source, Box.Square.Anchored.anchoredSquare_anchor] using threshold
  have sourceDisplacementBudget :
      Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) / separation.margin <=
        radius ^ 2 := by
    simpa only [source, Box.Square.Anchored.anchoredSquare_anchor] using displacementBudget
  let newton :=
    Dense.Gaussian.Newton.Box.Prepare.computeNewtonCenterOfPointResidualSeparated p separation
      sourceRefines sourceResidual sourceThreshold
  have displacement :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
        <= radius ^ 2 := by
    have derivativeNormPositive :
        0 < Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval source.anchor) :=
      Gaussian.Norm.Basic.normSq_pos newton.derivativeNonzero
    have inverseBound :
        (Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.GCD.derivative p).eval source.anchor))⁻¹ <=
            separation.margin⁻¹ :=
      Fraction.Order.Field.inv_le_inv_of_pos_direct
        separation.margin_pos newton.derivativeLower
    rw [Dense.Gaussian.Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor
      newton.derivativeNonzero]
    calc
      Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) *
            (Data.Gaussian.Norm.Basic.normSq
              ((Dense.Gaussian.GCD.derivative p).eval source.anchor))⁻¹ <=
          Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) * separation.margin⁻¹ :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound
          (Gaussian.Norm.Basic.normSq_nonneg _)
      _ = Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) / separation.margin := rfl
      _ <= radius ^ 2 := sourceDisplacementBudget
  have coordinateBounds :=
    Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le radiusPositive.le
      displacement
  have centerRealLower : point.re - radius <=
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re := by
    calc
      point.re - radius = -radius + point.re := by ring1
      _ <= (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).re + point.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct coordinateBounds.1
          point.re
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_re]
        ring1
  have centerRealUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re <=
      point.re + radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).re + point.re := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_re]
        ring1
      _ <= radius + point.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.1 point.re
      _ = point.re + radius := by ring1
  have centerImagLower : point.im - radius <=
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im := by
    calc
      point.im - radius = -radius + point.im := by ring1
      _ <= (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).im + point.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.2.1 point.im
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_im]
        ring1
  have centerImagUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im <=
      point.im + radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).im + point.im := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_im]
        ring1
      _ <= radius + point.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.2.2 point.im
      _ = point.im + radius := by ring1
  have targetStrict :
      (Box.Square.Centered.Affine.centeredSquare
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source) radius radiusPositive.le).StrictInterior
          ambient := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ambient.xLower < (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re - radius
      exact (calc
        ambient.xLower < point.re - 2 * radius := by
          apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
            (c := 2 * radius)
          simpa only [show (point.re - 2 * radius) + 2 * radius = point.re by
            ring1] using leftMargin
        _ = (point.re - radius) - radius := by ring1
        _ <= (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re - radius :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct centerRealLower _)
    · change (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re + radius < ambient.xUpper
      exact (calc
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re + radius <=
            (point.re + radius) + radius :=
          Fraction.Order.Arithmetic.add_le_add_right_direct centerRealUpper _
        _ = point.re + 2 * radius := by ring1
        _ < ambient.xUpper := rightMargin)
    · change ambient.yLower < (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im - radius
      exact (calc
        ambient.yLower < point.im - 2 * radius := by
          apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
            (c := 2 * radius)
          simpa only [show (point.im - 2 * radius) + 2 * radius = point.im by
            ring1] using bottomMargin
        _ = (point.im - radius) - radius := by ring1
        _ <= (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im - radius :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct centerImagLower _)
    · change (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im + radius < ambient.yUpper
      exact (calc
        (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im + radius <=
            (point.im + radius) + radius :=
          Fraction.Order.Arithmetic.add_le_add_right_direct centerImagUpper _
        _ = point.im + 2 * radius := by ring1
        _ < ambient.yUpper := topMargin)
  exact
    { source := source
      sourceRefines := sourceRefines
      residual := sourceResidual
      threshold := sourceThreshold
      radius := radius
      radiusPositive := radiusPositive
      displacementBudget := sourceDisplacementBudget
      targetStrict := targetStrict
      taylorSmall := taylorSmall }

/-- Compute the separated Newton certificate from the retained source box.

The source refinement, residual and threshold certificates are supplied to
the original derivative-separated Newton procedure. -/
@[expose] def newton (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate
      p ambient input.source separation :=
  Dense.Gaussian.Newton.Box.Prepare.computeNewtonCenterOfPointResidualSeparated p separation
    input.sourceRefines input.residual input.threshold

/-- The supplied displacement budget controls the computed Newton center. -/
theorem displacementSmall (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
    Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p input.source -
      input.source.anchor) <=
      input.radius ^ 2 := by
  have derivativeNormPositive :
      0 < Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.GCD.derivative p).eval input.source.anchor) :=
    Gaussian.Norm.Basic.normSq_pos input.newton.derivativeNonzero
  have inverseBound :
      (Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.GCD.derivative p).eval input.source.anchor))⁻¹ <=
          separation.margin⁻¹ :=
    Fraction.Order.Field.inv_le_inv_of_pos_direct
      separation.margin_pos input.newton.derivativeLower
  rw [Dense.Gaussian.Newton.Box.Anchor.normSq_anchorNewtonCenter_sub_anchor
    input.newton.derivativeNonzero]
  calc
    Data.Gaussian.Norm.Basic.normSq (p.eval input.source.anchor) *
          (Data.Gaussian.Norm.Basic.normSq
            ((Dense.Gaussian.GCD.derivative p).eval
              input.source.anchor))⁻¹ <=
        Data.Gaussian.Norm.Basic.normSq (p.eval input.source.anchor) * separation.margin⁻¹ :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound
        (Gaussian.Norm.Basic.normSq_nonneg _)
    _ = Data.Gaussian.Norm.Basic.normSq (p.eval input.source.anchor) / separation.margin := rfl
    _ <= input.radius ^ 2 := input.displacementBudget

/-- Form the centered target square of the retained separated restart.

Its center is the original anchor Newton update and its radius is the exact
positive radius retained in the input. -/
@[expose] def centeredBox (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
  Box :=
  Box.Square.Centered.Affine.centeredSquare
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p input.source) input.radius input.radiusPositive.le

/-- The predictable Newton-centered square refines the original ambient box. -/
theorem centeredBox_refines (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
    input.centeredBox.Refines ambient :=
  Geometry.Rational.Box.Refinement.StrictInterior.refines input.targetStrict

/-- The predictable restart square retains the strict margins supplied by
`ofAnchored`. -/
theorem centeredBox_strict (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
    input.centeredBox.StrictInterior ambient :=
  input.targetStrict

/-- The predictable target square has squared diagonal eight times the squared radius. -/
@[simp] theorem centeredBox_diagonalSq
    (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation) :
    input.centeredBox.diagonalSq = 8 * input.radius ^ 2 :=
  Box.Square.Centered.Affine.centeredSquare_diagonalSq _ input.radiusPositive.le
end SeparatedRestartInput

end Purelib.RootIsolation.Newton.Restart.Separated.Basic
