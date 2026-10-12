module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Anchored.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
public import Purelib.RootIsolation.Newton.Restart.Anchored.Prepare
public import Purelib.RootIsolation.Newton.Restart.Displacement
public import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Region (ProtectedAmbient)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.Newton.Restart.Anchored.Basic (AnchoredInput)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart.Anchored
namespace Basic.AnchoredInput

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
variable {squarefree : SquarefreeCertificate p}
variable {current : ProtectedAmbient p ambient}

/-- Construct the complete residual seed from the anchored scalar input. -/
def seed
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    Newton.Restart.Seed squarefree elimination current := by
  let source := Box.Square.Anchored.anchoredSquare input.point input.radius
    input.radiusPositive.le
  have sourceRefines : source.Refines current.box := by
    simpa only [source] using input.sourceRefines
  have sourceResidual : Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) ≤
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source := by
    simpa only [source, Box.Square.Anchored.anchoredSquare_anchor,
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound,
      Box.Square.Anchored.anchoredSquare_diagonalSq] using input.residual
  have sourceThreshold : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box := by
    simpa only [source, Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound,
      Box.Square.Anchored.anchoredSquare_diagonalSq] using
      input.threshold
  have sourceDisplacementBudget :
      Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) /
          Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box ≤ input.radius ^ 2 :=
            by
    simpa only [source, Box.Square.Anchored.anchoredSquare_anchor] using
      input.displacementBudget
  let newton := Dense.Gaussian.Newton.Box.Prepare.Squarefree.computeNewtonCenterOfResidual p squarefree sourceRefines
    sourceResidual sourceThreshold
  have displacement :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor)
        ≤
        input.radius ^ 2 :=
    (Newton.Restart.Displacement.newton_displacementResidualMargin newton).trans sourceDisplacementBudget
  have coordinateBounds :=
    Gaussian.Norm.Bounds.coordinate_bounds_of_normSq_le
      input.radiusPositive.le displacement
  have centerRealLower : input.point.re - input.radius ≤
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re := by
    calc
      input.point.re - input.radius = -input.radius + input.point.re := by
        ring1
      _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).re +
          input.point.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct coordinateBounds.1
          input.point.re
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_re]
        ring1
  have centerRealUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re ≤
      input.point.re + input.radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).re +
            input.point.re := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_re]
        ring1
      _ ≤ input.radius + input.point.re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.1 input.point.re
      _ = input.point.re + input.radius := by ring1
  have centerImagLower : input.point.im - input.radius ≤
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im := by
    calc
      input.point.im - input.radius = -input.radius + input.point.im := by
        ring1
      _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).im +
          input.point.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.2.1 input.point.im
      _ = (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_im]
        ring1
  have centerImagUpper : (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im ≤
      input.point.im + input.radius := by
    calc
      (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im =
          (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source - source.anchor).im +
            input.point.im := by
        simp only [source, Box.Square.Anchored.anchoredSquare_anchor, Gaussian.Basic.sub_im]
        ring1
      _ ≤ input.radius + input.point.im :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          coordinateBounds.2.2.2 input.point.im
      _ = input.point.im + input.radius := by ring1
  let band := Elimination.Axis.Band.selectedBand elimination (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p
    source)
    input.radius input.radiusPositive
  have leftPoint : current.box.xLower <
      input.point.re - 3 * input.radius := by
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
      (c := 3 * input.radius)
    calc
      current.box.xLower + 3 * input.radius < input.point.re :=
        input.leftMargin
      _ = (input.point.re - 3 * input.radius) + 3 * input.radius := by
        ring1
  have rightPoint : input.point.re + 3 * input.radius <
      current.box.xUpper := input.rightMargin
  have bottomPoint : current.box.yLower <
      input.point.im - 3 * input.radius := by
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
      (c := 3 * input.radius)
    calc
      current.box.yLower + 3 * input.radius < input.point.im :=
        input.bottomMargin
      _ = (input.point.im - 3 * input.radius) + 3 * input.radius := by
        ring1
  have topPoint : input.point.im + 3 * input.radius <
      current.box.yUpper := input.topMargin
  have bandStrict : band.box.StrictInterior current.box := by
    exact
      { left := by
          calc
            current.box.xLower < input.point.re - 3 * input.radius :=
              leftPoint
            _ = (input.point.re - input.radius) - 2 * input.radius := by
              ring1
            _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re - 2 * input.radius :=
              Fraction.Order.Arithmetic.sub_le_sub_right_direct centerRealLower _
            _ ≤ band.box.xLower := band.left_lower
        right := by
          calc
            band.box.xUpper ≤
                (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).re + 2 * input.radius :=
              band.right_upper
            _ ≤ (input.point.re + input.radius) + 2 * input.radius :=
              Fraction.Order.Arithmetic.add_le_add_right_direct
                centerRealUpper _
            _ = input.point.re + 3 * input.radius := by ring1
            _ < current.box.xUpper := rightPoint
        bottom := by
          calc
            current.box.yLower < input.point.im - 3 * input.radius :=
              bottomPoint
            _ = (input.point.im - input.radius) - 2 * input.radius := by
              ring1
            _ ≤ (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im - 2 * input.radius :=
              Fraction.Order.Arithmetic.sub_le_sub_right_direct centerImagLower _
            _ ≤ band.box.yLower := band.bottom_lower
        top := by
          calc
            band.box.yUpper ≤
                (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source).im + 2 * input.radius :=
              band.top_upper
            _ ≤ (input.point.im + input.radius) + 2 * input.radius :=
              Fraction.Order.Arithmetic.add_le_add_right_direct
                centerImagUpper _
            _ = input.point.im + 3 * input.radius := by ring1
            _ < current.box.yUpper := topPoint }
  exact
    { source := source
      sourceRefines := sourceRefines
      residual := sourceResidual
      threshold := sourceThreshold
      radius := input.radius
      radiusPositive := input.radiusPositive
      displacementBudget := sourceDisplacementBudget
      taylorSmall := input.taylorSmall
      bandStrict := by simpa only [band] using bandStrict }

/-- The constructed residual seed keeps the exact square anchored at the input point and radius. -/
@[simp] theorem seed_source
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    (input.seed elimination).source =
      Box.Square.Anchored.anchoredSquare input.point input.radius input.radiusPositive.le := rfl

/-- The constructed residual seed retains the original anchored input radius. -/
@[simp] theorem seed_radius
    (input : AnchoredInput squarefree current)
    (elimination : AxisEliminationCertificate p degreeBound) :
    (input.seed elimination).radius = input.radius := rfl

end Basic.AnchoredInput

/-- Fully automatic residual seed once the displayed rational point is
strictly inside and its actual residual meets the computed target. -/
def Seed.seedOfResidual
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (strict : current.box.StrictContains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Newton.Restart.Anchored.Budget.anchoredResidualTarget squarefree current point cap) :
    Newton.Restart.Seed squarefree elimination current :=
  (Newton.Restart.Anchored.Prepare.anchoredInputOfResidual squarefree current point strict capPositive
    residual).seed elimination

/-- The automatically prepared residual seed respects the original positive external radius cap. -/
theorem Seed.seedOfResidual_radius_le_cap
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (strict : current.box.StrictContains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Newton.Restart.Anchored.Budget.anchoredResidualTarget squarefree current point cap) :
    (Seed.seedOfResidual squarefree elimination current point strict capPositive
      residual).radius ≤ cap := by
  exact Newton.Restart.Anchored.Budget.anchoredRadius_le_cap squarefree current point cap

end Purelib.RootIsolation.Newton.Restart.Anchored

end
