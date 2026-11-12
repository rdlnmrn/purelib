module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Prepare
public import Purelib.Polynomial.Winding.Box.Newton.Square.Separated
public import Purelib.Polynomial.Winding.Box.ProtectedBoundary
public import Purelib.RootIsolation.Newton.Extraction.Separated.Basic
public import Purelib.RootIsolation.Newton.Extraction.Separated.Source
import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Dense.Gaussian.Newton.Box

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Separated.Build

/-- Complete finite local extraction driven by explicit derivative
separation. -/
def extractSeparated
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (epsilonPositive : 0 < epsilon) :
    Basic.SeparatedOutput current separation epsilon := by
  let sourceData := Source.selectSeparatedSource current separation elimination
    epsilonPositive
  let source := sourceData.source
  let r := Budget.Separated.separatedExtractionRadius separation current.box
    current.clearance epsilon
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    Budget.Separated.separatedExtractionRadius_pos separation current.clearance current.proper
      epsilonPositive
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box
  have sourceDiagonal := sourceData.diagonalSq_le
  have sourceProtected : source.box.diagonalSq ≤ rho ^ 2 :=
    sourceDiagonal.trans
      (Budget.Separated.separatedSourceDiagonalThreshold_le_protected separation
        current.clearance epsilon)
  have sourceDerivative : Residual.anchorResidualBound p current.box source.box ≤
      separation.threshold := by
    have thresholdBound := Budget.Separated.separatedSourceDiagonalThreshold_le_derivative
      separation current.clearance epsilon
    have scaledThreshold :
        Budget.Separated.separatedSourceDiagonalThreshold separation current.box
            current.clearance epsilon * lipschitz ≤ separation.threshold :=
      (Field.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      Residual.anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz * Budget.Separated.separatedSourceDiagonalThreshold separation
          current.box current.clearance epsilon :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = Budget.Separated.separatedSourceDiagonalThreshold separation current.box
          current.clearance epsilon * lipschitz := by ring1
      _ ≤ separation.threshold := scaledThreshold
  let newton := Winding.Box.Newton.Prepare.computeNewtonCenterOfRawWindingSeparated p degreePositive
    separation source.refinesAmbient source.proper source.rawWinding_ne
      sourceDerivative
  have residualDisplacement :
      Residual.anchorResidualBound p current.box source.box ≤
        separation.margin * r ^ 2 := by
    have thresholdBound := Budget.Separated.separatedSourceDiagonalThreshold_le_displacement
      separation current.clearance epsilon
    have scaledThreshold :
        Budget.Separated.separatedSourceDiagonalThreshold separation current.box
            current.clearance epsilon * lipschitz ≤
          separation.margin * r ^ 2 :=
      (Field.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      Residual.anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz * Budget.Separated.separatedSourceDiagonalThreshold separation
          current.box current.clearance epsilon :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = Budget.Separated.separatedSourceDiagonalThreshold separation current.box
          current.clearance epsilon * lipschitz := by ring1
      _ ≤ separation.margin * r ^ 2 := scaledThreshold
  have displacementSmall :
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    calc
      Gaussian.Norm.Basic.normSq (Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤
          Residual.anchorResidualBound p current.box source.box / separation.margin :=
        newton.displacementMargin
      _ ≤ r ^ 2 :=
        (Field.div_le_iff_pos separation.margin_pos).mpr
          (by
            calc
              Residual.anchorResidualBound p current.box source.box ≤
                  separation.margin * r ^ 2 := residualDisplacement
              _ = r ^ 2 * separation.margin := by ring1)
  have stripBounds := Winding.Box.ProtectedBoundary.strictly_inside_protectedBoundary
    (p := p) degreePositive current.clearance current.proper source.proper
      source.refinesAmbient source.rawWinding_ne sourceProtected
  have radiusLeRho : r ≤ rho :=
    Budget.Separated.separatedExtractionRadius_le_protected separation current.clearance
      epsilon
  let target := Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p
    source.box) r
    radiusPositive.le
  have targetStrict : target.StrictInterior current.box :=
    Box.Square.Centered.Interior.centeredSquare_strictInterior radiusPositive radiusLeRho stripBounds
      displacementSmall
  have targetRefinesCurrent : target.Refines current.box :=
    Box.Refinement.StrictInterior.refines targetStrict
  have targetRefinesAmbient : target.Refines ambient :=
    targetRefinesCurrent.trans current.refinesAmbient
  have taylorSmall :
      2 * (36 * Taylor.denseTaylorRemainderBound p current.box * r ^ 2) ≤
        separation.margin :=
    Budget.Separated.separatedExtractionRadius_taylor separation current.clearance
      current.proper epsilonPositive
  have windingFour : Winding.Box.Basic.quadrupledBoxWinding p target = 4 :=
    Winding.Box.Newton.Square.Separated.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare degreeAtLeastTwo
      newton source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  let targetClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p target :=
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearance degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have targetClearanceBound : targetClearance.bound =
      Square.Separated.separatedNewtonDominanceMargin separation r ^ 2 /
        (4 * Square.Bounds.separatedNewtonLinearizationMajorant
          p current.box r) := rfl
  have radiusEighth : r ≤ (1 / 8 : Fraction.Rational) * epsilon :=
    Budget.Separated.separatedExtractionRadius_le_eighth separation current.clearance epsilon
  have squareBound : r ^ 2 ≤ ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
    Arithmetic.pow_le_pow_direct radiusPositive.le radiusEighth 2
  have epsilonSquareNonnegative :=
    Arithmetic.sq_nonneg_direct epsilon
  have targetDiagonal : target.diagonalSq ≤ epsilon ^ 2 := by
    have coefficientIdentity :
        (8 : Fraction.Rational) * (1 / 8) ^ 2 = 1 / 8 := by decide
    calc
      target.diagonalSq = 8 * r ^ 2 :=
        Box.Square.Centered.Affine.centeredSquare_diagonalSq (Anchor.anchorNewtonCenter p
          source.box)
          radiusPositive.le
      _ ≤ 8 * ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct squareBound
          (by decide)
      _ = (8 * (1 / 8 : Fraction.Rational) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 8 : Fraction.Rational) * epsilon ^ 2 := by rw [coefficientIdentity]
      _ ≤ 1 * epsilon ^ 2 :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 / 8 : Fraction.Rational) ≤ 1 by decide)
          epsilonSquareNonnegative
      _ = epsilon ^ 2 := _root_.one_mul _
  exact
    { source := source
      radius := r
      radius_eq := rfl
      radiusPositive := radiusPositive
      newton := newton
      displacementSmall := displacementSmall
      taylorSmall := taylorSmall
      box := target
      box_eq := rfl
      strictCurrent := targetStrict
      refinesAmbient := targetRefinesAmbient
      proper := Box.Square.Centered.centeredSquare_proper (Anchor.anchorNewtonCenter p
        source.box)
        radiusPositive
      clearance := targetClearance
      clearance_bound := targetClearanceBound
      rawWindingFour := windingFour
      diagonalSq_le := targetDiagonal }
end Purelib.RootIsolation.Newton.Extraction.Separated.Build

end
