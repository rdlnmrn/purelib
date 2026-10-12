module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Square.Centered.Interior
public import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Squarefree
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Prepare.Squarefree
public import Purelib.Polynomial.Winding.Box.Newton.Square.Squarefree
public import Purelib.Polynomial.Winding.Box.ProtectedBoundary
public import Purelib.RootIsolation.Newton.Extraction.Basic
public import Purelib.RootIsolation.Newton.Extraction.Source
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
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original Newton source selection from checked safe-subdivision
stages, then reuse that source in the unchanged local extraction construction.
The source ownership equation is exact, including its boundary bound. -/
namespace Purelib.RootIsolation.Newton.Extraction.Prepare

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)

/-- Construct the original checked Newton square from a retained raw-subdivision source.

The saved source threshold supplies derivative, displacement and protected-boundary bounds; the exact Newton center and
radius give strict containment, winding four, boundary clearance and the requested diagonal accuracy. -/
def fromSource
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon)
    (sourceData : Newton.Extraction.Source.SourceOutput squarefree current epsilon) : Newton.Extraction.Basic.Output
      squarefree current epsilon := by
  let source := sourceData.source
  let r := Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius squarefree current.box current.clearance epsilon
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance
  let lipschitz := Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box
  let eta := Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  have radiusPositive : 0 < r :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_pos squarefree current.clearance current.proper
      epsilonPositive
  have rhoPositive : 0 < rho :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p current.clearance current.proper
  have lipschitzPositive : 0 < lipschitz :=
    Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box
  have etaPositive : 0 < eta := Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree
    current.box
  have sourceDiagonal := sourceData.diagonalSq_le
  have sourceProtected : source.box.diagonalSq ≤ rho ^ 2 :=
    sourceDiagonal.trans
      (Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold_le_protected squarefree current.box
        current.clearance epsilon)
  have sourceDerivative : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box := by
    have thresholdBound := Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold_le_derivative squarefree
      current.box current.clearance epsilon
    have scaledThreshold :
        Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
          epsilon *
            lipschitz ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box :=
      (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz *
          Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon * lipschitz := by ring1
      _ ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box := scaledThreshold
  let newton := Winding.Box.Newton.Prepare.Squarefree.computeNewtonCenterOfRawWinding p degreePositive squarefree
    source.refinesAmbient source.proper source.rawWinding_ne sourceDerivative
  have residualDisplacement : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box ≤
      eta * r ^ 2 := by
    have thresholdBound := Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold_le_displacement
      squarefree
      current.box current.clearance epsilon
    have scaledThreshold :
        Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
          epsilon *
            lipschitz ≤ eta * r ^ 2 :=
      (Fraction.Order.Field.le_div_iff_pos lipschitzPositive).mp
        thresholdBound
    calc
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box =
          lipschitz * source.box.diagonalSq := rfl
      _ ≤ lipschitz *
          Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          sourceDiagonal lipschitzPositive.le
      _ = Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance
            epsilon * lipschitz := by ring1
      _ ≤ eta * r ^ 2 := scaledThreshold
  have displacementSmall :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤ r ^ 2 := by
    calc
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box -
        source.box.anchor) ≤
          Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box / eta :=
        newton.displacementMargin
      _ ≤ r ^ 2 :=
        (Fraction.Order.Field.div_le_iff_pos etaPositive).mpr (by
          calc
            Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source.box ≤ eta * r ^ 2 :=
              residualDisplacement
            _ = r ^ 2 * eta := by ring1)
  have stripBounds := Winding.Box.ProtectedBoundary.strictly_inside_protectedBoundary
    (p := p) degreePositive current.clearance current.proper source.proper
      source.refinesAmbient source.rawWinding_ne sourceProtected
  have radiusLeRho : r ≤ rho :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_le_protected squarefree current.box current.clearance
      epsilon
  let target := Box.Square.Centered.Affine.centeredSquare (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p
    source.box) r
    radiusPositive.le
  have targetStrict : target.StrictInterior current.box :=
    Box.Square.Centered.Interior.centeredSquare_strictInterior radiusPositive radiusLeRho stripBounds
      displacementSmall
  have targetRefinesCurrent : target.Refines current.box :=
    Geometry.Rational.Box.Refinement.StrictInterior.refines targetStrict
  have targetRefinesAmbient : target.Refines ambient :=
    targetRefinesCurrent.trans current.refinesAmbient
  have bandTaylorSmall :
      2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_taylor squarefree current.clearance current.proper
      epsilonPositive
  have taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box := by
    have remainderNonnegative :
        0 ≤ Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2 :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p current.box).le
        (Fraction.Order.Arithmetic.sq_nonneg_direct r)
    have smallBlockNonnegative :
        0 ≤ ((4 : Fraction.Rational) * 9) *
          (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_pos_direct
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by decide))
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 9) (by decide))).le
        remainderNonnegative
    have smallBlockLe :
        ((4 : Fraction.Rational) * 9) *
            (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) ≤
          9 * (((4 : Fraction.Rational) * 9) *
            (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2)) := by
      calc
        ((4 : Fraction.Rational) * 9) *
            (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) =
            1 * (((4 : Fraction.Rational) * 9) *
              (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2)) := by ring1
        _ ≤ 9 * (((4 : Fraction.Rational) * 9) *
              (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2)) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Fraction.Cast.Order.natCast_le_direct
              (m := 1) (n := 9) (by decide)) smallBlockNonnegative
    have twoNonnegative : (0 : Fraction.Rational) ≤ 2 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 2) (by decide)).le
    calc
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) =
          2 * (((4 : Fraction.Rational) * 9) *
            (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2)) := by ring1
      _ ≤ 2 * (9 * (((4 : Fraction.Rational) * 9) *
            (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2))) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          smallBlockLe twoNonnegative
      _ = 2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
            Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * r ^ 2) := by
        unfold Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient
        ring1
      _ ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box := bandTaylorSmall
  have windingFour : Winding.Box.Basic.quadrupledBoxWinding p target = 4 :=
    Winding.Box.Newton.Square.Squarefree.quadrupledBoxWinding_eq_four_of_newtonSquare degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have targetClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p target :=
    Clearance.Box.Boundary.Newton.Square.Squarefree.newtonSquareBoundaryClearance degreeAtLeastTwo newton
      source.refinesAmbient radiusPositive targetRefinesCurrent
      displacementSmall taylorSmall
  have radiusEighth : r ≤ (1 / 8 : Fraction.Rational) * epsilon :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_le_eighth squarefree current.box current.clearance
      epsilon
  have squareBound : r ^ 2 ≤ ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusEighth 2
  have epsilonSquareNonnegative :=
    Fraction.Order.Arithmetic.sq_nonneg_direct epsilon
  have eighthSquare : (1 / 8 : Fraction.Rational) * epsilon ^ 2 ≤ epsilon ^ 2 := by
    calc
      (1 / 8 : Fraction.Rational) * epsilon ^ 2 ≤ 1 * epsilon ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) epsilonSquareNonnegative
      _ = epsilon ^ 2 := by ring1
  have targetDiagonal : target.diagonalSq ≤ epsilon ^ 2 := by
    have coefficientIdentity :
        (8 : Fraction.Rational) * (1 / 8) ^ 2 = 1 / 8 := by decide
    calc
      target.diagonalSq = 8 * r ^ 2 :=
        Box.Square.Centered.Affine.centeredSquare_diagonalSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p
          source.box)
          radiusPositive.le
      _ ≤ 8 * ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareBound
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 8) (by decide)).le
      _ = (8 * (1 / 8 : Fraction.Rational) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 8 : Fraction.Rational) * epsilon ^ 2 := by
        rw [coefficientIdentity]
      _ ≤ epsilon ^ 2 := eighthSquare
  exact
    { source := source
      radius := r
      radiusPositive := radiusPositive
      newton := newton
      displacementSmall := displacementSmall
      stripBounds := stripBounds
      bandTaylorSmall := bandTaylorSmall
      box := target
      box_eq := rfl
      strictCurrent := targetStrict
      refinesAmbient := targetRefinesAmbient
      proper := Box.Square.Centered.centeredSquare_proper (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p
        source.box)
        radiusPositive
      clearance := targetClearance
      rawWindingFour := windingFour
      diagonalSq_le := targetDiagonal }
end Purelib.RootIsolation.Newton.Extraction.Prepare

end
