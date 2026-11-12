module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Extraction.Majorized.Basic
public import Purelib.RootIsolation.Newton.Extraction.Separated.Build
import Purelib.RootIsolation.State.Raw
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Newton.Extraction.Separated.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian.Newton.Box

open scoped Purelib.Data.Nat

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Majorized.Build

/-- Run separated extraction and replace its boundary clearance with the
explicit majorant-based certificate.

The exact separated core and its selected source, Newton point, retained radius,
box and witnesses are reused. The supplied derivative and Taylor majorants
certify the same boundary-clearance readback and predicted lower bound. -/
@[expose] def extractSeparatedMajorized
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (current : State.Raw.RawWindingState p ambient)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (majorants : Majorants.ExtractionMajorants p current.box)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    {epsilon : Fraction.Rational} (epsilonPositive : 0 < epsilon) :
    Basic.MajorizedSeparatedOutput current separation majorants epsilon := by
  let core := Separated.Build.extractSeparated degreeAtLeastTwo current separation elimination
    epsilonPositive
  have radiusLeOne : core.radius ≤ 1 := by
    rw [core.radius_eq]
    exact Budget.Separated.separatedExtractionRadius_le_one separation current.clearance
      epsilon
  have radiusSquareLeOne : core.radius ^ 2 ≤ 1 := by
    calc
      core.radius ^ 2 ≤ (1 : Fraction.Rational) ^ 2 :=
        Arithmetic.pow_le_pow_direct core.radiusPositive.le
          radiusLeOne 2
      _ = 1 := by decide
  have centeredRefines :
      (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p core.source.box)
        core.radius
        core.radiusPositive.le).Refines current.box := by
    rw [← core.box_eq]
    exact (Box.Refinement.StrictInterior.refines core.strictCurrent)
  have linearizationUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary
        (Box.Square.Centered.Affine.centeredSquare (Anchor.anchorNewtonCenter p
          core.source.box) core.radius
          core.radiusPositive.le) z →
      Gaussian.Norm.Basic.normSq ((Linearization.newtonLinearization p
        core.source.box).eval z) ≤
        Budget.Majorants.majorizedLinearizationMajorant majorants := by
    intro z boundary
    have sourceAnchorInside : current.box.Contains core.source.box.anchor :=
      core.source.refinesAmbient.contains core.source.box.contains_anchor
    have derivativeBound := majorants.derivative_upper sourceAnchorInside
    have radial := Box.Square.Centered.centeredSquare_normSq_sub_center_le
      (Anchor.anchorNewtonCenter p core.source.box) core.radiusPositive.le boundary.1
    rw [Linearization.newtonLinearization,
      Dense.Gaussian.Linear.Affine.affineCoordinate_eval, Gaussian.Norm.Basic.normSq_mul]
    calc
      Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval core.source.box.anchor) *
          Gaussian.Norm.Basic.normSq (z - Anchor.anchorNewtonCenter p
            core.source.box) ≤
        majorants.derivative * (2 * core.radius ^ 2) :=
        Arithmetic.mul_le_mul_direct derivativeBound radial
          (Gaussian.Norm.Basic.normSq_nonneg (z - Anchor.anchorNewtonCenter p
            core.source.box))
          majorants.derivative_pos.le
      _ ≤ majorants.derivative * 2 :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusSquareLeOne (by decide)) majorants.derivative_pos.le
      _ = Budget.Majorants.majorizedLinearizationMajorant majorants := by
        unfold Budget.Majorants.majorizedLinearizationMajorant
        ring1
  let centeredClearance :=
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo core.newton core.source.refinesAmbient
      core.radiusPositive centeredRefines core.displacementSmall
      core.taylorSmall (Budget.Majorants.majorizedLinearizationMajorant majorants)
      (Budget.Majorants.majorizedLinearizationMajorant_pos majorants) linearizationUpper
  let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p core.box := by
    rw [core.box_eq]
    exact centeredClearance
  have clearanceBound : clearance.bound =
      Square.Separated.separatedNewtonDominanceMargin separation
          core.radius ^ 2 /
        (8 * majorants.derivative) := by
    change centeredClearance.bound = _
    rw [Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant_bound]
    have denominatorIdentity :
        (4 : Fraction.Rational) * Budget.Majorants.majorizedLinearizationMajorant majorants =
          8 * majorants.derivative := by
      unfold Budget.Majorants.majorizedLinearizationMajorant
      ring1
    rw [denominatorIdentity]
  let predictedRadius := Budget.Majorants.majorizedExtractionRadius separation
    current.clearance
    majorants epsilon
  have predictedRadiusPositive : 0 < predictedRadius :=
    Budget.Majorants.majorizedExtractionRadius_pos separation current.clearance majorants
      current.proper epsilonPositive
  have predictedRadiusLe : predictedRadius ≤ core.radius := by
    rw [core.radius_eq]
    exact Budget.Majorants.majorizedExtractionRadius_le separation current.clearance
      majorants epsilon
  have predictedSquareLe : predictedRadius ^ 2 ≤ core.radius ^ 2 :=
    Arithmetic.pow_le_pow_direct predictedRadiusPositive.le
      predictedRadiusLe 2
  let actualBase :=
    36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * core.radius ^ 2
  have errorHalf : Square.Bounds.newtonErrorBudget p current.box
      core.radius ≤ separation.margin * core.radius ^ 2 / 2 := by
    apply (Field.le_div_iff_pos
      (show (0 : Fraction.Rational) < 2 by decide)).mpr
    have scaledTaylor :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        core.taylorSmall
        (Arithmetic.sq_nonneg_direct core.radius)
    calc
      Square.Bounds.newtonErrorBudget p current.box core.radius * 2 =
          (2 * actualBase) * core.radius ^ 2 := by
        unfold Square.Bounds.newtonErrorBudget
        dsimp only [actualBase]
        ring1
      _ ≤ separation.margin * core.radius ^ 2 := scaledTaylor
  have halfMarginLe : separation.margin * core.radius ^ 2 / 2 ≤
      Square.Separated.separatedNewtonDominanceMargin separation
        core.radius := by
    unfold Square.Separated.separatedNewtonDominanceMargin
    apply Arithmetic.le_of_sub_nonneg_direct
    have totalBound : separation.margin * core.radius ^ 2 / 2 +
        Square.Bounds.newtonErrorBudget p current.box core.radius ≤
        separation.margin * core.radius ^ 2 := by
      have halfIdentity : separation.margin * core.radius ^ 2 / 2 +
          separation.margin * core.radius ^ 2 / 2 =
            separation.margin * core.radius ^ 2 :=
        Fraction.Field.two_halves _
      calc
        separation.margin * core.radius ^ 2 / 2 +
            Square.Bounds.newtonErrorBudget p current.box core.radius ≤
            separation.margin * core.radius ^ 2 / 2 +
            separation.margin * core.radius ^ 2 / 2 :=
          Arithmetic.add_le_add_direct le_rfl errorHalf
        _ = separation.margin * core.radius ^ 2 := halfIdentity
    have nonnegative := Arithmetic.sub_nonneg_direct totalBound
    have scalarIdentity :
        (separation.margin * core.radius ^ 2 -
          Square.Bounds.newtonErrorBudget p current.box core.radius) -
            separation.margin * core.radius ^ 2 / 2 =
          separation.margin * core.radius ^ 2 -
            (separation.margin * core.radius ^ 2 / 2 +
              Square.Bounds.newtonErrorBudget p current.box core.radius) := by
      ring1
    rw [scalarIdentity]
    exact nonnegative
  have predictedMarginLe : separation.margin * predictedRadius ^ 2 / 2 ≤
      Square.Separated.separatedNewtonDominanceMargin separation
        core.radius := by
    have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
      predictedSquareLe separation.margin_pos.le
    have divided : separation.margin * predictedRadius ^ 2 / 2 ≤
        separation.margin * core.radius ^ 2 / 2 := by
      change (separation.margin * predictedRadius ^ 2) *
          (2 : Fraction.Rational)⁻¹ ≤
        (separation.margin * core.radius ^ 2) * (2 : Fraction.Rational)⁻¹
      exact Arithmetic.mul_le_mul_of_nonneg_right_direct scaled
        (Field.inv_pos_direct
          (show (0 : Fraction.Rational) < 2 by decide)).le
    exact divided.trans halfMarginLe
  have actualMarginPositive :=
    Square.Separated.separatedNewtonDominanceMargin_pos separation
      core.radiusPositive core.taylorSmall
  have marginSquareLe := Arithmetic.pow_le_pow_direct
    (Field.div_pos_direct
      (Arithmetic.mul_pos_direct separation.margin_pos
        (Arithmetic.pow_pos_direct predictedRadiusPositive 2))
      (by decide)).le predictedMarginLe 2
  have denominatorPositive : 0 < (8 : Fraction.Rational) * majorants.derivative :=
    Arithmetic.mul_pos_direct (by decide)
      majorants.derivative_pos
  have predictedClearanceLe :
      Budget.Majorants.predictedExtractionClearance separation current.clearance majorants
          epsilon ≤ clearance.bound := by
    rw [clearanceBound]
    unfold Budget.Majorants.predictedExtractionClearance
    change _ * ((8 : Fraction.Rational) * majorants.derivative)⁻¹ ≤
      _ * ((8 : Fraction.Rational) * majorants.derivative)⁻¹
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct
      marginSquareLe
      (Field.inv_pos_direct denominatorPositive).le
  exact
    { core := core
      clearance := clearance
      clearance_bound := clearanceBound
      predicted_clearance_le := predictedClearanceLe }

end Purelib.RootIsolation.Newton.Extraction.Majorized.Build

end
