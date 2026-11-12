module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Cells
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Interval.Radius
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Residual-controlled numerical refinement of the original waist

The supplied original lift and its cached root process remain unchanged.
A requested finite square residual selects a retained process state and one
actual reading. The original signed seed box controls root differences
through radicand movement and both residuals, so local allowances shrink
with the chart width and requested accuracy.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {quarter : UnitCircuitQuarter} {regular : parameter ≠ criticalValue site}
variable {bound : normSq (parameter - criticalValue site) ≤ (1 / 16 : Fraction.Rational)}
variable {span : Interval.Bounds}
variable {unit : Owner ((unitPolynomial site).eval
  (point site parameter (direction quarter span.lower) regular bound).base)}

/-- Select an actual cached-name state and reading meeting the requested positive finite square-residual bound.

The original complete process equality transports the prepared state back to
the supplied lift's cached channel. Sampling executes that exact channel;
the retained model includes the same process state and actual witness.
-/
@[expose] def sample (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit)
    (target : Fraction.Rational) (positive : 0 < target) :
    { reading : Cells.Model data simple lift //
      normSq (reading.centerRoot * reading.centerRoot - (unitPolynomial site).eval
        (point site parameter (direction quarter span.lower) regular bound).base) < target } := by
  let original := (lift.unitOwner.certificate lift.unitOwner.parameterNonzero).value.name.process
  have ownerEq : original = lift.unitRoot.value.name.process := by
    rewrite [lift.unitRoot_eq]
    rfl
  let rawState := CertifiedSquareRoot.residualState lift.unitOwner.parameterNonzero lift.unitOwner.track target positive
  let state := Process.Sampling.castState ownerEq rawState
  let reading := Cells.Model.ofState data simple lift state 0
  have possible := Process.Sampling.witnessAt_possible_start original rawState 0
  have residual := CertifiedSquareRoot.residualState_candidate_residual_lt lift.unitOwner.parameterNonzero
    lift.unitOwner.track target positive possible
  have centerEq : reading.centerRoot = Process.Sampling.witnessAt original rawState 0 :=
    Process.Sampling.witnessAt_castState ownerEq rawState 0
  have accurate : normSq (reading.centerRoot * reading.centerRoot - (unitPolynomial site).eval
      (point site parameter (direction quarter span.lower) regular bound).base) < target := by
    rewrite [centerEq, Norm.Basic.normSq_eq_canonical]
    exact residual
  exact ⟨reading, accurate⟩

set_option genInjectivity false in
/-- One residual-controlled constant cell with its original retained lift, reading and signed window.

The accuracy request and its payment remain attached to the actual reading.
The allowance separately accounts for original chart width and both possible
square residuals, rather than the fixed signed box's full diagonal.
-/
structure Cell (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit)
    (accuracy : Fraction.Rational) where
  /-- The requested finite square-residual accuracy is positive. -/
  positive : 0 < accuracy
  /-- The actual retained original-process reading. -/
  reading : Cells.Model data simple lift
  /-- The original process reading pays this exact accuracy request. -/
  accurate : normSq (reading.centerRoot * reading.centerRoot - (unitPolynomial site).eval
    (point site parameter (direction quarter span.lower) regular bound).base) < accuracy
  /-- The retained original window selects the same signed cofactor occurrence. -/
  signed : reading.rootBox.Refines (UnitRoot.box site)
  /-- The computed uniform local squared-error allowance. -/
  allowance : Fraction.Rational
  /-- The allowance pays original chart movement and two requested square residuals. -/
  allowance_eq : allowance = data.chartSlope * (span.upper - span.lower) ^ 2 + 2 * data.residualSlope * accuracy
  /-- The computed local allowance is nonnegative. -/
  allowance_nonnegative : 0 ≤ allowance

constructive_injectivity Cell

namespace Cell

open Purelib.Data.Rat.Fraction.Order

/-- Prepare a requested actual cofactor reading and derive its residual-controlled constant cell allowance. -/
@[expose] def build (data : Bounds.Data site parameter differential) (simple : differential.denominatorPairs = 0)
    (lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit)
    (signed : lift.unitOwner.track.initial.box.Refines (UnitRoot.box site))
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) : Cell data simple lift accuracy := by
  let observed := sample data simple lift accuracy positive
  let reading := observed.val
  have within : reading.rootBox.Refines (UnitRoot.box site) := by
    rewrite [reading.rootBox_eq]
    exact signed
  let allowance := data.chartSlope * (span.upper - span.lower) ^ 2 + 2 * data.residualSlope * accuracy
  have nonnegative : 0 ≤ allowance :=
    (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct data.signed_slopes_nonnegative.1
          (Arithmetic.sq_nonneg_direct _))
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel) data.signed_slopes_nonnegative.2)
          positive.le))
  exact
    { positive, reading
      accurate := observed.property
      signed := within
      allowance, allowance_eq := rfl
      allowance_nonnegative := nonnegative }

variable {data : Bounds.Data site parameter differential} {simple : differential.denominatorPairs = 0}
variable {lift : Conic.Lift (point site parameter (direction quarter span.lower) regular bound) unit}
variable {accuracy : Fraction.Rational}

/-- Change the differential while retaining the exact paid root state, reading, accuracy and original signed owner. -/
@[expose] def reweight (cell : Cell data simple lift accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Bounds.Data site parameter nextDifferential) (nextSimple : nextDifferential.denominatorPairs = 0) :
    Cell nextData nextSimple lift accuracy :=
  let reading := cell.reading.reweight nextData nextSimple
  let allowance := nextData.chartSlope * (span.upper - span.lower) ^ 2 + 2 * nextData.residualSlope * accuracy
  { positive := cell.positive
    reading
    accurate := cell.accurate
    signed := cell.signed
    allowance, allowance_eq := rfl
    allowance_nonnegative :=
      (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.trans_le
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct nextData.signed_slopes_nonnegative.1
            (Arithmetic.sq_nonneg_direct _))
          (Arithmetic.mul_nonneg_direct
            (Arithmetic.mul_nonneg_direct (by decide +kernel) nextData.signed_slopes_nonnegative.2)
            cell.positive.le)) }

/-- Reuse the exact retained center as the starting observation of the residual-controlled constant polynomial. -/
@[expose] def centerObservation (cell : Cell data simple lift accuracy) :
    Integration.Polynomial.Gaussian.Cell.Basic.LocalObservation
      (Gaussian.Basic.constant cell.reading.center) cell.allowance :=
  { parameter := 0
    integrandReading := cell.reading.center
    error := 0
    decomposition := by
      rewrite [Gaussian.Evaluation.eval_constant]
      exact Basic.sub_self _
    error_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_zero]
      exact cell.allowance_nonnegative }

/-- Read the same retained center, allowance and starting observation as a parameter-integration cell. -/
@[expose] def model (cell : Cell data simple lift accuracy) : CellModel where
  start := ⟨span.lower, 0⟩
  finish := ⟨span.upper, 0⟩
  polynomial := Gaussian.Basic.constant cell.reading.center
  localAllowance := cell.allowance
  localAllowance_nonneg := cell.allowance_nonnegative
  observations := [cell.centerObservation]

/-- Every compatible signed cofactor reading on the original span pays the residual-controlled cell allowance. -/
theorem candidate_error_le (cell : Cell data simple lift accuracy) {time : Fraction.Rational}
    (inside : span.Contains time) {root : Canonical} (rootInside : (UnitRoot.box site).Contains root)
    (residual : normSq (root * root - (unitPolynomial site).eval
      (point site parameter (direction quarter time) regular bound).base) ≤
      SquareRootSheets.residualTarget ((unitPolynomial site).eval
        (point site parameter (direction quarter time) regular bound).base))
    (accurate : normSq (root * root - (unitPolynomial site).eval
      (point site parameter (direction quarter time) regular bound).base) ≤ accuracy) :
    normSq (data.coefficient quarter regular bound time root - cell.reading.center) ≤ cell.allowance := by
  have parameterBound := Interval.Radius.sub_sq_le_sampleRadiusSq span (sample := span.lower) inside
  rewrite [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at parameterBound
  have centerInside := cell.signed.contains cell.reading.centerRoot_inside
  have comparison := data.signed_coefficient_distance_le quarter regular bound time span.lower rootInside centerInside
    residual cell.reading.centerResidual accurate cell.accurate.le
  rewrite [cell.reading.center_eq, cell.allowance_eq]
  exact comparison.trans_eq (show data.chartSlope * (time - span.lower) ^ 2 +
      data.residualSlope * (accuracy + accuracy) = data.chartSlope * (time - span.lower) ^ 2 +
        2 * data.residualSlope * accuracy by ring1) |>.trans
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct parameterBound data.signed_slopes_nonnegative.1)
      (Fraction.Order.Basic.le_refl _))

end Cell

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Refinement
