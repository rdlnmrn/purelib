module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Observation.Basic
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Later root observations of the same retained scalar chart cell

A new residual request advances the exact original cofactor certificate
past the old cell's selected sample index. The original cell, observation,
coefficient and request remain intact. The same source query and differential
budget construct one new Model from that actual later observation.

The original process persistence law compares the complete observations;
the original signed square-residual estimate separately bounds the actual
coefficient difference. The resulting integral-sample error retains the
original chart width as its displacement factor.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.RootContinuation

variable {radicand : CoefficientPolynomial}
variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {source : Transport.Reading actual span.lower inside} {accuracy : AccuracyRequest}

/-- A new original Model at the same source whose actual sample index is after the retained old sample index. -/
abbrev Refined (model : Model data source accuracy) (request : AccuracyRequest) :=
  { current : Model data source request // model.sample.comparison.leftIndex ≤ current.sample.comparison.leftIndex }

/-- Advance the same cached cofactor certificate once and retain its actual new observation in the original Model.

The stage minimum includes the old sample's exact comparison index before
requestAfter chooses a new state and reading. The original source query,
differential budget and regularity are reused by ofSample without sampling
again or replacing the old Model.
-/
def refineAfter (model : Model data source accuracy) (request : AccuracyRequest) : Refined model request :=
  let selected := CertifiedSquareRoot.Sampling.requestAfter source.lift.unitRoot request
    model.sample.comparison.leftIndex
  let current := ofSample data source model.regular request selected.val
  ⟨current, selected.property⟩

/-- The actual new residual observation refines the identical original old process observation. -/
theorem Refined.observation_refines {model : Model data source accuracy} {request : AccuracyRequest}
    (refined : Refined model request) :
    Observation.Refines refined.val.sample.observation model.sample.observation := by
  constructor
  intro candidate possible
  rewrite [refined.val.sample.observation_eq, refined.val.sample.state_eq] at possible
  have earlier := Process.Sampling.stateAt_possible_persists source.lift.unitRoot.value.name.process
    source.lift.unitRoot.value.name.state refined.property possible
  rewrite [model.sample.observation_eq, model.sample.state_eq]
  exact earlier

/-- The new actual reading is possible in the original old selected state; the old witness is not replaced. -/
theorem Refined.reading_possible_old {model : Model data source accuracy} {request : AccuracyRequest}
    (refined : Refined model request) :
    source.lift.unitRoot.value.name.process.Possible model.sample.state refined.val.sample.reading := by
  have possible := refined.observation_refines.possible refined.val.sample.observation.witness_possible
  rewrite [model.sample.observation_eq] at possible
  exact possible

/-- The original old observation's retained spread bounds the two actual selected root readings. -/
theorem Refined.root_readings_le {model : Model data source accuracy} {request : AccuracyRequest}
    (refined : Refined model request) :
    Norm.Basic.normSq (refined.val.sample.reading - model.sample.reading) ≤
      model.sample.observation.spread :=
  model.sample.observation.pairwise
    (refined.observation_refines.possible refined.val.sample.observation.witness_possible)
    model.sample.observation.witness_possible

/-- The retained differential budget pays the coefficient comparison through both distinct residual requests. -/
@[expose] def errorBound (_model : Model data source accuracy) (request : AccuracyRequest) : Fraction.Rational :=
  Bounds.residualSlope data * (request.tolerance + accuracy.tolerance)

/-- The new actual coefficient and unchanged old coefficient pay their internally derived same-point residual bound. -/
theorem Refined.center_error_le {model : Model data source accuracy} {request : AccuracyRequest}
    (refined : Refined model request) :
    Norm.Basic.normSq (refined.val.center - model.center) ≤ errorBound model request := by
  have paid := Bounds.signed_reading_distance_le data quarter model.regular actual.data.bound span.lower span.lower
    refined.val.signed model.signed refined.val.residual model.residual
    refined.val.sample.reading_residual_lt.le model.sample.reading_residual_lt.le
  rewrite [refined.val.center_eq, model.center_eq]
  exact paid.trans_eq (by unfold errorBound; ring1)

/-- The exact original chart displacement weights the actual new-versus-old integral-sample error. -/
theorem Refined.integral_error_le {model : Model data source accuracy} {request : AccuracyRequest}
    (refined : Refined model request) :
    Norm.Basic.normSq (refined.val.cell.integralSample - model.cell.integralSample) ≤
      span.width ^ 2 * errorBound model request := by
  let step := Stereographic.Tangent.increment span.width
  have difference : refined.val.cell.integralSample - model.cell.integralSample =
      step * (refined.val.center - model.center) := by
    rewrite [refined.val.integralSample, model.integralSample]
    change (⟨span.upper - span.lower, 0⟩ : Canonical) * refined.val.center -
      (⟨span.upper - span.lower, 0⟩ : Canonical) * model.center =
        (⟨span.upper - span.lower, 0⟩ : Canonical) * (refined.val.center - model.center)
    ring1
  rewrite [difference, Norm.Basic.normSq_mul, Stereographic.Tangent.increment_normSq]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct refined.center_error_le
    (Fraction.Order.Arithmetic.sq_nonneg_direct span.width)

/-- A positive actual chart width gives the exact fourth-power square-residual accuracy request. -/
@[expose] def fourthRequest (_model : Model data source accuracy) (positive : 0 < span.width) : AccuracyRequest :=
  ⟨span.width ^ 4, Fraction.Order.Arithmetic.pow_pos_direct positive 4⟩

/-- The same chart request retains exactly the original width's fourth power as its square-residual tolerance. -/
theorem fourthRequest_tolerance (model : Model data source accuracy) (positive : 0 < span.width) :
    (model.fourthRequest positive).tolerance = span.width ^ 4 := rfl

/-- Pay the exact fourth-power residual request after the old cell's actual selected observation index. -/
def refineFourth (model : Model data source accuracy) (positive : 0 < span.width) :
    Refined model (model.fourthRequest positive) := model.refineAfter (model.fourthRequest positive)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells.Model

end
