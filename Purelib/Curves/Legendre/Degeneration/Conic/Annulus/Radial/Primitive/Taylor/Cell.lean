module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Slope
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading.Time
public import Purelib.Integration.Polynomial.Gaussian.Cell.Taylor
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Prescribed primitive endpoints against an actual original chart cell

The source is the exact original derivative cell and its retained cofactor
observation. An exact time equality transports a separately retained upper
Reading/observation without another query. Their fourth-power payment
constructs the original scalar primitive Taylor certificate; the actual
independent spatial derivative coefficient is that same cell's centre.

The resulting estimate concerns the original retained cell integral. It
neither changes old coarse requests nor assumes an integral endpoint law,
whole-path telescoping or comparison with canonical affine integral cells.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Cell

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.RootContinuation
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds}
variable {firstInside : FixedRootBoxPath.Inside span.lower} {lastInside : FixedRootBoxPath.Inside span.upper}

/-- The original primitive endpoint readings pay their error against the actual independent spatial derivative cell.

The cell's original selected cofactor observation is reused exactly. Its
fourth-power request and one distinct original upper observation derive the
scalar Taylor and source residual errors internally. The exact chart width
and original constant coefficient identify this same cell's integral sample.
-/
theorem integral_error_le {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    {data : Waist.Differential.Bounds.Data site parameter specification.differential}
    {source : Transport.Reading actual span.lower firstInside} {accuracy : AccuracyRequest}
    (model : Differential.Cells.Model (span := span) data source accuracy)
    (target : Transport.Reading actual span.upper lastInside)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = span.width ^ 4) :
    Norm.Basic.normSq
      (Primitive.reading (site := site) primitive quarter span.upper targetSample.reading -
        Primitive.reading (site := site) primitive quarter span.lower model.sample.reading -
          model.cell.integralSample) ≤
      2 * (Taylor.ceiling site parameter primitive model.regular +
        slopeResidualFactor site parameter primitive) * span.width ^ 4 := by
  have timeEqual : span.upper = span.lower + span.width := by
    change span.upper = span.lower + (span.upper - span.lower)
    ring1
  have transportedInside : FixedRootBoxPath.Inside (span.lower + span.width) := timeEqual ▸ lastInside
  let transported := target.castTime (lastInside := transportedInside) timeEqual
  let transportedSample := target.castTimeSample (lastInside := transportedInside) timeEqual targetSample
  let scalar := Taylor.build
    primitive source transported model.regular accuracy model.sample transportedSample accuracy_eq
  let step := Stereographic.Tangent.increment span.width
  let residualFactor := slopeResidualFactor site parameter primitive
  have unit : Norm.Basic.normSq step ≤ 1 := Stereographic.Tangent.increment_unit firstInside transportedInside
  have residualNonnegative : 0 ≤ residualFactor :=
    slopeResidualFactor_nonnegative site parameter primitive model.regular
  have sourceDiscrepancy : Norm.Basic.normSq (scalar.certificate.slope - model.center) ≤
      residualFactor * Norm.Basic.normSq step ^ 2 := by
    rewrite [model.center_eq]
    have opposite : scalar.certificate.slope -
        Differential.reading site parameter quarter span.lower specification.differential model.sample.reading =
      -(Differential.reading site parameter quarter span.lower specification.differential model.sample.reading -
        scalar.certificate.slope) := by ring1
    rewrite [opposite, Norm.Basic.normSq_neg, Stereographic.Tangent.increment_fourth]
    exact scalar_slope_le primitive source transported model.regular accuracy model.sample transportedSample
      accuracy_eq specification
  have displacement : model.cell.displacement = step := by
    apply Gaussian.Basic.ext
    · rfl
    · change (0 : Fraction.Rational) - 0 = 0
      ring1
  have error := CellModel.quadratic_integral_error_le scalar.certificate model.cell model.center displacement rfl
  have paid : Norm.Basic.normSq (scalar.certificate.output - scalar.certificate.base - model.cell.integralSample) ≤
      2 * (Taylor.ceiling site parameter primitive model.regular + residualFactor) * span.width ^ 4 := by
    have coefficient := Arithmetic.mul_le_mul_of_nonneg_left_direct sourceDiscrepancy
      (Norm.Basic.normSq_nonneg step)
    have coefficientSmall : Norm.Basic.normSq step * (residualFactor * Norm.Basic.normSq step ^ 2) ≤
        residualFactor * Norm.Basic.normSq step ^ 2 :=
      (Arithmetic.mul_le_mul_of_nonneg_right_direct unit
        (Arithmetic.mul_nonneg_direct residualNonnegative
          (Arithmetic.sq_nonneg_direct _))).trans_eq (Fraction.Field.one_mul _)
    have factor := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Taylor.build_factor_le
        primitive source transported model.regular accuracy model.sample transportedSample accuracy_eq)
      (Arithmetic.sq_nonneg_direct (Norm.Basic.normSq step))
    exact error.trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct factor (coefficient.trans coefficientSmall))
        (by decide +kernel)).trans_eq (by
          rewrite [Stereographic.Tangent.increment_fourth]
          ring1))
  have sourceValue := scalar.base_eq
  have targetValue := scalar.output_eq
  rewrite [Transport.Reading.castTimeSample_reading, ← timeEqual] at targetValue
  rewrite [targetValue, sourceValue] at paid
  exact paid

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Cell

end
