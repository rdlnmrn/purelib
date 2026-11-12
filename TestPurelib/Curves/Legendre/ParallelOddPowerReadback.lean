module

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Geometry.Gaussian.UnitCircle.Quarter

/-! # Six original differential readbacks on one retained cofactor observation

The actual original specification table reweights an existing scalar model.
Every value, cubic and quintic channel consumes the identical cofactor sample
and the same full-root reading, retaining its own numerator, scale and odd
power. This is coefficient readback, not a scalar/spatial error estimate.
-/

namespace TestPurelib.Curves.Legendre.ParallelOddPowerReadback

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Riemann.RootContinuation
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Radial
open Radial.Differential
open Periods.Jets.Specification
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Algebra.Quadratic (Pair)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {radicand : Pair.Polynomial.Coefficients} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {source : Transport.Reading actual span.lower inside} {accuracy : AccuracyRequest}

/-- Construct every original channel by reweighting the one actual sample, retaining its full-root value and exponent.

Only the channel's own original polynomial budget and scalar coefficient are
computed. The returned equality laws consume original public readbacks;
no root request, preparation, field reconstruction or assumed relation is
used for the six same-sample conclusions.
-/
def allSix (model : Cells.Model data source accuracy) :
    (channel : Fin 6) →
      {next : Cells.Model (Waist.Differential.Bounds.Data.build site parameter (Table.forms parameter channel))
          source accuracy //
        next.sample = model.sample ∧ next.rootReading.value = model.rootReading.value ∧
        next.center = ((Table.forms parameter channel).scale * (Table.forms parameter channel).numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            next.rootReading.value⁻¹ ^ (Table.forms parameter channel).denominatorExponent *
              Tangent.baseVelocity site parameter 2 quarter span.lower} := fun channel =>
  let next := model.reweight (Waist.Differential.Bounds.Data.build site parameter (Table.forms parameter channel))
  have sameSample : next.sample = model.sample := model.reweight_sample _
  have sameReading : next.sample.reading = model.sample.reading :=
    congrArg (fun observation : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy =>
      observation.reading) sameSample
  have sameRoot : next.rootReading.value = model.rootReading.value :=
    next.rootReading_value.trans
      ((congrArg (fun reading : Canonical => reading *
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate)
          sameReading).trans model.rootReading_value.symm)
  ⟨next, sameSample, sameRoot, next.center_fullRoot⟩

/-- The omitted odd-power generalization retains the complete former zero-pair coefficient claim. -/
example (model : Cells.Model data source accuracy) (pairs : differential.denominatorPairs = 0) :
    model.center = (differential.scale * differential.numerator.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        model.rootReading.value⁻¹ * Tangent.baseVelocity site parameter 2 quarter span.lower := by
  have retained := model.center_fullRoot
  rewrite [OddPowerDifferential.denominatorExponent, pairs] at retained
  simp only [Nat.mul_zero, Nat.zero_add, pow_one] at retained
  exact retained

end TestPurelib.Curves.Legendre.ParallelOddPowerReadback
