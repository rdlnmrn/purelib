module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

/-!
# Exact time-index transports of retained radial readings

An exact equality of chart times transports the complete original requested
Reading and its cofactor observation. The original owner, preparation, lift,
process and selected observation remain unchanged; these operations perform
no geometric query, root isolation or sample selection.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Approximation

variable {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
variable {positive : 0 < scale} {actual : Quarter site parameter scale quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}

/-- Transport the complete original Reading along an exact chart-time equality without rebuilding any retained cache. -/
@[expose] def castTime (equal : first = last) (reading : Reading actual first firstInside) :
    Reading actual last lastInside := by
  cases equal
  exact reading

/-- The exact time-index transport retains the identical original full-sheet coherent value. -/
theorem castTime_lift_value (equal : first = last) (reading : Reading actual first firstInside) :
    (castTime (lastInside := lastInside) equal reading).lift.value = reading.lift.value := by
  cases equal
  rfl

/-- The exact time-index transport retains the original complete cofactor certificate's identical coherent value. -/
theorem castTime_unit_value (equal : first = last) (reading : Reading actual first firstInside) :
    (castTime (lastInside := lastInside) equal reading).lift.unitRoot.value = reading.lift.unitRoot.value := by
  cases equal
  rfl

/-- Transport the complete original paid cofactor observation with its already retained Reading and exact time index. -/
@[expose] def castTimeSample (equal : first = last) (reading : Reading actual first firstInside)
    {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    CertifiedSquareRoot.Sampling.ResidualObservation
      (castTime (lastInside := lastInside) equal reading).lift.unitRoot accuracy := by
  cases equal
  exact sample

/-- The time-index transport retains the exact same original observation, witness, candidate predicate and spread. -/
theorem castTimeSample_observation (equal : first = last) (reading : Reading actual first firstInside)
    {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    (castTimeSample (lastInside := lastInside) equal reading sample).observation = sample.observation := by
  cases equal
  rfl

/-- The exact time-index transport preserves the same actual selected cofactor witness. -/
theorem castTimeSample_reading (equal : first = last) (reading : Reading actual first firstInside)
    {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    (castTimeSample (lastInside := lastInside) equal reading sample).reading = sample.reading := by
  cases equal
  rfl

/-- The transported original square comparison preserves its actual selected source index. -/
theorem castTimeSample_index (equal : first = last) (reading : Reading actual first firstInside)
    {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    (castTimeSample (lastInside := lastInside) equal reading sample).comparison.leftIndex =
      sample.comparison.leftIndex := by
  cases equal
  rfl

/-- Exact chart-time transport preserves the complete original Reading and all original owner/preparation caches. -/
theorem castTime_heq (equal : first = last) (reading : Reading actual first firstInside) :
    HEq (castTime (lastInside := lastInside) equal reading) reading := by
  cases equal
  rfl

/-- The identical original query factory commutes with exact chart-time transport without acquiring another query. -/
theorem castTime_build (equal : first = last) :
    castTime (lastInside := lastInside) equal (Reading.build actual first firstInside) =
      Reading.build actual last lastInside := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading

end
