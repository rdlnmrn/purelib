module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Transport

/-!
# Exact request transport of a retained primitive endpoint entry

The entire original endpoint Entry moves along an equality of its root or
arithmetic requests. Each transport preserves the other request and all
retained observations. No preparation, root sampler or arithmetic comparison
is run.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
variable {first last accuracy : AccuracyRequest}
variable {sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot first}

/-- Transport the whole original endpoint Entry while aligning only its cofactor request index. -/
@[expose] def castRootAccuracy (equal : first = last)
    (entry : Entry primitive reading regular sample accuracy) :
    Entry primitive reading regular (CertifiedSquareRoot.Sampling.ResidualObservation.castAccuracy equal sample)
      accuracy := by
  cases equal
  exact entry

/-- Exact root-request transport preserves the complete original primitive Endpoint preparation and evaluator caches. -/
theorem castRootAccuracy_endpoint (equal : first = last)
    (entry : Entry primitive reading regular sample accuracy) :
    (entry.castRootAccuracy equal).endpoint = entry.endpoint := by
  cases equal
  rfl

/-- Exact root-request transport preserves the entire independently selected original arithmetic Reading. -/
theorem castRootAccuracy_selected (equal : first = last)
    (entry : Entry primitive reading regular sample accuracy) :
    HEq (entry.castRootAccuracy equal).selected entry.selected := by
  cases equal
  rfl

/-- Exact root-request transport preserves both original arithmetic starts and the whole retained comparison. -/
theorem castRootAccuracy_comparison (equal : first = last)
    (entry : Entry primitive reading regular sample accuracy) :
    HEq (entry.castRootAccuracy equal).selected.comparison entry.selected.comparison := by
  cases equal
  rfl

/-- Exact root-request transport retains the identical already selected primitive endpoint witness. -/
theorem castRootAccuracy_value (equal : first = last)
    (entry : Entry primitive reading regular sample accuracy) :
    (entry.castRootAccuracy equal).value = entry.value := by
  cases equal
  rfl

section Arithmetic

variable {rootAccuracy arithmeticFirst arithmeticLast : AccuracyRequest}
variable {rootSample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy}

/-- Transport the whole original Entry along equal arithmetic requests while keeping its root sample unchanged. -/
@[expose] def castAccuracy (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    Entry primitive reading regular rootSample arithmeticLast := by
  cases equal
  exact entry

/-- Exact arithmetic-request transport preserves the original complete Endpoint and prepared evaluator caches. -/
theorem castAccuracy_endpoint (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    (entry.castAccuracy equal).endpoint = entry.endpoint := by
  cases equal
  rfl

/-- Exact arithmetic-request transport preserves the whole independently selected original arithmetic Reading. -/
theorem castAccuracy_selected (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    HEq (entry.castAccuracy equal).selected entry.selected := by
  cases equal
  rfl

/-- Exact arithmetic-request transport preserves the complete original comparison and both of its selected starts. -/
theorem castAccuracy_comparison (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    HEq (entry.castAccuracy equal).selected.comparison entry.selected.comparison := by
  cases equal
  rfl

/-- Exact arithmetic-request transport preserves both complete original arithmetic observation records. -/
theorem castAccuracy_observations (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    (entry.castAccuracy equal).selected.originalObservation = entry.selected.originalObservation ∧
      (entry.castAccuracy equal).selected.paidObservation = entry.selected.paidObservation := by
  cases equal
  exact ⟨rfl, rfl⟩

/-- Exact arithmetic-request transport preserves the actual old selected primitive value. -/
theorem castAccuracy_value (equal : arithmeticFirst = arithmeticLast)
    (entry : Entry primitive reading regular rootSample arithmeticFirst) :
    (entry.castAccuracy equal).value = entry.value := by
  cases equal
  rfl

end Arithmetic

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

end
