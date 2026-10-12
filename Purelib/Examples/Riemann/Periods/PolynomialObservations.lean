module

import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Riemann.Periods.PolynomialPeriodInput
import Purelib.Riemann.Periods.PolynomialPeriodObservation

/-! Checked coefficient-first entries retain their preparations through
observation, numerical readback, comparison and continuation. Regular-curve
periods remain distinct from original-coordinate square-factor differentials.
The inputs below are initial curve or path preparations and their validity
evidence; the checked entry and every observation are constructed here. -/

namespace Purelib.Examples.Riemann.Periods.PolynomialObservations

open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Curves.Hyperelliptic
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming
  CoefficientPolynomial -> GaussianPolynomial
open Purelib.Riemann.Periods

/-- One checked reduced-curve entry supplies policy comparison, retained numerical reading and resumed output. -/
example (polynomial : GaussianPolynomial) (selection : PolynomialPeriodInput.Selection)
    (nonzero : polynomial.isZero = false) (curve : Preparation.Polynomial.Prepared polynomial)
    (bounds : PolynomialPeriodInput.Bounds selection curve.genus)
    (left right : PeriodPolicies.Policy) (query : PeriodPolicies.Request) (count extra : Nat) :
    match PolynomialPeriodInput.prepareRegular selection nonzero curve with
    | .error _ => False
    | .ok entry =>
      let compared := PolynomialPeriodObservation.comparePrepared entry left right query count
      let observed := compared.leftObservation
      let other := compared.rightObservation
      let numerical := observed.preparedRequest
      let resumed := observed.resume extra
      observed.prepared.prepared = curve ∧ compared.prepared = entry ∧
        observed.recorded = compared.leftRecorded ∧ other.recorded = compared.rightRecorded ∧
        numerical.cache = observed.recorded.selectedExchange.reply ∧
        reading (control (PeriodPolicies.program entry.entry left)) numerical.index numerical.cache =
          observed.recorded.observation.selected ∧
        resumed.recorded.observation.selected = observed.recorded.observation.selected ∧
        observed.recorded.observation.word.IsPrefix resumed.recorded.observation.word ∧
        numerical.radiusSq < query.target := by
  rw [PolynomialPeriodInput.prepareRegular_complete selection nonzero curve bounds]
  let entry := PolynomialPeriodInput.PreparedEntry.ofCurve selection nonzero curve bounds
  let compared := PolynomialPeriodObservation.comparePrepared entry left right query count
  let observed := compared.leftObservation
  exact ⟨rfl, rfl, rfl, rfl, rfl, observed.recorded.preparedRequest_reading,
    observed.resume_selected extra, observed.resume_prefix extra, observed.preparedRequest.radiusSq_accurate⟩

/-- Different selections retain one computed curve while owning separate selected entry caches.

Only the curve preparation is shared across selections. Within each selection,
the observation reads the thunk created by that selection's checked entry. -/
example (polynomial : GaussianPolynomial) (nonzero : polynomial.isZero = false)
    (curve : Preparation.Polynomial.Prepared polynomial)
    (first second : PolynomialPeriodInput.Selection)
    (firstBounds : PolynomialPeriodInput.Bounds first curve.genus)
    (secondBounds : PolynomialPeriodInput.Bounds second curve.genus) :
    match PolynomialPeriodInput.prepareRegular first nonzero curve,
        PolynomialPeriodInput.prepareRegular second nonzero curve with
    | .ok firstEntry, .ok secondEntry =>
      firstEntry.prepared = curve ∧ secondEntry.prepared = curve
    | _, _ => False := by
  rw [PolynomialPeriodInput.prepareRegular_complete first nonzero curve firstBounds,
    PolynomialPeriodInput.prepareRegular_complete second nonzero curve secondBounds]
  exact ⟨rfl, rfl⟩

end Purelib.Examples.Riemann.Periods.PolynomialObservations
