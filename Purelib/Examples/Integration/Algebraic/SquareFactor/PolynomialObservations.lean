module

import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
import Purelib.Integration.Algebraic.SquareFactor.ObservationTransport
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

/-! Checked coefficient-first entries retain their preparations through
observation, numerical readback, comparison and continuation. Regular-curve
periods remain distinct from original-coordinate square-factor differentials.
The inputs below are initial curve or path preparations and their validity
evidence; the checked entry and every observation are constructed here. -/

namespace Purelib.Examples.Integration.Algebraic.SquareFactor.PolynomialObservations

open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Curves.Hyperelliptic
open Purelib.Integration.Algebraic
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming
  CoefficientPolynomial -> GaussianPolynomial

/-- Original-coordinate checking retains one safe source through policy comparison and continuation. -/
example {polynomial : GaussianPolynomial} {differential : Differentials.SquareFactor.Request}
    {segment : SquareFactor.PathInput.Segment}
    (prepared : Differentials.SquareFactor.Prepared polynomial differential)
    (data : SquareFactor.PathInput.Data prepared segment) (safe : data.Safe)
    (sheet : Fin 2) (original : 0 < data.squareFactor.lowerBound)
    (left right : SquareFactor.PathObservation.Policy)
    (query : SquareFactor.PathObservation.ObservationRequest) (count extra : Nat) :
    match SquareFactor.ObservationInput.prepareChecked prepared data sheet .originalCoordinate with
    | .error _ => False
    | .ok entry =>
      let compared := SquareFactor.PolynomialObservation.comparePrepared entry left right query count
      let observed := compared.leftObservation
      let other := compared.rightObservation
      let numerical := observed.preparedRequest
      let resumed := observed.resume extra
      observed.entry.prepared = prepared ∧ compared.entry = entry ∧
        observed.recorded = compared.comparison.leftRecorded ∧
        other.recorded = compared.comparison.rightRecorded ∧
        numerical.cache = observed.recorded.selectedExchange.reply ∧
        reading (control (SquareFactor.PathObservation.program entry.source left)) numerical.index numerical.cache =
          observed.recorded.observation.selected ∧
        resumed.recorded.observation.selected = observed.recorded.observation.selected ∧
        observed.recorded.observation.word.IsPrefix resumed.recorded.observation.word ∧
        numerical.radiusSq < query.target := by
  rw [SquareFactor.ObservationInput.prepareChecked_complete prepared data safe sheet .originalCoordinate original]
  let entry := SquareFactor.ObservationInput.PreparedEntry.ofData prepared data safe sheet .originalCoordinate original
  let compared := SquareFactor.PolynomialObservation.comparePrepared entry left right query count
  let observed := compared.leftObservation
  exact ⟨rfl, rfl, rfl, rfl, rfl, observed.recorded.preparedRequest_reading,
    observed.resume_selected extra, observed.resume_prefix extra, observed.preparedRequest.radiusSq_accurate⟩

/-- Each resumed original-coordinate cell retains its logged model and original differential correspondence. -/
example {polynomial : GaussianPolynomial} {differential : Differentials.SquareFactor.Request}
    {segment : SquareFactor.PathInput.Segment}
    (prepared : Differentials.SquareFactor.Prepared polynomial differential)
    (data : SquareFactor.PathInput.Data prepared segment) (safe : data.Safe)
    (sheet : Fin 2) (original : 0 < data.squareFactor.lowerBound)
    (policy : SquareFactor.PathObservation.Policy)
    (query : SquareFactor.PathObservation.ObservationRequest) (count extra : Nat) :
    match SquareFactor.ObservationInput.prepareChecked prepared data sheet .originalCoordinate with
    | .error _ => False
    | .ok entry =>
      let observed := SquareFactor.PolynomialObservation.observePrepared entry policy query count
      let resumed := observed.resume extra
      ∀ (traceIndex : Fin resumed.recorded.trace.length)
        (cellIndex : Fin (SquareFactor.ObservationTransport.traceLayer resumed traceIndex).cells.length),
        let cell := SquareFactor.ObservationTransport.transportCell resumed traceIndex cellIndex
        cell.cell.model.cell ∈
            (SquareFactor.ObservationTransport.traceExchange resumed traceIndex).reply.model.cells ∧
          Nonempty (∀ (fraction : SquareFactor.PathInput.Coordinate)
            (inside : SquareFactor.PathInput.unitInterval.Contains fraction),
            Equivalence.NamedEquivalent (cell.cell.edge.source fraction inside).name
              (SquareFactor.SourceTransport.originalName cell.cell.edge
                resumed.entry.domainEvidence fraction inside).name) := by
  rw [SquareFactor.ObservationInput.prepareChecked_complete prepared data safe sheet .originalCoordinate original]
  intro traceIndex cellIndex
  let cell := SquareFactor.ObservationTransport.transportCell _ traceIndex cellIndex
  exact ⟨cell.model_member, ⟨fun fraction inside => cell.source_original fraction inside⟩⟩

/-- Continuation retains the checked entry and domain.

A cancelled-expression entry is never promoted to an original-coordinate entry. -/
example {polynomial : GaussianPolynomial} {differential : Differentials.SquareFactor.Request}
    {segment : SquareFactor.PathInput.Segment}
    (prepared : Differentials.SquareFactor.Prepared polynomial differential)
    (data : SquareFactor.PathInput.Data prepared segment) (safe : data.Safe)
    (sheet : Fin 2) (domain : SquareFactor.ObservationInput.Domain) (evidence : domain.Evidence data)
    (policy : SquareFactor.PathObservation.Policy)
    (query : SquareFactor.PathObservation.ObservationRequest) (count extra : Nat) :
    match SquareFactor.ObservationInput.prepareChecked prepared data sheet domain with
    | .error _ => False
    | .ok entry =>
      let observed := SquareFactor.PolynomialObservation.observePrepared entry policy query count
      observed.entry = entry ∧ (observed.resume extra).entry = entry := by
  rw [SquareFactor.ObservationInput.prepareChecked_complete prepared data safe sheet domain evidence]
  exact ⟨rfl, rfl⟩

end Purelib.Examples.Integration.Algebraic.SquareFactor.PolynomialObservations
