module

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume
import Purelib.Examples.Riemann.Periods.PolynomialObservations
import Purelib.Examples.Integration.Algebraic.SquareFactor.PolynomialObservations
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.PathObservation
import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Periods.PeriodPolicies
import Purelib.Riemann.Periods.PolynomialPeriodInput
import Purelib.Riemann.Periods.PolynomialPeriodObservation

/-! Recovering a request reads its initial retained exchange even when no bits
were requested. Continuation preserves that request's exact selected reading,
model and radius; it does not reacquire them from the stage source. -/

namespace Test.Riemann.PreparedObservationRequests

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.CertifiedProgram
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Curves.Hyperelliptic
open Purelib.Integration.Algebraic
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming
  CoefficientPolynomial -> GaussianPolynomial
open Purelib.Riemann.Periods

/-- A zero-bit observation still retains its selected query, complete model, sample and accuracy. -/
example (program : CachedProgram) (query : Request) :
    let recorded := Observation.Record.record program query 0
    let numerical := recorded.preparedRequest
    recorded.trace ≠ [] ∧ recorded.observation.word.length = 0 ∧
      numerical.cache = recorded.selectedExchange.reply ∧
      numerical.cache.model = (program.stage numerical.index).model ∧
      numerical.radiusSq = recorded.observation.selected.ball.radiusSq ∧
      reading (control program) numerical.index numerical.cache = recorded.observation.selected ∧
      numerical.radiusSq < query.target := by
  let recorded := Observation.Record.record program query 0
  let numerical := recorded.preparedRequest
  exact ⟨recorded.trace_nonempty, Observation.Record.recorded_length program query 0, rfl,
    congrArg (fun cache => cache.model) numerical.cache_eq, rfl,
    recorded.preparedRequest_reading, numerical.radiusSq_accurate⟩

/-- Recovering a numerical request after continuation preserves the original radius and exact cached model. -/
example (program : CachedProgram) (query : Request) (count extra : Nat) :
    let recorded := Observation.Record.record program query count
    let resumed := recorded.resume extra
    let original := recorded.preparedRequest
    let continued := resumed.recorded.preparedRequest
    continued.radiusSq = original.radiusSq ∧ continued.cache = original.cache ∧
      continued.index = original.index := by
  let recorded := Observation.Record.record program query count
  let resumed := recorded.resume extra
  let original := recorded.preparedRequest
  let continued := resumed.recorded.preparedRequest
  have radius : continued.radiusSq = original.radiusSq :=
    congrArg (fun selected => selected.ball.radiusSq) resumed.selected_eq
  have index : continued.index = original.index := continued.index_eq.trans original.index_eq.symm
  have cache : continued.cache = original.cache :=
    continued.cache_eq.trans
      ((congrArg program.stage index).trans original.cache_eq.symm)
  exact ⟨radius, cache, index⟩

/-- Both period comparison views preserve their exact existing receipts and shared selected entry. -/
example {polynomial : GaussianPolynomial} {selection : PolynomialPeriodInput.Selection}
    {left right : PeriodPolicies.Policy} {query : PeriodPolicies.Request} {count : Nat}
    (compared : PolynomialPeriodObservation.Comparison polynomial selection left right query count) :
    compared.leftObservation.recorded = compared.leftRecorded ∧
      compared.rightObservation.recorded = compared.rightRecorded ∧
      compared.leftObservation.prepared = compared.prepared ∧
      compared.rightObservation.prepared = compared.prepared := ⟨rfl, rfl, rfl, rfl⟩

/-- Square-factor comparison views retain the original entry, sheet, domain and actual policy receipts. -/
example {polynomial : GaussianPolynomial} {differential : Differentials.SquareFactor.Request}
    {segment : SquareFactor.PathInput.Segment} {sheet : Fin 2}
    {domain : SquareFactor.ObservationInput.Domain} {left right : SquareFactor.PathObservation.Policy}
    {query : SquareFactor.PathObservation.ObservationRequest} {count : Nat}
    (compared : SquareFactor.PolynomialObservation.Comparison
      polynomial differential segment sheet domain left right query count) :
    compared.leftObservation.recorded = compared.comparison.leftRecorded ∧
      compared.rightObservation.recorded = compared.comparison.rightRecorded ∧
      compared.leftObservation.entry = compared.entry ∧
      compared.rightObservation.entry = compared.entry := ⟨rfl, rfl, rfl, rfl⟩

end Test.Riemann.PreparedObservationRequests
