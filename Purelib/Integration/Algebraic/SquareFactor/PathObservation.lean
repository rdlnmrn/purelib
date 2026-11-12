module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume
public import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Computation.Query.Basic
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Computation.Query.Boundary
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.RefinementGeometry
import Purelib.Integration.CertifiedProgram
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Computation.Query.Computation

public section

/-!
# Finite observations of the transported rational differential

The generated coherent path program enters the actual cached observation
runner.  Every logged reply retains its equality to the corresponding
inherited integration layer, including its original path geometry and
uniform quotient-source bounds.  Finite policies only schedule or cache the
same source; they cannot replace its differential, orientation or sheet.

This is the prepared-path adapter.  The coefficient-first input checker must
construct its `data.Safe` input; no numerical coherence, integral equality,
refinement certificate or successful-run equation is supplied here.
Replay observes complete model queries, not internal root-isolation steps.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.PathObservation

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Integration.Algebraic.SquareFactor

universe u

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells

/-- The original cached-program scheduling and allocation policy carrier. -/
abbrev Policy := Program.Gaussian.Cached.Policy
open Purelib.Integration in
/-- The original certified numerical observation request carrier. -/
abbrev ObservationRequest := CertifiedProgram.Request
/-- The original retained Gaussian integration model cache carrier. -/
abbrev CachedModel := Program.Gaussian.Cached.Basic.CachedModel

variable {polynomial : GaussianPolynomial} {request :
  Request}
  {prepared : Prepared polynomial request} {segment :
    Segment}
  {data : Data prepared segment}

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.Cached in
set_option genInjectivity false in
/-- The exact cached integration source for one retained safe path and selected sheet.

The defining equation binds the retained source program to the original layer construction, preserving the path data and
sheet owner. -/
structure Source (data : Data prepared segment) (sheet : Fin 2) where
  /-- The original retained path's denominator and radicand safety certificate. -/ safe : data.Safe
  /-- The retained exact cached integration source program. -/ value : Basic.CachedProgram
  /-- The retained program equals the original safe-path and sheet construction. -/ value_eq : value =
    IntegrationProgram.cached safe sheet

constructive_injectivity Source

open Purelib.Integration.Algebraic.SquareFactor in
/-- Retain the exact canonical source program for the supplied safe path and original sheet. -/
@[expose] def Source.canonical (safe : data.Safe) (sheet : Fin 2) : Source data sheet :=
  ⟨safe, IntegrationProgram.cached safe sheet, rfl⟩

/-- Retain the supplied original initial layer when constructing its same complete path-observation source. -/
@[expose] def Source.ofInitial (safe : data.Safe) (sheet : Fin 2) (start : IntegrationLayers.Layer safe 0)
    (same : start = IntegrationLayers.initial safe sheet) : Source data sheet :=
  ⟨safe, IntegrationProgram.cachedFrom start, IntegrationProgram.cachedFrom_eq_cached safe sheet start same⟩

/-- The original initial-layer identity preserves the complete original canonical path source and all its callbacks. -/
theorem Source.ofInitial_eq_canonical (safe : data.Safe) (sheet : Fin 2) (start : IntegrationLayers.Layer safe 0)
    (same : start = IntegrationLayers.initial safe sheet) :
    Source.ofInitial safe sheet start same = Source.canonical safe sheet := by
  cases same
  rfl

variable {sheet : Fin 2}

section
open Purelib.Integration.Algebraic.SquareFactor
/-- The retained source sample equals the exact original layer integral sample at the same stage. -/
theorem Source.sample_eq (source : Source data sheet) (index : Nat) :
    (source.value.stage index).sample =
      (IntegrationProgram.layerAt source.safe sheet index).model.integralSample := by
  rw [source.value_eq]
  exact IntegrationProgram.cached_sample source.safe sheet index

/-- The retained source model equals the exact original layer model at the same stage. -/
theorem Source.model_eq (source : Source data sheet) (index : Nat) :
    (source.value.stage index).model =
      (IntegrationProgram.layerAt source.safe sheet index).model := by
  rw [source.value_eq]
  exact IntegrationProgram.cached_model source.safe sheet index

end

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Apply the original cache-and-schedule policy to the exact retained source program. -/
@[expose] def program (source : Source data sheet) (policy : Policy) :
  Basic.CachedProgram :=
  policy.program source.value

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Record the exact policy-controlled source observation for the original request and bit count. -/
@[expose] def record (source : Source data sheet) (policy : Policy) (query :
  ObservationRequest) (count : Nat) :
    Observation.Record.Recorded (program source policy) query count :=
  Observation.Record.record (program source policy) query count

open Purelib.CCL.Progressive in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Read the original source index selected by the policy schedule for the exact numerical request. -/
@[expose] def sourceIndex (source : Source data sheet) (policy : Policy) (query :
  ObservationRequest) : Nat :=
  policy.schedule.index (IntegrationReplay.selectedIndex
    (IntegrationReplay.control (program source policy)) query)

section
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Integration.Program.Gaussian.CCL.Replay
/-- A recorded numerical observation tied to the original square-factor layer samples and every queried layer model.

The exact selected source index and per-query schedule indices retain the original safe path, sheet and compiled cell
owners. -/
structure Contract (source : Source data sheet) (policy : Policy) (query :
  ObservationRequest) (count : Nat)
    (recorded : Observation.Record.Recorded (program source policy) query count) : Prop where
  /-- The exact retained record's numerical, replay and machine-semantics contract. -/ numerical :
    Observation.Contract (program source policy) query count recorded
  /-- The selected reading equals the original layer sample at the retained scheduled source index. -/ selected_sample :
    recorded.observation.selected.sample =
    (IntegrationProgram.layerAt source.safe sheet (sourceIndex source policy
      query)).model.integralSample
  /-- Every retained query reply model equals the original layer at its exact scheduled index. -/ trace_models : ∀
    exchange ∈ recorded.trace, exchange.reply.model =
    (IntegrationProgram.layerAt source.safe sheet (policy.schedule.index exchange.query)).model

/-- Every certified retained policy observation satisfies its original numerical and square-factor layer contract. -/
theorem observation_contract (source : Source data sheet) (policy : Policy)
    (query : ObservationRequest) (count : Nat)
    (recorded : Observation.Record.Recorded (program source policy) query count :=
      record source policy query count) : Contract source policy query count recorded :=
        by
  rw [recorded.eq_record]
  refine ⟨Observation.Contract.observation_contract _ _ _, ?_, ?_⟩
  · rw [Observation.Record.recorded_selected]
    change ((program source policy).stage _).sample = _
    rw [program, policy.stage_eq]
    exact source.sample_eq _
  · intro exchange member
    rw [Observation.Record.recorded_reply (program source policy) query count exchange member,
      program, policy.stage_eq]
    exact source.model_eq _

end

namespace Contract

variable {source : Source data sheet} {policy :
  Policy} {query :
  ObservationRequest} {count : Nat}
  {recorded : Program.Gaussian.CCL.Replay.Observation.Record.Recorded
    (program source policy) query count}
  (contract : Contract source policy query count recorded)

include contract

open Purelib.Computation.Query in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained transcript model contains exactly the original scheduled layer's compiled cell models. -/
theorem trace_cells (exchange : Basic.Exchange Nat CachedModel) (member : exchange ∈ recorded.trace) :
    exchange.reply.model.cells =
      (IntegrationProgram.layerAt source.safe sheet (policy.schedule.index exchange.query)).cells.map
        (fun cell => cell.model.cell) := by
  rw [contract.trace_models exchange member]
  exact (IntegrationProgram.layerAt source.safe sheet _).model_cells

open Purelib.Computation.Query in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Every retained transcript model has its original compiled cells and exact dyadic parameter-edge geometry. -/
theorem trace_geometry (exchange : Basic.Exchange Nat CachedModel) (member : exchange ∈ recorded.trace)
  :
    ∃ (cells : List (Cell source.safe)) (depth : Nat),
      exchange.reply.model.cells = cells.map (fun cell => cell.model.cell) ∧
      cells.map RefinementGeometry.parameterEdge =
        ClearSheetContinuation.Subdivision.dyadicEdges depth PathContinuation.first
          Purelib.Integration.Algebraic.SquareFactor.PathContinuation.last :=
  ⟨_, _, contract.trace_cells exchange member,
    (IntegrationProgram.layerAt source.safe sheet _).geometry⟩

end Contract

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Two retained policies give equivalent output names for the same original square-factor source. -/
@[expose] def outputs_equivalent (source : Source data sheet) (left right : Policy) :
    Equivalence.NamedEquivalent (program source left).output.name
      (program source right).output.name :=
  Policy.outputs_equivalent source.value left right

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
set_option genInjectivity false in
/-- Separate retained policy observations of one original source with output equivalence and individual contracts. -/
structure Comparison (source : Source data sheet) (left right : Policy) (query :
  ObservationRequest) (count : Nat) where
  /-- The exact retained observation under the original left policy. -/ leftRecorded : Observation.Record.Recorded
    (program source left) query count
  /-- The exact retained observation under the original right policy. -/ rightRecorded : Observation.Record.Recorded
    (program source right) query count
  /-- The two retained policy output names are equivalent. -/ outputs : Equivalence.NamedEquivalent
    (program source left).output.name
    (program source right).output.name
  /-- The original left record's source and numerical contract. -/ left_contract : Contract source left
    query count leftRecorded
  /-- The original right record's source and numerical contract. -/ right_contract : Contract source
    right query count rightRecorded

constructive_injectivity Comparison

open Purelib.Integration.Algebraic.SquareFactor in
/-- Record both policy observations once and retain their exact records, output equivalence and separate source
contracts. -/
@[expose] def compare (source : Source data sheet) (left right : Policy) (query :
  ObservationRequest) (count : Nat) :
    Comparison source left right query count :=
  let leftRecorded := record source left query count
  let rightRecorded := record source right query count
  ⟨leftRecorded, rightRecorded, outputs_equivalent source left right,
    observation_contract source left query count leftRecorded,
    observation_contract source right query count rightRecorded⟩

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- The resumed record retains the exact original source contract at the extended bit count. -/
theorem resumed_contract (source : Source data sheet) (policy : Policy)
    (query : ObservationRequest) (count extra : Nat)
    {saved : Observation.Record.Recorded (program source policy) query count}
    (resumed : Observation.Resume.IntegrationReplay.Resumed saved extra) :
    Contract source policy query (count + extra) resumed.recorded :=
  observation_contract source policy query (count + extra) resumed.recorded

open Purelib.CCL.Progressive in
open Purelib.Computation.Query in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Program.Gaussian.CCL.Replay in
/-- Changing payload-dependent oracle replies outside the exact retained trace preserves the original source observation
execution. -/
theorem payload_erasure (source : Source data sheet) (policy : Policy)
    (query : ObservationRequest) (count : Nat) {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → CachedModel) :
    (Observation.Basic.computation (IntegrationReplay.control (program source policy)) query count).run
      (Boundary.Trace.overlay (record source policy query count).trace (outside payload)) =
        ⟨.ok (record source policy query count).observation, (record source policy query
          count).trace⟩ :=
  Observation.Noninterference.payload_erasure (program source policy) query count payload outside

end Purelib.Integration.Algebraic.SquareFactor.PathObservation
