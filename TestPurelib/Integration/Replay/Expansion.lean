module

import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Expansion
import Purelib.Integration.Program.Gaussian.Exact
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Batteries.Lean.Except

/-! # Composed model evaluations and cached reply replay -/

namespace TestPurelib.Integration.Replay.Expansion

open Purelib
open Purelib.Computation.Query
open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.Basic
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Polynomial
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Transducer.Replay (Failure)
open Purelib.Approximation.Gaussian

/-- Form the original exact cached integration program for the supplied finite constant coefficient. -/
private def exact (coefficient : Gaussian) : CachedProgram :=
  (RefinementProgram.exactPolynomial 0 1 (Ascending.Gaussian.Basic.constant coefficient)).certifiedView.program

/-- The model handler consumes both actual root and numerator replies before constructing its exact cached model. -/
private def handler (index : Nat) : Protocol (Nat × Bool) Gaussian CachedModel :=
  (Protocol.query (index, false)).bind fun root =>
    (Protocol.query (index, true)).map fun numerator => (exact (numerator / root)).stage index

/-- Retain every numerical observation field and the exact replay machine, or its original failure. -/
private def retained (result : Except Failure Observation) :
    Except Failure ((Nat × Gaussian × Coordinate × Gaussian × Coordinate) × Replay.Machine) :=
  result.map fun observed =>
    ((observed.selected.index, observed.selected.sample, observed.selected.allowance,
      observed.selected.ball.center, observed.selected.ball.radiusSq), observed.machine)

/-- Read the exact ordered stage indices, samples and allowances retained by an outer model trace. -/
private def modelTrace (trace : Trace) :=
  trace.map fun entry => (entry.query, entry.reply.sample, entry.reply.allowance)

/-- Expand every retained model request into its two original root and numerator exchanges in order. -/
private def expectedInnerTrace (trace : Trace) : List ((Nat × Bool) × Gaussian) :=
  trace.flatMap fun entry => [((entry.query, false), 2), ((entry.query, true), 2)]

/-- Exercise all controller phases, pending queues and rejected residual reads through the shared construction. -/
private def checkMachines : IO Unit := do
  let source := exact 1
  let bounds := control source
  let cursor : Process.Recipe.Cursor := ⟨.source, 0⟩
  let modes : List Replay.Mode :=
    [.initial cursor, .low 2 cursor, .loop .loop 1 cursor (.ofLower 2), .residual cursor 0 (1 / 4)]
  for mode in modes do
    for pending in [[], [false, true]] do
      let machine : Replay.Machine := ⟨mode, [true, false], pending⟩
      for count in [0, 1, 2, 4] do
        let expanded := (Machine.advanceProgram bounds machine count).expand handler
        let observed := expanded.run (fun _ => 2)
        let original := (Machine.advance bounds machine count).run source.stage
        unless decide (observed.value.value = original.value) &&
            decide (modelTrace observed.value.trace = modelTrace original.trace) &&
            decide (observed.trace.map (fun entry => (entry.query, entry.reply)) =
              expectedInnerTrace observed.value.trace) do
          throw (IO.userError "shared controller changed a phase, pending bit, complete result or ordered model log")
        if count ≤ pending.length then
          unless observed.trace.isEmpty do
            throw (IO.userError "pending bits performed an unexpected model-handler callback")
  let residual : Replay.Machine := ⟨.residual cursor 0 (1 / 4), [], []⟩
  let rejected := ((Machine.advanceProgram bounds residual 4).expand handler).run
    (fun question => if question.2 then 2 else 1)
  match rejected.value.value with
  | .error (.source (.center _ _ _ _)) =>
      unless rejected.value.trace.length == 1 && rejected.trace.length == 2 do
        throw (IO.userError "rejected residual reply continued into the inverse branch or later finite steps")
  | _ => throw (IO.userError "changed residual source did not retain the original center-bound failure")

/-- Execute nested model handlers, checking both logs, replay, queued bits and consumed versus outside changes. -/
public def run : IO Unit := do
  checkMachines
  let source := exact 1
  let request : Integration.CertifiedProgram.Request := ⟨0, 1 / 16, by decide⟩
  let oracle : Nat × Bool → Gaussian := fun _ => 2
  for count in [0, 1, 3, 12, 30] do
    let computation := Observation.Expansion.computation handler (control source) request count
    let recorded := computation.run oracle
    let original := (Observation.Basic.computation (control source) request count).run source.stage
    unless decide (retained recorded.value.value = retained original.value) &&
        decide (modelTrace recorded.value.trace = modelTrace original.trace) &&
        decide (recorded.trace.map (fun entry => (entry.query, entry.reply)) =
          expectedInnerTrace recorded.value.trace) do
      throw (IO.userError "expanded integration lost the original observation or an internal model request")
    let changed := computation.run (Boundary.Trace.overlay recorded.trace (fun _ => 0))
    unless decide (retained changed.value.value = retained recorded.value.value) &&
        decide (modelTrace changed.value.trace = modelTrace recorded.value.trace) &&
        decide (changed.trace.map (fun entry => (entry.query, entry.reply)) =
          recorded.trace.map (fun entry => (entry.query, entry.reply))) do
      throw (IO.userError "outside root/evaluator replies changed the expanded integration execution")
    match computation.replayExact recorded.trace with
    | .error _ => throw (IO.userError "expanded integration rejected its complete internal request trace")
    | .ok replayed =>
        unless decide (retained replayed.value = retained original.value) &&
            decide (modelTrace replayed.trace = modelTrace original.trace) do
          throw (IO.userError "expanded integration replay lost the original observation or outer query log")
    let altered := computation.run (fun question => if question.2 then 2 else 1)
    match altered.value.value with
    | .error (.source (.center _ _ _ _)) =>
        unless altered.value.trace.length == 1 && altered.trace.length == 2 do
          throw (IO.userError "rejected selected model continued into later callbacks")
    | _ => throw (IO.userError "changed consumed root did not retain the original invalid model-bound result")
  IO.print "composed integration: phases, complete values, both logs, pending bits, rejection and replay passed\n"

end TestPurelib.Integration.Replay.Expansion
