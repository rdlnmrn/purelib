module

public import Purelib.Integration.Algebraic.SquareFactor.PathObservation
public import Purelib.Integration.Algebraic.SquareFactor.IntegrationProgram.Observation
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Expansion

open Purelib.CCL.Progressive

/-!
# Canonical path observations with original source construction displayed

Initial isolation, preparation and cell construction run once and return
the original initial layer. Every model handler starts from that same
retained layer and records its actual chronological refinement requests.
The original observer consumes the resulting cached models, retaining its
complete outer execution and ordered inner source trace. Replay invokes
neither initial preparation nor subsequent source callbacks.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.PathObservation

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query
open Purelib.Integration.Program.Gaussian.CCL.Replay

namespace Expansion

variable {polynomial : SquareFactor.GaussianPolynomial} {differential : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial differential} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment}

/-- The original unit-accuracy request used once by initial source preparation. -/
def initialResolution (safe : data.Safe) := Accuracy.resolve safe 1 (by decide) 1 (by decide)

/-- The original initialization questions at its exact canonical unit request. -/
abbrev InitialQuestion (safe : data.Safe) (sheet : Fin 2) :=
  IntegrationLayers.Observation.InitialQuestion safe sheet (initialResolution safe)

/-- The original initialization replies at the same exact unit request. -/
abbrev InitialReply (safe : data.Safe) (sheet : Fin 2) :=
  IntegrationLayers.Observation.InitialReply safe sheet (initialResolution safe)

/-- Chronological source questions retaining the original canonical initial-layer identity. -/
abbrev RefinementQuestion (safe : data.Safe) (sheet : Fin 2) :=
  IntegrationProgram.Observation.Question (IntegrationLayers.initial safe sheet)

/-- Original chronological source replies at the same retained canonical initial-layer owner. -/
abbrev RefinementReply (safe : data.Safe) (sheet : Fin 2) :=
  IntegrationProgram.Observation.Reply (IntegrationLayers.initial safe sheet)

set_option genInjectivity false in
/-- An actual original initialization or chronological-refinement source request below the model-query boundary. -/
inductive Question (safe : data.Safe) (sheet : Fin 2) where
  /-- Request the original initial isolation, mesh preparation or cell reading. -/ | initial
      (question : InitialQuestion safe sheet)
  /-- Request an actual original successor's selected mesh or cell reading. -/ | refinement
      (question : RefinementQuestion safe sheet)
  deriving @[expose] DecidableEq

set_option genInjectivity false in
/-- The actual complete source reply with its original initialization or chronological ownership. -/
inductive Reply (safe : data.Safe) (sheet : Fin 2) where
  /-- Retain the original initial owner, mesh or cell reply. -/ | initial (reply : InitialReply safe sheet)
  /-- Retain an actual chronological successor's selection or cell reply. -/ | refinement
      (reply : RefinementReply safe sheet)

set_option genInjectivity false in
/-- A reply has the wrong source-construction stage or violates its original checking boundary. -/
inductive Invalidity where
  /-- Initial construction received a successor reply. -/ | expectedInitial
  /-- Successor construction received an initial reply. -/ | expectedRefinement
  /-- Retain the original initialization invalidity. -/ | initial (invalid : OwnedCells.Preparation.Invalidity)
  /-- Retain the original chronological invalidity and its complete position evidence. -/ | refinement
      (invalid : IntegrationProgram.Observation.Invalidity)

/-- The complete original outer observation value and ordered model-query execution. -/
abbrev Execution := Basic.Execution Nat CachedModel (Except Data.CCL.Transducer.Replay.Failure Observation)

/-- Execute original initialization once per request or use the actual parent carried by a chronological question. -/
def answer (safe : data.Safe) (sheet : Fin 2) : Question safe sheet → Reply safe sheet :=
  let resolution := initialResolution safe
  fun question =>
    match question with
    | .initial question => .initial (IntegrationLayers.Observation.initialAnswer safe sheet resolution question)
    | .refinement question => .refinement (IntegrationProgram.Observation.answer question)

/-- Forward an actual initialization request and reject a chronological reply at that boundary. -/
private def initialHandler (safe : data.Safe) (sheet : Fin 2) (question : InitialQuestion safe sheet) :
    Program (Question safe sheet) (Reply safe sheet) (Except Invalidity (InitialReply safe sheet)) :=
  (Program.query (.initial question)).map fun reply =>
    match reply with
    | .initial actual => .ok actual
    | .refinement _ => .error .expectedInitial

/-- Forward an actual successor source request and reject an initialization reply at that boundary. -/
private def refinementHandler (safe : data.Safe) (sheet : Fin 2) (question : RefinementQuestion safe sheet) :
    Program (Question safe sheet) (Reply safe sheet) (Except Invalidity (RefinementReply safe sheet)) :=
  (Program.query (.refinement question)).map fun reply =>
    match reply with
    | .initial _ => .error .expectedRefinement
    | .refinement actual => .ok actual

/-- Build the original initial layer once, retaining its actual returned caches and complete construction identity. -/
private def initialProgram (safe : data.Safe) (sheet : Fin 2) :
    Program (Question safe sheet) (Reply safe sheet)
      (Except Invalidity (IntegrationLayers.Observation.InitialRealization safe sheet)) :=
  let resolution := initialResolution safe
  ((IntegrationLayers.Observation.initialProgram safe sheet resolution rfl).substituteChecked
    (initialHandler safe sheet)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed => executed.value.mapError Invalidity.initial

/-- Read the complete original stage cache from the actual returned layer without reconstructing its source. -/
private def cachedLayer {safe : data.Safe} {sheet : Fin 2} {index : Nat}
    (actual : IntegrationProgram.Observation.Realization (IntegrationLayers.initial safe sheet) index) : CachedModel :=
  (IntegrationProgram.Observation.ModelRealization.ofLayer actual).val

/-- Construct a model request from the shared actual initial layer and its displayed chronological source calls. -/
private def modelProgram (safe : data.Safe) (sheet : Fin 2)
    (start : IntegrationLayers.Observation.InitialRealization safe sheet) (index : Nat) :
    Program (Question safe sheet) (Reply safe sheet) (Except Invalidity CachedModel) :=
  let actual := IntegrationProgram.Observation.program start.val index
  let retained := IntegrationProgram.Observation.castStart start.property actual
  (retained.substituteChecked (refinementHandler safe sheet)).map fun result =>
    match result with
    | .error invalid => .error invalid
    | .ok executed =>
        match executed.value with
        | .error invalid => .error (.refinement invalid)
        | .ok layer => .ok (cachedLayer layer)

/-- Continue the original observer on the shared retained initial source, exposing every reached model handler. -/
private def continueObservation (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat)
    (result : Except Invalidity (IntegrationLayers.Observation.InitialRealization safe sheet)) :
    Program (Question safe sheet) (Reply safe sheet) (Except Invalidity Execution) :=
  match result with
  | .error invalid => .pure (.error invalid)
  | .ok start =>
      let source := Source.ofInitial safe sheet start.val start.property
      let control := IntegrationReplay.control source.value
      (Observation.Expansion.program control query count).substituteChecked (modelProgram safe sheet start)

/-- Construct the canonical original path observer with initial preparation once and all actual model source calls. -/
def program (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    Program (Question safe sheet) (Reply safe sheet) (Except Invalidity Execution) :=
  (initialProgram safe sheet).bind (continueObservation safe sheet query count)

/-- Record the canonical original observer, its complete outer model log and ordered initialization/refinement trace. -/
def computation (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    Protocol (Question safe sheet) (Reply safe sheet) (Except Invalidity Execution) :=
  (program safe sheet query count).protocol

/-- Original initialization replies retain the same original initial layer and its complete cache identity. -/
private theorem initialProgram_value (safe : data.Safe) (sheet : Fin 2) :
    ((initialProgram safe sheet).protocol.run (answer safe sheet)).value =
      .ok ⟨IntegrationLayers.initial safe sheet, rfl⟩ := by
  rewrite [initialProgram, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _
      (IntegrationLayers.Observation.initialAnswer safe sheet (initialResolution safe)) (fun _ => rfl)]
  dsimp only
  rewrite [IntegrationLayers.Observation.initialProgram_value]
  rfl

/-- The actual returned chronological layer supplies the same complete original canonical stage cache. -/
private theorem cachedLayer_eq {safe : data.Safe} {sheet : Fin 2} {index : Nat}
    (actual : IntegrationProgram.Observation.Realization (IntegrationLayers.initial safe sheet) index) :
    cachedLayer actual = (IntegrationProgram.cached safe sheet).stage index :=
  (IntegrationProgram.Observation.ModelRealization.ofLayer actual).property.trans
    (congrArg (fun source => source.stage index)
      (IntegrationProgram.cachedFrom_eq_cached safe sheet (IntegrationLayers.initial safe sheet) rfl))

/-- Every actual model handler preserves the exact original stage while consuming the shared returned initial layer. -/
private theorem modelProgram_value (safe : data.Safe) (sheet : Fin 2)
    (start : IntegrationLayers.Observation.InitialRealization safe sheet) (index : Nat) :
    ((modelProgram safe sheet start index).protocol.run (answer safe sheet)).value =
      .ok ((IntegrationProgram.cached safe sheet).stage index) := by
  cases start with
  | mk start same =>
      cases same
      rewrite [modelProgram]
      dsimp only [IntegrationProgram.Observation.castStart]
      rewrite [Program.map_execution, Protocol.map_run_value,
        Program.substituteChecked_value _ _ _ IntegrationProgram.Observation.answer (fun _ => rfl)]
      dsimp only
      rewrite [IntegrationProgram.Observation.program_value]
      exact congrArg Except.ok (cachedLayer_eq _)

/-- The shared original source and exact stage handlers preserve the complete original observer execution. -/
private theorem continueObservation_value (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat)
    (start : IntegrationLayers.Observation.InitialRealization safe sheet) :
    ((continueObservation safe sheet query count (.ok start)).protocol.run (answer safe sheet)).value =
      .ok ((Observation.Basic.computation (IntegrationReplay.control
        (IntegrationProgram.cached safe sheet)) query count).run (IntegrationProgram.cached safe sheet).stage) := by
  rewrite [continueObservation, Program.substituteChecked_value _ _ _ (IntegrationProgram.cached safe sheet).stage
    (modelProgram_value safe sheet start)]
  rewrite [Source.ofInitial_eq_canonical]
  exact congrArg Except.ok (Observation.Expansion.program_execution _ _ _ _)

/-- The canonical expanded source returns exactly the original whole observer execution and ordered model log. -/
private theorem program_value_spec (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    ((program safe sheet query count).protocol.run (answer safe sheet)).value =
      .ok ((Observation.Basic.computation (IntegrationReplay.control
        (IntegrationProgram.cached safe sheet)) query count).run (IntegrationProgram.cached safe sheet).stage) := by
  rewrite [program, Program.bind_execution, Protocol.bind_run_value, initialProgram_value]
  exact continueObservation_value safe sheet query count _

/-- The canonical construction retains the complete original observation and every model-query occurrence. -/
theorem program_value (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    ((program safe sheet query count).protocol.run (answer safe sheet)).value =
      .ok ((Observation.Basic.computation (IntegrationReplay.control
        (IntegrationProgram.cached safe sheet)) query count).run (IntegrationProgram.cached safe sheet).stage) :=
  program_value_spec safe sheet query count

/-- Complete execution retains the original outer observer and its actual ordered source-construction trace. -/
theorem computation_execution (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    let computation := computation safe sheet query count
    let oracle := answer safe sheet
    computation.run oracle =
      ⟨.ok ((Observation.Basic.computation (IntegrationReplay.control
        (IntegrationProgram.cached safe sheet)) query count).run (IntegrationProgram.cached safe sheet).stage),
        (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (program_value safe sheet query count) rfl

/-- Replay recovers the complete original observer from saved initialization and refinement receipts. -/
theorem computation_replay (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat) :
    let computation := computation safe sheet query count
    let oracle := answer safe sheet
    computation.replayExact (computation.run oracle).trace =
      .ok (.ok ((Observation.Basic.computation (IntegrationReplay.control
        (IntegrationProgram.cached safe sheet)) query count).run (IntegrationProgram.cached safe sheet).stage)) :=
  ((computation safe sheet query count).replayExact_run _).trans
    (congrArg Except.ok (program_value safe sheet query count))

/-- Changes outside reached canonical source requests preserve both complete executions and their ordered logs. -/
theorem payload_erasure {Payload : Type} (safe : data.Safe) (sheet : Fin 2) (query : ObservationRequest) (count : Nat)
    (payload : Payload) (outside : Payload → Question safe sheet → Reply safe sheet) :
    let computation := computation safe sheet query count
    let oracle := answer safe sheet
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (computation safe sheet query count) (answer safe sheet) payload outside

end Expansion

end Purelib.Integration.Algebraic.SquareFactor.PathObservation
