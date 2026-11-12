module

public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Step
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Algebraic denominator evidence for the logarithm quotient scheduler

The original scheduler state and its logarithm child remain intact. An exact
algebraic denominator decision can retain an equivalent prepared presentation
alongside that state, or identify the original zero denominator.
-/

public section

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.Algebraic

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Provenance

/-- A preparation computed by the original denominator sidecar's decision. -/
@[expose] def CachedPreparation (client : Client) (sidecar : Provenance.Algebraic.Sidecar client.denominator) :=
  { prepared : Division.Prepared client.denominator // sidecar.decide = .prepared prepared }

set_option genInjectivity false in
/-- The original scheduler state, sidecar and optional completed denominator decision. -/
structure Cursor (client : Client) (sidecar : Provenance.Algebraic.Sidecar client.denominator) where
  /-- The complete original dependency-tree state. -/
  current : Quotient.State client
  /-- The actual original algebraic denominator evidence. -/
  source : Provenance.Algebraic.Sidecar client.denominator
  /-- The retained source is the supplied sidecar. -/
  source_eq : source = sidecar
  /-- The exact prepared denominator computed for the same sidecar, when available. -/
  preparation : Option (CachedPreparation client source)

constructive_injectivity Cursor

/-- Begin with the original scheduler state and sidecar, before its algebraic decision. -/
@[expose] def Cursor.start {client : Client} (sidecar : Provenance.Algebraic.Sidecar client.denominator)
    (state : Quotient.State client) : Cursor client sidecar := ⟨state, sidecar, rfl, none⟩

/-- Resume an original blocked request while retaining the completed algebraic preparation. -/
@[expose] def Cursor.resume {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (cursor : Cursor client sidecar) (request : Quotient.Requirement.Blocked client)
    (_atState : request.state = cursor.current) (evidence : request.Evidence) : Cursor client sidecar :=
  ⟨request.resume evidence, cursor.source, cursor.source_eq, cursor.preparation⟩

/-- Resuming a blocked child retains the complete original sidecar. -/
theorem Cursor.resume_source {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (cursor : Cursor client sidecar) (request : Quotient.Requirement.Blocked client)
    (atState : request.state = cursor.current) (evidence : request.Evidence) :
    (cursor.resume request atState evidence).source = cursor.source := rfl

/-- Resuming a blocked child does not recompute or replace the cached preparation. -/
theorem Cursor.resume_preparation {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (cursor : Cursor client sidecar) (request : Quotient.Requirement.Blocked client)
    (atState : request.state = cursor.current) (evidence : request.Evidence) :
    (cursor.resume request atState evidence).preparation = cursor.preparation := rfl

set_option genInjectivity false in
/-- One original scheduler action or one retained algebraic denominator decision. -/
inductive Progress {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator} :
    Cursor client sidecar → Cursor client sidecar → Type 2 where
  /-- Reuse an original scheduler transition while keeping the existing preparation cache. -/
  | original {first second : Quotient.State client} (source : Provenance.Algebraic.Sidecar client.denominator)
      (same : source = sidecar) (cached : Option (CachedPreparation client source))
      (transition : Quotient.Step.Progress client first second) :
      Progress ⟨first, source, same, cached⟩ ⟨second, source, same, cached⟩
  /-- Retain the computed preparation and toggle the original scheduling priority once. -/
  | certified (source : Provenance.Algebraic.Sidecar client.denominator) (same : source = sidecar)
      (log : Quotient.State.LogSlot client)
      (denominator : Name.Coherent.Refinement.State client.denominator) (cursor : Bool)
      (prepared : Division.Prepared client.denominator) (computed : source.decide = .prepared prepared) :
      Progress ⟨Quotient.State.withDenominatorSearching log denominator cursor, source, same, none⟩
        ⟨Quotient.State.withDenominatorSearching log denominator (!cursor), source, same, some ⟨prepared, computed⟩⟩

constructive_injectivity Progress

set_option genInjectivity false in
/-- One scheduler outcome retaining its exact original state and any completed preparation. -/
inductive Result {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (cursor : Cursor client sidecar) : Type 2 where
  /-- Return an ordinary original-scheduler quotient. -/
  | ready (retained : Cursor client sidecar) (same : retained = cursor)
      (output : Name.Coherent.CoherentNamed) (valid : Quotient.Ready client output)
  /-- Return the quotient using the actual retained equivalent preparation. -/
  | readyPrepared (retained : Cursor client sidecar) (same : retained = cursor)
      (cached : CachedPreparation client retained.source) (selected : retained.preparation = some cached)
      (output : Name.Coherent.CoherentNamed) (valid : Quotient.PreparedReady client output)
      (uses : valid.denominator = cached.val)
      (log_eq : retained.current.log = .ready valid.logState valid.logOutput valid.logValid)
  /-- Retain the next state and its certified single action. -/
  | progressed (next : Cursor client sidecar) (progress : Progress cursor next)
  /-- Keep the entire original cursor and the exact blocked child request. -/
  | blocked (retained : Cursor client sidecar) (same : retained = cursor)
      (request : Quotient.Requirement.Blocked client) (atState : request.state = retained.current)
  /-- Keep the cursor and the exact zero identity for the original denominator. -/
  | excluded (retained : Cursor client sidecar) (same : retained = cursor)
      (zero : Equivalence.Zero.ZeroIdentity client.denominator) (computed : retained.source.decide = .excluded zero)

constructive_injectivity Result

/-- Lift an original scheduler action without changing its retained algebraic cache. -/
@[expose] def lift {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (cursor : Cursor client sidecar) (result : Quotient.Step.StepResult client cursor.current) : Result cursor :=
  match cursor with
  | ⟨current, source, same, cached⟩ => match result with
    | .ready output valid => .ready ⟨current, source, same, cached⟩ rfl output valid
    | .progressed next transition => .progressed ⟨next, source, same, cached⟩
        (.original source same cached transition)
    | .blocked request atState => .blocked ⟨current, source, same, cached⟩ rfl request atState

/-- Perform the selected denominator action using its original algebraic decision. -/
@[expose] def decideDenominator {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator}
    (source : Provenance.Algebraic.Sidecar client.denominator) (same : source = sidecar)
    (log : Quotient.State.LogSlot client) (denominator : Name.Coherent.Refinement.State client.denominator)
    (priority : Bool) : Result
      ⟨Quotient.State.withDenominatorSearching log denominator priority, source, same, none⟩ :=
  match computed : source.decide with
  | .excluded zero => .excluded _ rfl zero computed
  | .prepared prepared => .progressed
      ⟨Quotient.State.withDenominatorSearching log denominator (!priority), source, same, some ⟨prepared, computed⟩⟩
      (.certified source same log denominator priority prepared computed)

/-- Perform at most the original scheduler's selected child action.

The algebraic decision replaces only a selected pending denominator action.
After it succeeds, later ticks reuse its exact preparation while continuing
the original logarithm child and preserving blocked overlap requests. An
already ready original denominator keeps its existing scheduler behavior. -/
@[expose] def step {client : Client} {sidecar : Provenance.Algebraic.Sidecar client.denominator} :
    (cursor : Cursor client sidecar) → Result cursor
  | ⟨⟨.ready logState logOutput logValid, .ready denominator evidence, priority⟩, source, same, cached⟩ =>
      let current := Quotient.State.withLogReady logState logOutput logValid (.ready denominator evidence) priority
      lift ⟨current, source, same, cached⟩ (Quotient.Step.step client current)
  | ⟨⟨.ready logState logOutput logValid, _denominator, _priority⟩, _source, _same, some cached⟩ =>
      let output := cached.val.quotient (AnchoredChart.output logOutput)
      .readyPrepared _ rfl cached rfl output ⟨logState, logOutput, logValid, cached.val, rfl⟩ rfl rfl
  | ⟨⟨.searching logState, denominator, priority⟩, source, same, some cached⟩ =>
      lift ⟨⟨.searching logState, denominator, priority⟩, source, same, some cached⟩
        (Quotient.Step.advanceLog client logState denominator priority)
  | ⟨⟨.ready logState logOutput logValid, .searching denominator, priority⟩, source, same, none⟩ =>
      decideDenominator source same (.ready logState logOutput logValid) denominator priority
  | ⟨⟨.searching logState, .searching denominator, true⟩, source, same, none⟩ =>
      decideDenominator source same (.searching logState) denominator true
  | ⟨state, source, same, none⟩ => lift ⟨state, source, same, none⟩ (Quotient.Step.step client state)

end Purelib.Approximation.Gaussian.Logarithm.Quotient.Algebraic

end
