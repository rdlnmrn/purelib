import CCL.Progressive.PartialDivision
import CCL.Progressive.PartialLogarithm

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

namespace CCL.ProgressivePartialLogQuotient

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev PossibleApart := CCL.ProgressiveCharts.PossibleApart

namespace Log
abbrev State := CCL.ProgressivePartialLogarithm.State
abbrev Progress {target : CoherentNamed} :=
  @CCL.ProgressivePartialLogarithm.Progress target
abbrev Requirement := CCL.ProgressivePartialLogarithm.Requirement
abbrev Evidence
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    (requirement : Requirement sourceInput targetInput source state) :=
  CCL.ProgressivePartialLogarithm.Evidence requirement
abbrev Ready := CCL.ProgressivePartialLogarithm.Ready
abbrev StepResult := CCL.ProgressivePartialLogarithm.StepResult
abbrev preparedTarget {target : CoherentNamed} (state : State target) :=
  CCL.ProgressivePartialLogarithm.preparedTarget state
abbrev step := CCL.ProgressivePartialLogarithm.step
abbrev satisfy := CCL.ProgressivePartialLogarithm.satisfy
end Log

namespace Division
abbrev State := CCL.ProgressivePartialDivision.State
abbrev Progress {denominator : CoherentNamed} :=
  @CCL.ProgressivePartialDivision.Progress denominator
abbrev Requirement {denominator : CoherentNamed}
    (state : State denominator) :=
  CCL.ProgressivePartialDivision.Requirement state
abbrev Evidence {denominator : CoherentNamed} {state : State denominator}
    (requirement : Requirement state) :=
  CCL.ProgressivePartialDivision.Evidence requirement
abbrev PreparationResult := CCL.ProgressivePartialDivision.PreparationResult
abbrev prepare := CCL.ProgressivePartialDivision.prepare
abbrev readyName := CCL.ProgressivePartialDivision.readyName
end Division

/-- Static data for the expression `log(1 + z) / z`.  The source anchor fixes
the intended local logarithm branch; its eventual overlap with `1 + z` is
supplied as typed evidence. -/
structure Client where
  denominator : CoherentNamed
  sourceInput : CoherentNamed
  source : AnchoredChart sourceInput

namespace Client

/-- The total child expression `1 + z`. -/
def argument (client : Client) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1) client.denominator

end Client

/-- Retained state of the anchored-logarithm child.  Once ready, its ordinary
anchored chart and validity proof are retained and never recomputed. -/
inductive LogSlot (client : Client) : Type 2
  | searching (state : Log.State client.argument)
  | ready (state : Log.State client.argument)
      (output : AnchoredChart (Log.preparedTarget state))
      (valid : Log.Ready client.sourceInput client.argument client.source
        state output)

/-- Retained state of denominator-only apartness acquisition. -/
inductive DenominatorSlot (client : Client) : Type
  | searching (state : Division.State client.denominator)
  | ready (state : Division.State client.denominator)
      (evidence : PossibleApart
        (CCL.ProgressiveCharts.based client.denominator.name.process
          state.source))

/-- Current finite dependency tree.  `cursor = false` gives the logarithm
child priority when both children are still pending; `true` gives the
denominator priority. -/
structure State (client : Client) : Type 2 where
  log : LogSlot client
  denominator : DenominatorSlot client
  cursor : Bool

namespace State

def initial (client : Client) : State client where
  log := .searching
    (CCL.ProgressivePartialLogarithm.State.initial client.argument)
  denominator := .searching
    (CCL.ProgressivePartialDivision.State.initial client.denominator)
  cursor := false

def withLogSearching {client : Client}
    (logState : Log.State client.argument)
    (denominator : DenominatorSlot client) (cursor : Bool) : State client :=
  { log := .searching logState, denominator := denominator, cursor := cursor }

def withLogReady {client : Client}
    (logState : Log.State client.argument)
    (output : AnchoredChart (Log.preparedTarget logState))
    (valid : Log.Ready client.sourceInput client.argument client.source
      logState output)
    (denominator : DenominatorSlot client) (cursor : Bool) : State client :=
  { log := .ready logState output valid
    denominator := denominator
    cursor := cursor }

def withDenominatorSearching {client : Client}
    (log : LogSlot client)
    (denominatorState : Division.State client.denominator)
    (cursor : Bool) : State client :=
  { log := log, denominator := .searching denominatorState, cursor := cursor }

def withDenominatorReady {client : Client}
    (log : LogSlot client)
    (denominatorState : Division.State client.denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based client.denominator.name.process
        denominatorState.source))
    (cursor : Bool) : State client :=
  { log := log
    denominator := .ready denominatorState evidence
    cursor := cursor }

end State

/-- Finite path of a partial child in this two-node dependency tree. -/
inductive NodePath
  | logarithm
  | denominator
  deriving DecidableEq

/-- One exact typed request together with the other retained child.  The
request itself determines the scheduler state to which evidence may resume. -/
inductive Blocked (client : Client) : Type 2
  | logarithm (logState : Log.State client.argument)
      (requirement : Log.Requirement client.sourceInput client.argument
        client.source logState)
      (denominator : DenominatorSlot client) (cursor : Bool)
  | denominator (denominatorState : Division.State client.denominator)
      (requirement : Division.Requirement denominatorState)
      (log : LogSlot client) (cursor : Bool)

namespace Blocked

def state {client : Client} : Blocked client → State client
  | .logarithm logState _ denominatorSlot cursor =>
      State.withLogSearching logState denominatorSlot cursor
  | .denominator denominatorState _ log cursor =>
      State.withDenominatorSearching log denominatorState cursor

def path {client : Client} : Blocked client → NodePath
  | .logarithm .. => .logarithm
  | .denominator .. => .denominator

/-- Evidence is indexed by the complete blocked request, including its exact
node path and retained child state. -/
def Evidence {client : Client} : Blocked client → Type
  | .logarithm _ requirement _ _ => Log.Evidence requirement
  | .denominator _ requirement _ _ => Division.Evidence requirement

/-- Resume only the child named by the blocked request.  The other child is
retained definitionally and the round-robin cursor advances once. -/
def resume {client : Client} (blocked : Blocked client)
    (evidence : Evidence blocked) : State client :=
  match blocked with
  | .logarithm logState requirement denominatorSlot cursor =>
      let satisfied := Log.satisfy client.sourceInput client.argument
        client.source logState requirement evidence
      State.withLogReady logState satisfied.output satisfied.valid denominatorSlot
        (!cursor)
  | .denominator denominatorState requirement log cursor =>
      match requirement with
      | .candidateApartness =>
          State.withDenominatorReady log denominatorState evidence (!cursor)

end Blocked

/-- Construct an explicit manual denominator-apartness request at the current
retained denominator state.  Automatic scheduling never fabricates this
evidence and may instead keep refining. -/
def requestDenominator {client : Client} (log : LogSlot client)
    (denominatorState : Division.State client.denominator) (cursor : Bool) :
    Blocked client :=
  .denominator denominatorState .candidateApartness log cursor

/-- The ordinary quotient produced after both children are ready. -/
def readyName (client : Client)
    (logState : Log.State client.argument)
    (logOutput : AnchoredChart (Log.preparedTarget logState))
    (denominatorState : Division.State client.denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based client.denominator.name.process
        denominatorState.source)) : CoherentNamed :=
  Division.readyName logOutput.output client.denominator denominatorState
    evidence

/-- Ready expression package.  It retains both child certificates, which is
what makes schedule-independence provable without recomputing either child. -/
structure Ready (client : Client) (output : CoherentNamed) : Type 2 where
  logState : Log.State client.argument
  logOutput : AnchoredChart (Log.preparedTarget logState)
  logValid : Log.Ready client.sourceInput client.argument client.source
    logState logOutput
  denominatorState : Division.State client.denominator
  denominatorEvidence : PossibleApart
    (CCL.ProgressiveCharts.based client.denominator.name.process
      denominatorState.source)
  output_eq : output = readyName client logState logOutput
    denominatorState denominatorEvidence

/-- One certified scheduler transition.  Readiness acquisition is progress:
it replaces one pending child by retained evidence and never recomputes it. -/
inductive Progress (client : Client) : State client → State client → Type 2
  | logRefined (logState next : Log.State client.argument)
      (progress : Log.Progress logState next)
      (denominatorSlot : DenominatorSlot client) (cursor : Bool) :
      Progress client
        (State.withLogSearching logState denominatorSlot cursor)
        (State.withLogSearching next denominatorSlot (!cursor))
  | logPrepared (logState : Log.State client.argument)
      (output : AnchoredChart (Log.preparedTarget logState))
      (valid : Log.Ready client.sourceInput client.argument client.source
        logState output)
      (denominatorSlot : DenominatorSlot client) (cursor : Bool) :
      Progress client
        (State.withLogSearching logState denominatorSlot cursor)
        (State.withLogReady logState output valid denominatorSlot (!cursor))
  | denominatorRefined (logSlot : LogSlot client)
      (denominatorState next : Division.State client.denominator)
      (progress : Division.Progress denominatorState next) (cursor : Bool) :
      Progress client
        (State.withDenominatorSearching logSlot denominatorState cursor)
        (State.withDenominatorSearching logSlot next (!cursor))
  | denominatorPrepared (logSlot : LogSlot client)
      (denominatorState : Division.State client.denominator)
      (evidence : PossibleApart
        (CCL.ProgressiveCharts.based client.denominator.name.process
          denominatorState.source))
      (cursor : Bool) :
      Progress client
        (State.withDenominatorSearching logSlot denominatorState cursor)
        (State.withDenominatorReady logSlot denominatorState evidence (!cursor))

/-- Finite reachability contains only the current dependency-tree states, not
an unbounded execution log. -/
inductive Reachable {client : Client} : State client → State client → Type 2
  | refl (state : State client) : Reachable state state
  | tail {start middle finish : State client} :
      Progress client start middle → Reachable middle finish →
        Reachable start finish

/-- One global scheduler tick. -/
inductive StepResult (client : Client) (current : State client) : Type 2
  | ready (output : CoherentNamed) (valid : Ready client output)
  | progressed (next : State client) (progress : Progress client current next)
  | blocked (request : Blocked client) (retained : request.state = current)

/-- Advance the logarithm child by exactly one operation-specific action. -/
def advanceLog (client : Client)
    (logState : Log.State client.argument)
    (denominatorSlot : DenominatorSlot client) (cursor : Bool) :
    StepResult client (State.withLogSearching logState denominatorSlot cursor) :=
  match Log.step client.sourceInput client.argument client.source logState with
  | .ready output valid =>
      .progressed
        (State.withLogReady logState output valid denominatorSlot (!cursor))
        (.logPrepared logState output valid denominatorSlot cursor)
  | .progressed next progress =>
      .progressed
        (State.withLogSearching next denominatorSlot (!cursor))
        (.logRefined logState next progress denominatorSlot cursor)
  | .blocked requirement =>
      .blocked (.logarithm logState requirement denominatorSlot cursor) rfl

/-- Advance denominator-only preparation by exactly one operation-specific
action.  It is independent of the not-yet-ready logarithm numerator. -/
def advanceDenominator (client : Client) (logSlot : LogSlot client)
    (denominatorState : Division.State client.denominator) (cursor : Bool) :
    StepResult client
      (State.withDenominatorSearching logSlot denominatorState cursor) :=
  match Division.prepare client.denominator denominatorState with
  | .prepared evidence =>
      .progressed
        (State.withDenominatorReady logSlot denominatorState evidence (!cursor))
        (.denominatorPrepared logSlot denominatorState evidence cursor)
  | .progressed next progress =>
      .progressed
        (State.withDenominatorSearching logSlot next (!cursor))
        (.denominatorRefined logSlot denominatorState next progress cursor)

/-- Deterministic round-robin scheduler.  If only one child is pending it is
selected directly; if both are pending, `cursor` selects the next child. -/
def step (client : Client) : (state : State client) → StepResult client state
  | ⟨.ready logState logOutput logValid,
      .ready denominatorState denominatorEvidence, _cursor⟩ =>
      let output := readyName client logState logOutput denominatorState
        denominatorEvidence
      .ready output
        { logState := logState
          logOutput := logOutput
          logValid := logValid
          denominatorState := denominatorState
          denominatorEvidence := denominatorEvidence
          output_eq := rfl }
  | ⟨.ready logState logOutput logValid,
      .searching denominatorState, cursor⟩ =>
      advanceDenominator client (.ready logState logOutput logValid)
        denominatorState cursor
  | ⟨.searching logState,
      .ready denominatorState denominatorEvidence, cursor⟩ =>
      advanceLog client logState
        (.ready denominatorState denominatorEvidence) cursor
  | ⟨.searching logState, .searching denominatorState, cursor⟩ =>
      if cursor then
        advanceDenominator client (.searching logState) denominatorState cursor
      else
        advanceLog client logState (.searching denominatorState) cursor

/-! ## Ready-output laws -/

/-- Any two successful schedules for the same fixed source anchor and input
produce operationally equivalent quotient names. -/
def ready_respects {client : Client} {firstOutput secondOutput : CoherentNamed}
    (first : Ready client firstOutput) (second : Ready client secondOutput) :
    NamedEquivalent firstOutput.name secondOutput.name := by
  rcases first with
    ⟨firstLogState, firstLogOutput, firstLogValid,
      firstDenominatorState, firstEvidence, rfl⟩
  rcases second with
    ⟨secondLogState, secondLogOutput, secondLogValid,
      secondDenominatorState, secondEvidence, rfl⟩
  let firstDenominator :=
    CCL.ProgressivePartialDivision.preparedDenominator
      firstDenominatorState firstEvidence
  let secondDenominator :=
    CCL.ProgressivePartialDivision.preparedDenominator
      secondDenominatorState secondEvidence
  have numeratorEquivalent : NamedEquivalent
      firstLogOutput.output.name secondLogOutput.output.name :=
    CCL.ProgressivePartialLogarithm.ready_respects
      firstLogValid secondLogValid
  have denominatorEquivalent : NamedEquivalent
      firstDenominator.name secondDenominator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.ProgressivePartialDivision.preparedDenominatorEquivalent
          firstDenominatorState firstEvidence))
      (CCL.ProgressivePartialDivision.preparedDenominatorEquivalent
        secondDenominatorState secondEvidence)
  simpa only [readyName, CCL.ProgressivePartialDivision.readyName,
    firstDenominator, secondDenominator,
    CCL.ProgressiveCoherence.CoherentNamed.div] using
    CCL.ProgressiveDivisionCongruence.coherentDiv_respects
      firstLogOutput.output secondLogOutput.output
      firstDenominator secondDenominator
      (CCL.ProgressivePartialDivision.preparedApart
        firstDenominatorState firstEvidence)
      (CCL.ProgressivePartialDivision.preparedApart
        secondDenominatorState secondEvidence)
      numeratorEquivalent denominatorEquivalent

/-- A ready expression is an ordinary productive coherent name. -/
theorem ready_productive {client : Client} {output : CoherentNamed}
    (_ready : Ready client output) (count : Nat) :
    output.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance output.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        output.name.machine count).emitted.length = count :=
  output.name.productive count

/-- Resuming a logarithm request retains the denominator child exactly. -/
theorem resume_logarithm_preserves_denominator {client : Client}
    (logState : Log.State client.argument)
    (requirement : Log.Requirement client.sourceInput client.argument
      client.source logState)
    (denominatorSlot : DenominatorSlot client) (cursor : Bool)
    (evidence : Blocked.Evidence
      (.logarithm logState requirement denominatorSlot cursor)) :
    (Blocked.resume (.logarithm logState requirement denominatorSlot cursor)
      evidence).denominator = denominatorSlot := by
  cases requirement <;> rfl

/-- Resuming a denominator request retains the logarithm child exactly. -/
theorem resume_denominator_preserves_log {client : Client}
    (denominatorState : Division.State client.denominator)
    (requirement : Division.Requirement denominatorState)
    (logSlot : LogSlot client) (cursor : Bool)
    (evidence : Blocked.Evidence
      (.denominator denominatorState requirement logSlot cursor)) :
    (Blocked.resume (.denominator denominatorState requirement logSlot cursor)
      evidence).log = logSlot := by
  cases requirement
  rfl

/-! ## Caller-bounded execution -/

inductive RunKind
  | ready
  | blocked
  | exhausted
  deriving DecidableEq

inductive RunPayload (client : Client) (state : State client) :
    RunKind → Type 2
  | ready (output : CoherentNamed) (valid : Ready client output) :
      RunPayload client state .ready
  | blocked (request : Blocked client) (retained : request.state = state) :
      RunPayload client state .blocked
  | exhausted : RunPayload client state .exhausted

/-- A bounded run retains one current dependency-tree state and finite
reachability from its start. -/
structure RunResult (client : Client) (start : State client) : Type 2 where
  kind : RunKind
  state : State client
  reachable : Reachable start state
  payload : RunPayload client state kind

def exhaustedResult (client : Client) (state : State client) :
    RunResult client state where
  kind := .exhausted
  state := state
  reachable := .refl state
  payload := .exhausted

def readyResult (client : Client) (state : State client)
    (output : CoherentNamed) (valid : Ready client output) :
    RunResult client state where
  kind := .ready
  state := state
  reachable := .refl state
  payload := .ready output valid

def blockedResult (client : Client) (state : State client)
    (request : Blocked client) (retained : request.state = state) :
    RunResult client state where
  kind := .blocked
  state := state
  reachable := .refl state
  payload := .blocked request retained

def prefixResult {client : Client} {start next : State client}
    (progress : Progress client start next) (later : RunResult client next) :
    RunResult client start where
  kind := later.kind
  state := later.state
  reachable := .tail progress later.reachable
  payload := later.payload

/-- Structurally recursive scheduler.  One unit of fuel performs at most one
operation-specific child action; blocked and ready results consume no further
fuel. -/
def attempt (client : Client) (state : State client) :
    Nat → RunResult client state
  | 0 => exhaustedResult client state
  | fuel + 1 =>
      match step client state with
      | .ready output valid => readyResult client state output valid
      | .blocked request retained =>
          blockedResult client state request retained
      | .progressed next progress =>
          prefixResult progress (attempt client next fuel)

@[simp] theorem attempt_zero (client : Client) (state : State client) :
    attempt client state 0 = exhaustedResult client state := rfl

end CCL.ProgressivePartialLogQuotient
