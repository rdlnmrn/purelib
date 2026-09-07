import CCL.Transcendental.LogChartCongruence

/-!
# Retryable finite preflight for one anchored logarithm branch

The source anchor fixes the logarithm branch.  Automatic work refines one
target coherent name until an executable rational chart-safety certificate is
visible.  Generic finite refinement cannot construct semantic overlap between
two unrelated `Possible` predicates, so success of the safety test returns a
typed `blocked` requirement for an overlap witness at the exact prepared target
state.  Supplying that witness resumes directly into the existing
`SafeOverlapExtension.transport` operation.

No output name is exposed before readiness.  Failure of a safety test performs
one certified refinement and never proves that the input is zero or outside a
logarithm domain.
-/

namespace CCL.ProgressivePartialLogarithm

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev OverlapWitness := CCL.LogBranchGeometry.OverlapWitness
abbrev SafeOverlapExtension := CCL.LogBranchGeometry.SafeOverlapExtension
abbrev SafetyCertificate := CCL.LogChartSafety.Certificate

/-- Retained automatic-search state for one fixed target name. -/
structure State (target : CoherentNamed) where
  source : target.name.process.State
  nextIndex : Nat
  persists : ∀ {value : Gaussian},
    target.name.process.Possible source value →
      target.name.process.Possible target.name.state value

namespace State

def initial (target : CoherentNamed) : State target where
  source := target.name.state
  nextIndex := 0
  persists := fun possible => possible

def advance {target : CoherentNamed} (state : State target) : State target where
  source := target.name.process.refine state.source
    (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex)
  nextIndex := state.nextIndex + 1
  persists := fun possible =>
    state.persists
      (target.name.process.refine_persists state.source
        (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
        (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex)
        possible)

@[simp] theorem initial_source (target : CoherentNamed) :
    (initial target).source = target.name.state := rfl

@[simp] theorem initial_nextIndex (target : CoherentNamed) :
    (initial target).nextIndex = 0 := rfl

@[simp] theorem advance_source {target : CoherentNamed} (state : State target) :
    state.advance.source = target.name.process.refine state.source
      (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
      (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex) := rfl

@[simp] theorem advance_nextIndex {target : CoherentNamed}
    (state : State target) :
    state.advance.nextIndex = state.nextIndex + 1 := rfl

end State

/-- One certified automatic refinement step. -/
inductive Progress {target : CoherentNamed} : State target → State target → Prop
  | refined (state : State target) : Progress state state.advance

namespace Progress

theorem possible_persists {target : CoherentNamed}
    {current next : State target} (progress : Progress current next)
    {value : Gaussian}
    (possible : target.name.process.Possible next.source value) :
    target.name.process.Possible current.source value := by
  cases progress
  exact target.name.process.refine_persists current.source
    (CCL.ProgressiveSampling.refinementTarget current.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos current.nextIndex)
    possible

@[simp] theorem nextIndex_eq {target : CoherentNamed}
    {current next : State target} (progress : Progress current next) :
    next.nextIndex = current.nextIndex + 1 := by
  cases progress
  rfl

end Progress

/-- Finite reachability generated only by genuine refinement progress. -/
inductive Reachable {target : CoherentNamed} : State target → State target → Prop
  | refl (state : State target) : Reachable state state
  | tail {start middle finish : State target} :
      Progress start middle → Reachable middle finish → Reachable start finish

namespace Reachable

theorem possible_persists {target : CoherentNamed}
    {start finish : State target} (reachable : Reachable start finish)
    {value : Gaussian}
    (possible : target.name.process.Possible finish.source value) :
    target.name.process.Possible start.source value := by
  induction reachable with
  | refl state => exact possible
  | tail progress later inductionHypothesis =>
      exact progress.possible_persists (inductionHypothesis possible)

end Reachable

/-- The coherent target restricted to the successful finite refinement
future. -/
def preparedTarget {target : CoherentNamed} (state : State target) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.based target state.source

/-- Every prepared target retains the operational value of the original
target name. -/
def preparedTargetEquivalent {target : CoherentNamed} (state : State target) :
    NamedEquivalent target.name (preparedTarget state).name :=
  CCL.ProgressiveCoherence.CoherentNamed.basedEquivalent target state.source

/-- Prepared targets reached on two different finite schedules remain
operationally equivalent. -/
def preparedTargetsEquivalent {target : CoherentNamed}
    (first second : State target) :
    NamedEquivalent (preparedTarget first).name (preparedTarget second).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (preparedTargetEquivalent first))
    (preparedTargetEquivalent second)

/-- Typed evidence requests at one exact retained target state.  The overlap
constructor retains the already discovered automatic safety proof.  A complete
extension can be supplied directly when family-specific geometry has already
constructed it. -/
inductive Requirement
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) : Type
  | overlap
      (certificate : SafetyCertificate source.chart.factor
        (targetInput.name.process.ball state.source) state.nextIndex)
  | completeExtension

/-- Anchored-logarithm preflight has no automatic exclusion verdict.  Failure
of the finite safety test can justify refinement, but it cannot construct a
proof that no logarithm branch exists. -/
inductive Exclusion
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) : Type

/-- Evidence is indexed by the exact source anchor, target, state, and
requirement which requested it. -/
def Evidence
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput} :
    Requirement sourceInput targetInput source state → Type
  | .overlap _ => OverlapWitness sourceInput (preparedTarget state)
  | .completeExtension =>
      SafeOverlapExtension sourceInput (preparedTarget state) source

/-- A ready branch is exactly the transport through one displayed safe overlap
extension. -/
structure Ready
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (output : AnchoredChart (preparedTarget state)) : Type where
  extension : SafeOverlapExtension sourceInput (preparedTarget state) source
  output_eq : output = extension.transport source

/-- One operation-specific finite step.  `blocked` exposes an exact typed
requirement at the unchanged state. -/
inductive StepResult
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) : Type 2
  | ready (output : AnchoredChart (preparedTarget state))
      (valid : Ready sourceInput targetInput source state output)
  | progressed (next : State targetInput) (progress : Progress state next)
  | blocked (requirement : Requirement sourceInput targetInput source state)

/-- Assemble a ready result from a complete safe overlap extension. -/
def readyOfExtension
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    (extension : SafeOverlapExtension sourceInput (preparedTarget state) source) :
    StepResult sourceInput targetInput source state :=
  .ready (extension.transport source)
    { extension := extension, output_eq := rfl }

/-- The ordinary ready branch computed by satisfying one exact requirement.
This package is convenient for a parent dependency scheduler: it contains no
spurious progressed or blocked alternatives. -/
structure Satisfied
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) : Type 2 where
  output : AnchoredChart (preparedTarget state)
  valid : Ready sourceInput targetInput source state output

/-- Satisfy one exact typed requirement and return the resulting branch
directly. -/
def satisfy
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (requirement : Requirement sourceInput targetInput source state)
    (evidence : Evidence requirement) :
    Satisfied sourceInput targetInput source state :=
  match requirement with
  | .overlap certificate =>
      let extension :=
        CCL.LogChartSafety.extensionOfBased sourceInput targetInput source
          state.source certificate evidence
      { output := extension.transport source
        valid := { extension := extension, output_eq := rfl } }
  | .completeExtension =>
      { output := evidence.transport source
        valid := { extension := evidence, output_eq := rfl } }

/-- Inspect one target ball.  Failure performs exactly one canonical
refinement.  Success exposes the semantic overlap evidence which rational ball
arithmetic cannot manufacture for unrelated `Possible` predicates. -/
def step
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) :
    StepResult sourceInput targetInput source state :=
  if certificate : SafetyCertificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex then
    .blocked (.overlap certificate)
  else
    .progressed state.advance (.refined state)

theorem step_is_blocked_of_safe
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (certificate : SafetyCertificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex) :
    ∃ discovered : SafetyCertificate source.chart.factor
        (targetInput.name.process.ball state.source) state.nextIndex,
      step sourceInput targetInput source state =
        .blocked (.overlap discovered) := by
  rw [step, dif_pos certificate]
  exact ⟨certificate, rfl⟩

theorem step_eq_progressed_of_not_safe
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (notSafe : ¬ SafetyCertificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex) :
    step sourceInput targetInput source state =
      .progressed state.advance (.refined state) := by
  rw [step, dif_neg notSafe]

/-- Satisfy one exact typed requirement.  An overlap witness is combined with
the retained safety proof; a complete extension is used directly. -/
def resume
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (requirement : Requirement sourceInput targetInput source state)
    (evidence : Evidence requirement) :
    StepResult sourceInput targetInput source state :=
  let satisfied := satisfy sourceInput targetInput source state
    requirement evidence
  .ready satisfied.output satisfied.valid

theorem resume_is_ready
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (requirement : Requirement sourceInput targetInput source state)
    (evidence : Evidence requirement) :
    ∃ output : AnchoredChart (preparedTarget state),
      ∃ valid : Ready sourceInput targetInput source state output,
        resume sourceInput targetInput source state requirement evidence =
          .ready output valid := by
  cases requirement with
  | overlap certificate => exact ⟨_, _, rfl⟩
  | completeExtension => exact ⟨_, _, rfl⟩

/-- Small non-dependent observation of why a finite run stopped. -/
inductive ResultKind
  | ready
  | blocked
  | exhausted
  deriving DecidableEq

/-- The payload which is specific to one terminal kind and exact retained
state.  Only this field is dependent; ordinary scheduling observations remain
cheap projections. -/
inductive RunPayload
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) : ResultKind → Type 2
  | ready (output : AnchoredChart (preparedTarget state))
      (valid : Ready sourceInput targetInput source state output) :
      RunPayload sourceInput targetInput source state .ready
  | blocked (requirement : Requirement sourceInput targetInput source state) :
      RunPayload sourceInput targetInput source state .blocked
  | exhausted :
      RunPayload sourceInput targetInput source state .exhausted

/-- Terminal result of a caller-bounded automatic run.  Kind and state are
first-class fields; the exact branch or requirement remains indexed by both. -/
structure RunResult
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (start : State targetInput) : Type 2 where
  kind : ResultKind
  state : State targetInput
  reachable : Reachable start state
  payload : RunPayload sourceInput targetInput source state kind

/-- Exhaustion at an unchanged retained state. -/
def exhaustedResult
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) :
    RunResult sourceInput targetInput source state where
  kind := .exhausted
  state := state
  reachable := .refl state
  payload := .exhausted

/-- Immediate ready result at one retained state. -/
def readyResult
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (output : AnchoredChart (preparedTarget state))
    (valid : Ready sourceInput targetInput source state output) :
    RunResult sourceInput targetInput source state where
  kind := .ready
  state := state
  reachable := .refl state
  payload := .ready output valid

/-- Immediate typed evidence request at one retained state. -/
def blockedResult
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput)
    (requirement : Requirement sourceInput targetInput source state) :
    RunResult sourceInput targetInput source state where
  kind := .blocked
  state := state
  reachable := .refl state
  payload := .blocked requirement

/-- Prefix one genuine progress step to a recursive terminal result. -/
def prefixResult
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {start next : State targetInput}
    (progress : Progress start next)
    (later : RunResult sourceInput targetInput source next) :
    RunResult sourceInput targetInput source start where
  kind := later.kind
  state := later.state
  reachable := .tail progress later.reachable
  payload := later.payload

/-- Structurally recursive finite runner.  Fuel is consumed only by a genuine
`progressed` transition. -/
def attempt
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) :
    Nat → RunResult sourceInput targetInput source state
  | 0 => exhaustedResult sourceInput targetInput source state
  | fuel + 1 =>
      match step sourceInput targetInput source state with
      | .ready output valid =>
          readyResult sourceInput targetInput source state output valid
      | .blocked requirement =>
          blockedResult sourceInput targetInput source state requirement
      | .progressed next progress =>
          prefixResult progress
            (attempt sourceInput targetInput source next fuel)

@[simp] theorem attempt_zero
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (state : State targetInput) :
    attempt sourceInput targetInput source state 0 =
      exhaustedResult sourceInput targetInput source state := rfl

/-! ## Operational laws of readiness -/

/-- Any two ready branches obtained from the fixed source anchor are
operationally equivalent, independently of their finite safety and overlap
schedules. -/
def ready_respects
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {firstState secondState : State targetInput}
    {firstOutput : AnchoredChart (preparedTarget firstState)}
    {secondOutput : AnchoredChart (preparedTarget secondState)}
    (firstReady : Ready sourceInput targetInput source firstState firstOutput)
    (secondReady : Ready sourceInput targetInput source secondState secondOutput) :
    NamedEquivalent firstOutput.output.name secondOutput.output.name := by
  rcases firstReady with ⟨firstExtension, rfl⟩
  rcases secondReady with ⟨secondExtension, rfl⟩
  exact CCL.LogChartCongruence.transportedOutput_respects source
    firstExtension secondExtension
    (preparedTargetsEquivalent firstState secondState)

/-- Reachability documents the execution relationship; the stronger
schedule-free theorem supplies semantic stability. -/
def ready_stable_after_progress
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {firstState laterState : State targetInput}
    (_reachable : Reachable firstState laterState)
    {firstOutput : AnchoredChart (preparedTarget firstState)}
    {laterOutput : AnchoredChart (preparedTarget laterState)}
    (firstReady : Ready sourceInput targetInput source firstState firstOutput)
    (laterReady : Ready sourceInput targetInput source laterState laterOutput) :
    NamedEquivalent firstOutput.output.name laterOutput.output.name :=
  ready_respects firstReady laterReady

/-- Every ready branch has the existing finite exponential inverse. -/
def ready_exponential_inverse
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (_ready : Ready sourceInput targetInput source state output) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named output.output.name)
      (preparedTarget state).name :=
  output.exponential_inverse

/-- Readiness returns an ordinary productive anchored-logarithm name. -/
theorem ready_productive
    {sourceInput targetInput : CoherentNamed}
    {source : AnchoredChart sourceInput}
    {state : State targetInput}
    {output : AnchoredChart (preparedTarget state)}
    (_ready : Ready sourceInput targetInput source state output)
    (count : Nat) :
    output.output.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          output.output.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        output.output.name.machine count).emitted.length = count :=
  output.output.name.productive count

end CCL.ProgressivePartialLogarithm
