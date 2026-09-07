import CCL.Progressive.DivisionCongruence

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace CCL.ProgressivePartialDivision

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev PossibleApart := CCL.ProgressiveCharts.PossibleApart
abbrev BasedState := CCL.ProgressiveCharts.BasedState

open RFAP.ConstructiveGaussian.Gaussian

/-- Retained automatic-search state for one fixed coherent denominator.
`persists` records finite provenance back to the denominator's original named
state, while `nextIndex` selects the next canonical positive rational request.
-/
structure State (denominator : CoherentNamed) where
  source : denominator.name.process.State
  nextIndex : Nat
  persists : ∀ {value : Gaussian},
    denominator.name.process.Possible source value →
      denominator.name.process.Possible denominator.name.state value

namespace State

/-- The initial search state performs no refinement and has reflexive
candidate provenance. -/
def initial (denominator : CoherentNamed) : State denominator where
  source := denominator.name.state
  nextIndex := 0
  persists := fun possible => possible

/-- One deterministic unit of automatic work.  The retained source is refined
in place, and its provenance proof is composed with refinement persistence. -/
def advance {denominator : CoherentNamed}
    (state : State denominator) : State denominator where
  source := denominator.name.process.refine state.source
    (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex)
  nextIndex := state.nextIndex + 1
  persists := fun possible =>
    state.persists
      (denominator.name.process.refine_persists state.source
        (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
        (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex)
        possible)

@[simp] theorem initial_source (denominator : CoherentNamed) :
    (initial denominator).source = denominator.name.state := rfl

@[simp] theorem initial_nextIndex (denominator : CoherentNamed) :
    (initial denominator).nextIndex = 0 := rfl

@[simp] theorem advance_source {denominator : CoherentNamed}
    (state : State denominator) :
    state.advance.source = denominator.name.process.refine state.source
      (CCL.ProgressiveSampling.refinementTarget state.nextIndex)
      (CCL.ProgressiveSampling.refinementTarget_pos state.nextIndex) := rfl

@[simp] theorem advance_nextIndex {denominator : CoherentNamed}
    (state : State denominator) :
    state.advance.nextIndex = state.nextIndex + 1 := rfl

/-- Every retained candidate still has the promised provenance at the
original named denominator state. -/
theorem possible_at_initial {denominator : CoherentNamed}
    (state : State denominator) {value : Gaussian}
    (possible : denominator.name.process.Possible state.source value) :
    denominator.name.process.Possible denominator.name.state value :=
  state.persists possible

end State

/-- A genuine automatic transition.  There is exactly one transition from a
state: its canonical finite refinement. -/
inductive Progress {denominator : CoherentNamed} :
    State denominator → State denominator → Type
  | refined (state : State denominator) : Progress state state.advance

namespace Progress

/-- One automatic transition preserves every candidate admitted by its target
as a candidate admitted by its source. -/
theorem possible_persists {denominator : CoherentNamed}
    {current next : State denominator} (progress : Progress current next)
    {value : Gaussian}
    (possible : denominator.name.process.Possible next.source value) :
    denominator.name.process.Possible current.source value := by
  cases progress
  exact denominator.name.process.refine_persists current.source
    (CCL.ProgressiveSampling.refinementTarget current.nextIndex)
    (CCL.ProgressiveSampling.refinementTarget_pos current.nextIndex)
    possible

@[simp] theorem nextIndex_eq {denominator : CoherentNamed}
    {current next : State denominator} (progress : Progress current next) :
    next.nextIndex = current.nextIndex + 1 := by
  cases progress
  rfl

end Progress

/-- Finite reflexive-transitive reachability generated only by certified
automatic refinement steps.  No completed execution history is stored. -/
inductive Reachable {denominator : CoherentNamed} :
    State denominator → State denominator → Type
  | refl (state : State denominator) : Reachable state state
  | tail {first middle last : State denominator} :
      Progress first middle → Reachable middle last → Reachable first last

namespace Reachable

/-- Candidate persistence composes along every finite execution. -/
theorem possible_persists {denominator : CoherentNamed}
    {first last : State denominator} (reachable : Reachable first last)
    {value : Gaussian}
    (possible : denominator.name.process.Possible last.source value) :
    denominator.name.process.Possible first.source value := by
  induction reachable with
  | refl => exact possible
  | tail progress reachable inductionHypothesis =>
      exact progress.possible_persists (inductionHypothesis possible)

end Reachable

/-- The sole manually satisfiable obligation for division at a retained
state.  Its state index prevents a certificate for another base state from
being replayed here. -/
inductive Requirement {denominator : CoherentNamed}
    (state : State denominator) : Type
  | candidateApartness

/-- Division preflight has no constructive automatic exclusion certificate.
In particular, repeated failure of centre separation cannot inhabit this
family and therefore cannot be mistaken for proof that the denominator is
zero. -/
inductive Exclusion {denominator : CoherentNamed}
    (state : State denominator) : Type

/-- Evidence is indexed by the exact requirement and retained state. -/
def Evidence {denominator : CoherentNamed} {state : State denominator} :
    Requirement state → Type
  | .candidateApartness =>
      PossibleApart
        (CCL.ProgressiveCharts.based denominator.name.process state.source)

/-- The coherent denominator restricted to the retained refinement future. -/
def basedDenominator {denominator : CoherentNamed}
    (state : State denominator) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.based denominator state.source

/-- Turn exact state-indexed candidate apartness into the existing total,
whole-ball-apart coherent denominator. -/
def preparedDenominator {denominator : CoherentNamed}
    (state : State denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (basedDenominator state) evidence

/-- Uniform whole-ball apartness consumed by ordinary total division. -/
def preparedApart {denominator : CoherentNamed}
    (state : State denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    CCL.ProgressiveTransducer.Named.Apart
      (preparedDenominator state evidence).name where
  certificate := CCL.ProgressiveCharts.apartifyApart evidence

/-- The ordinary total quotient returned after preflight succeeds. -/
def readyName (numerator denominator : CoherentNamed)
    (state : State denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div numerator
    (preparedDenominator state evidence) (preparedApart state evidence)

/-- A ready result records the exact state-indexed evidence from which its
ordinary coherent quotient was constructed. -/
structure Ready (numerator denominator : CoherentNamed)
    (state : State denominator) (output : CoherentNamed) where
  evidence : PossibleApart
    (CCL.ProgressiveCharts.based denominator.name.process state.source)
  output_eq : output = readyName numerator denominator state evidence

/-- One automatic inspection either finishes or performs exactly one
certified refinement.  There is deliberately no exclusion constructor. -/
inductive StepResult (numerator denominator : CoherentNamed)
    (state : State denominator) : Type 2
  | ready (output : CoherentNamed) (valid : Ready numerator denominator state output)
  | progressed (next : State denominator) (progress : Progress state next)

/-- Convert the successful rational centre-separation test into the precisely
indexed evidence required for manual or automatic readiness. -/
def evidenceOfSeparation {denominator : CoherentNamed}
    (state : State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center) :
    PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source) :=
  CCL.ProgressiveCharts.possibleApartOfBall
    denominator.name.process state.source
    (CCL.ResidualDecision.apartOfCenter
      (denominator.name.process.ball state.source) separated)

/-- Denominator-only preparation result.  This separates acquisition of the
apartness certificate from construction of a quotient, allowing a dependency
scheduler to prepare a denominator before its numerator is available. -/
inductive PreparationResult (denominator : CoherentNamed)
    (state : State denominator) : Type
  | prepared (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source))
  | progressed (next : State denominator) (progress : Progress state next)

/-- Inspect or refine only the denominator.  No placeholder numerator and no
partial quotient is constructed. -/
def prepare (denominator : CoherentNamed) (state : State denominator) :
    PreparationResult denominator state :=
  if separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center then
    .prepared (evidenceOfSeparation state separated)
  else
    .progressed state.advance (.refined state)

theorem prepare_is_prepared_of_separated (denominator : CoherentNamed)
    (state : State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center) :
    ∃ evidence : PossibleApart
        (CCL.ProgressiveCharts.based denominator.name.process state.source),
      prepare denominator state = .prepared evidence := by
  rw [prepare, dif_pos separated]
  exact ⟨_, rfl⟩

theorem prepare_eq_progressed_of_not_separated
    (denominator : CoherentNamed) (state : State denominator)
    (notSeparated : ¬
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center) :
    prepare denominator state =
      .progressed state.advance (.refined state) := by
  rw [prepare, dif_neg notSeparated]

/-- Inspect one displayed rational ball.  A failed test performs exactly the
canonical refinement selected by `nextIndex`; it never reports zero or domain
exclusion. -/
def step (numerator denominator : CoherentNamed)
    (state : State denominator) : StepResult numerator denominator state :=
  if separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center then
    let evidence := evidenceOfSeparation state separated
    .ready (readyName numerator denominator state evidence)
      { evidence := evidence, output_eq := rfl }
  else
    .progressed state.advance (.refined state)

/-- A successful rational separation test makes the automatic step ready. -/
theorem step_is_ready_of_separated (numerator denominator : CoherentNamed)
    (state : State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center) :
    ∃ output : CoherentNamed, ∃ valid :
        Ready numerator denominator state output,
      step numerator denominator state = .ready output valid := by
  rw [step, dif_pos separated]
  exact ⟨_, _, rfl⟩

/-- Failure of the sufficient separation test has exactly one meaning: one
canonical certified refinement is returned. -/
theorem step_eq_progressed_of_not_separated
    (numerator denominator : CoherentNamed) (state : State denominator)
    (notSeparated : ¬
      2 * (denominator.name.process.ball state.source).radiusSq <
        normSq (denominator.name.process.ball state.source).center) :
    step numerator denominator state =
      .progressed state.advance (.refined state) := by
  rw [step, dif_neg notSeparated]

/-- Satisfy the exact typed requirement explicitly, bypassing further
automatic search. -/
def resume (numerator denominator : CoherentNamed)
    (state : State denominator) (requirement : Requirement state)
    (evidence : Evidence requirement) :
    StepResult numerator denominator state :=
  match requirement with
  | .candidateApartness =>
      .ready (readyName numerator denominator state evidence)
        { evidence := evidence, output_eq := rfl }

/-- Supplying evidence for the exact indexed requirement always returns an
ordinary ready quotient in one finite call. -/
theorem resume_is_ready (numerator denominator : CoherentNamed)
    (state : State denominator) (requirement : Requirement state)
    (evidence : Evidence requirement) :
    ∃ output : CoherentNamed, ∃ valid :
        Ready numerator denominator state output,
      resume numerator denominator state requirement evidence =
        .ready output valid := by
  cases requirement
  exact ⟨_, _, rfl⟩

/-- Terminal result of a caller-bounded automatic run.  `exhausted` means only
that the supplied natural fuel was consumed. -/
inductive RunResult (numerator denominator : CoherentNamed)
    (start : State denominator) : Nat → Type 2
  | ready {fuel : Nat} (state : State denominator)
      (reachable : Reachable start state) (output : CoherentNamed)
      (valid : Ready numerator denominator state output) :
      RunResult numerator denominator start fuel
  | exhausted {fuel : Nat} (state : State denominator)
      (reachable : Reachable start state) :
      RunResult numerator denominator start fuel

/-- Structurally recursive finite runner.  Fuel is consumed only after a real
`progressed` transition.  At zero fuel the retained state is returned
unchanged. -/
def attempt (numerator denominator : CoherentNamed)
    (state : State denominator) :
    (fuel : Nat) → RunResult numerator denominator state fuel
  | 0 => .exhausted state (.refl state)
  | fuel + 1 =>
      match step numerator denominator state with
      | .ready output valid => .ready state (.refl state) output valid
      | .progressed next progress =>
          match attempt numerator denominator next fuel with
          | .ready final reachable output valid =>
              .ready final (.tail progress reachable) output valid
          | .exhausted final reachable =>
              .exhausted final (.tail progress reachable)

@[simp] theorem attempt_zero (numerator denominator : CoherentNamed)
    (state : State denominator) :
    attempt numerator denominator state 0 =
      .exhausted state (.refl state) := rfl

/-- A ready one-step result terminates every positive-fuel run immediately;
unused fuel is irrelevant finite budget. -/
theorem attempt_succ_eq_ready_of_step_ready
    (numerator denominator : CoherentNamed) (state : State denominator)
    (fuel : Nat) (output : CoherentNamed)
    (valid : Ready numerator denominator state output)
    (stepReady : step numerator denominator state = .ready output valid) :
    attempt numerator denominator state (fuel + 1) =
      .ready state (.refl state) output valid := by
  rw [attempt, stepReady]

/-- A progressed step prefixes its reachability certificate to a recursively
ready finite run. -/
theorem attempt_succ_eq_ready_of_step_progressed
    (numerator denominator : CoherentNamed)
    (state next final : State denominator) (fuel : Nat)
    (progress : Progress state next) (reachable : Reachable next final)
    (output : CoherentNamed) (valid : Ready numerator denominator final output)
    (stepProgressed : step numerator denominator state =
      .progressed next progress)
    (laterReady : attempt numerator denominator next fuel =
      .ready final reachable output valid) :
    attempt numerator denominator state (fuel + 1) =
      .ready final (.tail progress reachable) output valid := by
  rw [attempt, stepProgressed]
  simp only
  rw [laterReady]

/-- A progressed step likewise retains its transition when the recursive run
exhausts its remaining fuel. -/
theorem attempt_succ_eq_exhausted_of_step_progressed
    (numerator denominator : CoherentNamed)
    (state next final : State denominator) (fuel : Nat)
    (progress : Progress state next) (reachable : Reachable next final)
    (stepProgressed : step numerator denominator state =
      .progressed next progress)
    (laterExhausted : attempt numerator denominator next fuel =
      .exhausted final reachable) :
    attempt numerator denominator state (fuel + 1) =
      .exhausted final (.tail progress reachable) := by
  rw [attempt, stepProgressed]
  simp only
  rw [laterExhausted]

/-! ## Operational laws of readiness -/

/-- The based and apartified denominator returned by preflight has the same
finite operational value as the original coherent denominator. -/
def preparedDenominatorEquivalent {denominator : CoherentNamed}
    (state : State denominator)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based denominator.name.process state.source)) :
    NamedEquivalent denominator.name (preparedDenominator state evidence).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.ProgressiveCoherence.CoherentNamed.basedEquivalent
      denominator state.source)
    (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent
      (basedDenominator state) evidence)

/-- Any two ready quotients of the fixed inputs are operationally equivalent,
regardless of the finite states or evidence schedules at which readiness was
obtained. -/
def ready_respects {numerator denominator : CoherentNamed}
    {firstState secondState : State denominator}
    {firstOutput secondOutput : CoherentNamed}
    (firstReady : Ready numerator denominator firstState firstOutput)
    (secondReady : Ready numerator denominator secondState secondOutput) :
    NamedEquivalent firstOutput.name secondOutput.name := by
  rcases firstReady with ⟨firstEvidence, rfl⟩
  rcases secondReady with ⟨secondEvidence, rfl⟩
  let firstDenominator := preparedDenominator firstState firstEvidence
  let secondDenominator := preparedDenominator secondState secondEvidence
  have denominatorEquivalent : NamedEquivalent
      firstDenominator.name secondDenominator.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (preparedDenominatorEquivalent firstState firstEvidence))
      (preparedDenominatorEquivalent secondState secondEvidence)
  simpa only [readyName, firstDenominator, secondDenominator,
    CCL.ProgressiveCoherence.CoherentNamed.div] using
    CCL.ProgressiveDivisionCongruence.coherentDiv_respects
      numerator numerator firstDenominator secondDenominator
      (preparedApart firstState firstEvidence)
      (preparedApart secondState secondEvidence)
      (CCL.OperationalEquivalence.NamedEquivalent.refl numerator.name)
      denominatorEquivalent

/-- In particular, a ready output remains semantically stable against any
later reachable success.  Reachability is retained to document the execution
relationship; operational stability follows from the stronger schedule-free
ready congruence above. -/
def ready_stable_after_progress {numerator denominator : CoherentNamed}
    {firstState laterState : State denominator}
    (_reachable : Reachable firstState laterState)
    {firstOutput laterOutput : CoherentNamed}
    (firstReady : Ready numerator denominator firstState firstOutput)
    (laterReady : Ready numerator denominator laterState laterOutput) :
    NamedEquivalent firstOutput.name laterOutput.name :=
  ready_respects firstReady laterReady

/-- A ready quotient is an ordinary productive name: every finite bit request
returns exactly the requested number of raw bits and preserves its prefix. -/
theorem ready_productive {numerator denominator : CoherentNamed}
    {state : State denominator} {output : CoherentNamed}
    (_ready : Ready numerator denominator state output) (count : Nat) :
    (output.name.machine).emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance output.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance output.name.machine count).emitted.length =
        count :=
  output.name.productive count

end CCL.ProgressivePartialDivision
