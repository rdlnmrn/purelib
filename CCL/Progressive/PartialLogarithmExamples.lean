import CCL.Progressive.PartialDivisionExamples
import CCL.Progressive.PartialLogarithmOutput

/-!
# Executable examples for retryable anchored-logarithm preflight

The target reuses the deliberately delayed exact-one process from division
preflight.  Its initial ball is too coarse for complex-log chart safety.  One
finite refinement exposes an exact safe ball, after which the generic builder
blocks on the precise semantic overlap witness.  Supplying that witness
transports the separately packaged exact-one anchor to a genuinely different
based process state type.
-/

namespace CCL.ProgressivePartialLogarithmExamples

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

open CCL.ProgressivePartialLogarithm

def sourceInput : CoherentNamed := CCL.LogAnchorSeeds.exactOneInput

def sourceAnchor : AnchoredChart sourceInput :=
  CCL.LogAnchorSeeds.exactOneAnchor

def targetInput : CoherentNamed :=
  CCL.ProgressivePartialDivisionExamples.delayedOne

def initial : State targetInput := State.initial targetInput

def refined : State targetInput := initial.advance

def refinedAgain : State targetInput := refined.advance

theorem initial_not_safe :
    ¬ CCL.LogChartSafety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball initial.source) initial.nextIndex := by
  decide

theorem first_step_progresses :
    step sourceInput targetInput sourceAnchor initial =
      .progressed refined (.refined initial) := by
  exact step_eq_progressed_of_not_safe sourceInput targetInput sourceAnchor
    initial initial_not_safe

theorem refinedSafety :
    CCL.LogChartSafety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball refined.source) refined.nextIndex := by
  decide

theorem second_step_blocks_for_overlap :
    step sourceInput targetInput sourceAnchor refined =
      .blocked (.overlap refinedSafety) := by
  rw [step, dif_pos refinedSafety]

/-- At the refined exact-one state, the rational point `1` is admitted by both
the source anchor input and the prepared target. -/
def refinedOverlap :
    OverlapWitness sourceInput (preparedTarget refined) where
  point := 1
  left_possible := rfl
  right_possible := rfl

def refinedRequirement :
    Requirement sourceInput targetInput sourceAnchor refined :=
  .overlap refinedSafety

def refinedExtension :
    SafeOverlapExtension sourceInput (preparedTarget refined) sourceAnchor :=
  CCL.LogChartSafety.extensionOfBased sourceInput targetInput sourceAnchor
    refined.source refinedSafety refinedOverlap

def refinedOutput : AnchoredChart (preparedTarget refined) :=
  refinedExtension.transport sourceAnchor

def refinedReady :
    Ready sourceInput targetInput sourceAnchor refined refinedOutput where
  extension := refinedExtension
  output_eq := rfl

theorem resume_overlap_is_ready :
    resume sourceInput targetInput sourceAnchor refined refinedRequirement
      refinedOverlap = .ready refinedOutput refinedReady := by
  rfl

def oneFuelExpected :
    RunResult sourceInput targetInput sourceAnchor initial :=
  prefixResult (.refined initial)
    (exhaustedResult sourceInput targetInput sourceAnchor refined)

/-- The executable one-unit run.  Its transition-level characterization is
`first_step_progresses`; `oneFuelExpected` displays the retained result without
forcing the elaborator to normalize the concrete dependent chart payload. -/
def oneFuelRun :
    RunResult sourceInput targetInput sourceAnchor initial :=
  attempt sourceInput targetInput sourceAnchor initial 1

def twoFuelExpected :
    RunResult sourceInput targetInput sourceAnchor initial :=
  prefixResult (.refined initial)
    (blockedResult sourceInput targetInput sourceAnchor refined
      (.overlap refinedSafety))

/-- The executable two-unit run.  Theorems `first_step_progresses` and
`second_step_blocks_for_overlap` certify its two structural transitions, and
`twoFuelExpected` exposes the exact retained typed requirement. -/
def twoFuelRun :
    RunResult sourceInput targetInput sourceAnchor initial :=
  attempt sourceInput targetInput sourceAnchor initial 2

theorem refinedAgainSafety :
    CCL.LogChartSafety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball refinedAgain.source)
      refinedAgain.nextIndex := by
  decide

def refinedAgainOverlap :
    OverlapWitness sourceInput (preparedTarget refinedAgain) where
  point := 1
  left_possible := rfl
  right_possible := rfl

def refinedAgainExtension :
    SafeOverlapExtension sourceInput (preparedTarget refinedAgain)
      sourceAnchor :=
  CCL.LogChartSafety.extensionOfBased sourceInput targetInput sourceAnchor
    refinedAgain.source refinedAgainSafety refinedAgainOverlap

def refinedAgainOutput : AnchoredChart (preparedTarget refinedAgain) :=
  refinedAgainExtension.transport sourceAnchor

def refinedAgainReady :
    Ready sourceInput targetInput sourceAnchor refinedAgain
      refinedAgainOutput where
  extension := refinedAgainExtension
  output_eq := rfl

/-- Readiness at two different retained states gives the same finite
logarithm operationally because both transports retain the fixed anchor. -/
def different_schedules_equivalent :
    NamedEquivalent refinedOutput.output.name refinedAgainOutput.output.name :=
  ready_respects refinedReady refinedAgainReady

/-- The ready branch enters the unchanged persistent output layer. -/
theorem ready_request_length (epsilonSq : RFAP.ConstructiveFraction.Rational)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor refinedReady).request epsilonSq positive count).machine.emitted.length =
      (readyCursor refinedReady).machine.emitted.length + count :=
  readyCursor_request_length refinedReady epsilonSq positive count

end CCL.ProgressivePartialLogarithmExamples
