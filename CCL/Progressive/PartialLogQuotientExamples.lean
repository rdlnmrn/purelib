import CCL.Progressive.PartialLogQuotientOutput

/-!
# Executable schedules for `log(1 + z) / z`

The concrete input is the exact rational `z = 1/2`, while the logarithm source
anchor is built independently at `3/2`.  One schedule acquires logarithm
overlap first and denominator apartness second; another supplies denominator
apartness first.  Both finish with ordinary operationally equivalent quotient
CCLs.
-/

namespace CCL.ProgressivePartialLogQuotientExamples

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

open CCL.ProgressivePartialLogQuotient

def half : Gaussian := ⟨1 / 2, 0⟩

def threeHalves : Gaussian := ⟨3 / 2, 0⟩

def denominator : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact half

def sourceInput : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact threeHalves

/-- A direct unit-factor chart at the exact rational `3/2`.  The reduced
coordinate is `1/5`, so the local `1/9` squared-radius condition is immediate
finite rational arithmetic. -/
def sourceChart : CCL.ComplexLogChart.Chart sourceInput.name :=
  CCL.ComplexLogChart.Chart.ofBounds sourceInput.name
    1 1 (by decide)
    (by
      intro state source possible
      change source = threeHalves at possible
      subst source
      decide)
    (by
      intro numeratorSource denominatorSource numeratorPossible
        denominatorPossible
      change numeratorSource = threeHalves at numeratorPossible
      change denominatorSource = threeHalves at denominatorPossible
      subst numeratorSource
      subst denominatorSource
      decide)
    (CCL.ProgressiveTransducer.Named.exact 0)

def sourceAnchor : AnchoredChart sourceInput where
  chart := sourceChart
  certificate :=
    { factor_ne_zero := by decide
      correction_exponential := by
        change CCL.OperationalEquivalence.NamedEquivalent
          (CCL.ProgressiveExpRange.named
            (CCL.ProgressiveTransducer.Named.exact 0))
          (CCL.ProgressiveTransducer.Named.exact 1)
        exact CCL.TranscendentalCoherence.automaticExp_zero }
  correctionCoherent := CCL.ProgressiveCoherence.Coherent.exact 0

def client : Client where
  denominator := denominator
  sourceInput := sourceInput
  source := sourceAnchor

def initial : State client := State.initial client

def logState : Log.State client.argument :=
  CCL.ProgressivePartialLogarithm.State.initial client.argument

def denominatorState : Division.State client.denominator :=
  CCL.ProgressivePartialDivision.State.initial client.denominator

theorem initialLogSafety :
    CCL.LogChartSafety.Certificate sourceAnchor.chart.factor
      (client.argument.name.process.ball logState.source)
      logState.nextIndex := by
  decide

def logRequirement :
    Log.Requirement client.sourceInput client.argument client.source logState :=
  .overlap initialLogSafety

def logBlocked : Blocked client :=
  .logarithm logState logRequirement (.searching denominatorState) false

/-- The independently constructed chart input and `1 + 1/2` admit the same
exact rational point, so this is genuine chart transport rather than wrapping
an already supplied target chart. -/
def logOverlap :
    CCL.LogBranchGeometry.OverlapWitness client.sourceInput
      (Log.preparedTarget logState) where
  point := threeHalves
  left_possible := rfl
  right_possible := by
    exact ⟨1, half, rfl, rfl, by decide⟩

def afterLog : State client := logBlocked.resume logOverlap

/-- Executable initial scheduler result.  `initialLogSafety` and the definition
of `advanceLog` certify that its retained payload is `logBlocked`. -/
def firstStep : StepResult client initial := step client initial

def firstStepExpected : StepResult client initial :=
  .blocked logBlocked rfl

theorem denominatorSeparated :
    2 * (client.denominator.name.process.ball denominatorState.source).radiusSq <
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (client.denominator.name.process.ball denominatorState.source).center := by
  decide

def denominatorEvidence : PossibleApart
    (CCL.ProgressiveCharts.based client.denominator.name.process
      denominatorState.source) :=
  CCL.ProgressivePartialDivision.evidenceOfSeparation denominatorState
    denominatorSeparated

def afterBoth : State client :=
  State.withDenominatorReady afterLog.log denominatorState denominatorEvidence
    false

/-- Executable post-log scheduler step and its exact retained target. -/
def secondStep : StepResult client afterLog := step client afterLog

def secondStepExpected : StepResult client afterLog :=
  .progressed afterBoth
    (.denominatorPrepared afterLog.log denominatorState denominatorEvidence
      true)

def logSatisfied : CCL.ProgressivePartialLogarithm.Satisfied
    client.sourceInput client.argument client.source logState :=
  Log.satisfy client.sourceInput client.argument client.source logState
    logRequirement logOverlap

def finalOutput : CoherentNamed :=
  readyName client logState logSatisfied.output denominatorState
    denominatorEvidence

def finalReady : Ready client finalOutput where
  logState := logState
  logOutput := logSatisfied.output
  logValid := logSatisfied.valid
  denominatorState := denominatorState
  denominatorEvidence := denominatorEvidence
  output_eq := rfl

theorem third_step_is_ready :
    ∃ output : CoherentNamed, ∃ valid : Ready client output,
      step client afterBoth = .ready output valid := by
  simp only [afterBoth, afterLog, logBlocked, Blocked.resume]
  exact ⟨_, _, rfl⟩

theorem final_request_length (epsilonSq : Coordinate)
    (positive : 0 < epsilonSq) (count : Nat) :
    ((readyCursor finalReady).request epsilonSq positive count).machine.emitted.length =
      (readyCursor finalReady).machine.emitted.length + count :=
  readyCursor_request_length finalReady epsilonSq positive count

/-! ## A different evidence schedule -/

def denominatorBlockedFirst : Blocked client :=
  requestDenominator (.searching logState) denominatorState false

def denominatorEvidenceFirst : Blocked.Evidence denominatorBlockedFirst :=
  denominatorEvidence

def afterDenominatorFirst : State client :=
  denominatorBlockedFirst.resume denominatorEvidenceFirst

def logBlockedSecond : Blocked client :=
  .logarithm logState logRequirement (.ready denominatorState
    denominatorEvidence) true

def afterBothSecond : State client := logBlockedSecond.resume logOverlap

/-- Executable logarithm request when denominator evidence was supplied
first. -/
def denominatorFirstStep : StepResult client afterDenominatorFirst :=
  step client afterDenominatorFirst

def denominatorFirstStepExpected : StepResult client afterDenominatorFirst :=
  .blocked logBlockedSecond rfl

theorem denominator_first_finishes :
    ∃ output : CoherentNamed, ∃ valid : Ready client output,
      step client afterBothSecond = .ready output valid := by
  simp only [afterBothSecond, logBlockedSecond, Blocked.resume]
  exact ⟨_, _, rfl⟩

/-- The two finite evidence schedules cannot change the ready expression's
operational value. -/
def schedules_equivalent
    {firstOutput secondOutput : CoherentNamed}
    (firstReady : Ready client firstOutput)
    (secondReady : Ready client secondOutput) :
    CCL.OperationalEquivalence.NamedEquivalent
      firstOutput.name secondOutput.name :=
  ready_respects firstReady secondReady

end CCL.ProgressivePartialLogQuotientExamples
