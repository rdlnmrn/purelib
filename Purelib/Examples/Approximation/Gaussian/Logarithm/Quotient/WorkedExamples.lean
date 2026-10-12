module
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Exact
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Quotient.State
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Step
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Overlap
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Executable schedules for `log(1 + z) / z`

The concrete input is the exact rational `z = 1/2`, while the logarithm source
anchor is built independently at `3/2`.  One schedule acquires logarithm
overlap first and denominator apartness second; another supplies denominator
apartness first.  Both finish with ordinary operationally equivalent quotient
CCLs.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.WorkedExamples

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Examples
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Approximation.Gaussian.Division

/-- The Gaussian rational number one half. -/
def half : Basic.Canonical := ⟨1 / 2,
  0⟩

/-- The Gaussian rational number three halves. -/
def threeHalves : Basic.Canonical := ⟨3
  / 2, 0⟩

/-- The exact coherent denominator name at one half. -/
def denominator :
  CoherentNamed :=
  CoherentNamed.Coherence.exact half

/-- The exact coherent chart-source name at three halves. -/
def sourceInput :
  CoherentNamed :=
  CoherentNamed.Coherence.exact threeHalves

/-- The retained logarithm chart at three halves with unit bounds and zero correction.

Certifies the original exact source's separation and pairwise bounds directly, preserving its named correction. -/
def sourceChart :
  Approximation.Gaussian.Logarithm.Chart sourceInput.name :=
  Approximation.Gaussian.Logarithm.Chart.ofBounds
      sourceInput.name
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
      change denominatorSource =
        threeHalves at denominatorPossible
      subst numeratorSource
      subst denominatorSource
      decide)
    (Basic.Named.exact 0)

/-- The anchored chart with its original exponential-correction certificate.

Retains the exact-zero correction name and its equivalence to the unit exponential output. -/
def sourceAnchor :
  Logarithm.Chart.Anchored.AnchoredChart sourceInput where
  chart := sourceChart
  certificate :=
    { factor_ne_zero := by decide
      correction_exponential := by
        change Equivalence.NamedEquivalent
          (Exponential.Progressive.Range.Name.named
            (Basic.Named.exact 0))
          (Basic.Named.exact 1)
        exact Exponential.Progressive.Range.Exact.automaticExp_zero }
  correctionCoherent := Coherence.Basic.Coherent.exact 0

/-- The logarithm-quotient client retaining the denominator, source input and anchor. -/
def client :
  Approximation.Gaussian.Logarithm.Quotient.Client where
  denominator := denominator
  sourceInput := sourceInput
  source := sourceAnchor

/-- The original joint logarithm/denominator search state. -/
def initial :
  Approximation.Gaussian.Logarithm.Quotient.State client :=
  Approximation.Gaussian.Logarithm.Quotient.State.initial
      client

/-- The initial logarithm-refinement state for the client's actual argument. -/
def logState : LogarithmState.State
  client.argument :=
  LogarithmState.State.initial client.argument

/-- The initial denominator-refinement state of the same client. -/
def denominatorState :
    Refinement.State
  client.denominator :=
  Refinement.State.initial
      client.denominator

/-- The original argument ball satisfies the retained chart-safety certificate. -/
theorem initialLogSafety :
    Logarithm.Chart.Safety.Certificate
      sourceAnchor.chart.factor
      (client.argument.name.process.ball
        logState.source)
      logState.nextIndex := by
  decide

/-- The overlap requirement retaining the initial logarithm safety evidence. -/
def logRequirement :
    Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
      client.sourceInput
      client.argument
      client.source
      logState :=
  .overlap initialLogSafety

/-- The exact logarithm-overlap obstruction with denominator search still pending. -/
def logBlocked :
  Logarithm.Quotient.Requirement.Blocked client :=
  .logarithm logState
    logRequirement (.searching
    denominatorState) false

/-- The common value three halves certifies the retained logarithm overlap.

Keeps its actual possible-value witnesses for the source input and prepared quotient argument. -/
def logOverlap :
    Coherent.Overlap.OverlapWitness client.sourceInput
      (LogarithmState.preparedTarget
        logState) where
  point := threeHalves
  left_possible := rfl
  right_possible := by
    exact ⟨1, half, rfl, rfl, by decide⟩

/-- The original joint state resumed with the retained logarithm overlap. -/
def afterLog :
  Approximation.Gaussian.Logarithm.Quotient.State client :=
  logBlocked.resume
  logOverlap

/-- The actual first step of the original joint search. -/
def firstStep :
  Logarithm.Quotient.Step.StepResult client
  initial := Logarithm.Quotient.Step.step
  client
  initial

/-- The expected first-step obstruction requesting logarithm overlap. -/
def firstStepExpected :
  Logarithm.Quotient.Step.StepResult client
  initial :=
  .blocked logBlocked rfl

/-- The original exact denominator ball is separated from zero. -/
theorem denominatorSeparated :
    2 * (client.denominator.name.process.ball
      denominatorState.source).radiusSq <
      Data.Gaussian.Norm.Basic.normSq
        (client.denominator.name.process.ball
          denominatorState.source).center := by
  decide

/-- The candidate-apartness certificate from the retained denominator separation. -/
def denominatorEvidence :
  Apart.Possible.PossibleApart
    (Based.based client.denominator.name.process
      denominatorState.source) :=
  Partial.Preparation.evidenceOfSeparation denominatorState
    denominatorSeparated

/-- The joint state with the original logarithm and denominator evidence retained. -/
def afterBoth :
  Approximation.Gaussian.Logarithm.Quotient.State client :=
  Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorReady
    afterLog.log
    denominatorState
    denominatorEvidence
    false

/-- The actual next step after the logarithm overlap has been supplied. -/
def secondStep :
  Logarithm.Quotient.Step.StepResult client
  afterLog := Logarithm.Quotient.Step.step
  client
  afterLog

/-- The expected denominator-preparation transition of the second step. -/
def secondStepExpected :
  Logarithm.Quotient.Step.StepResult client
  afterLog :=
  .progressed afterBoth
    (.denominatorPrepared afterLog.log
      denominatorState
      denominatorEvidence
      true)

/-- The original partial logarithm requirement satisfied by its retained overlap. -/
def logSatisfied :
  Logarithm.Chart.Partial.Step.Satisfied
    client.sourceInput
      client.argument
      client.source
      logState :=
  Logarithm.Chart.Partial.Step.satisfy client.sourceInput
    client.argument
    client.source
    logState
    logRequirement
      logOverlap

/-- The quotient output name built from the retained logarithm and denominator states.

Reuses the original satisfied chart output and the actual candidate-apartness certificate. -/
def finalOutput :
  CoherentNamed :=
  Logarithm.Quotient.Ready.readyName client
    logState
    logSatisfied.output
    denominatorState
    denominatorEvidence

/-- Readiness certificate for the exact assembled logarithm-quotient output.

Retains the original logarithm state/output/validity and denominator state/evidence with its defining output identity.
-/
def finalReady :
  Approximation.Gaussian.Logarithm.Quotient.Ready client
  finalOutput where
  logState := logState
  logOutput := logSatisfied.output
  logValid := logSatisfied.valid
  denominatorState := denominatorState
  denominatorEvidence := denominatorEvidence
  output_eq := rfl

/-- After both retained requirements are satisfied the next step returns readiness.

Returns the actual coherent output and its original client-indexed certificate. -/
theorem third_step_is_ready :
    ∃ output : CoherentNamed, ∃ valid : Approximation.Gaussian.Logarithm.Quotient.Ready
      client output,
      Logarithm.Quotient.Step.step client
        afterBoth = .ready output valid := by
  simp only [afterBoth,
    afterLog,
    logBlocked, Logarithm.Quotient.Requirement.Blocked.resume]
  exact ⟨_, _, rfl⟩

end Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.WorkedExamples

end
