import CCL.Progressive.PartialDivision
import CCL.Riemann.LegendreFractionalWords

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

namespace CCL.Riemann.LegendreDenominatorAcquisition

open CCL.Riemann.LegendreModularMonodromy
open CCL.Riemann.LegendreFractionalAction

abbrev IntegralMatrix :=
  CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev DenominatorPreparation :=
  CCL.Riemann.LegendreModularMonodromy.DenominatorPreparation
abbrev PossibleApart := CCL.ProgressiveCharts.PossibleApart

/-- Retained generic division state specialized to one exact fractional
denominator. -/
abbrev State (matrix : IntegralMatrix) (tau : CoherentNamed) :=
  CCL.ProgressivePartialDivision.State (fractionalDenominator matrix tau)

/-- Initial state of the bounded transformed-denominator search. -/
def initial (matrix : IntegralMatrix) (tau : CoherentNamed) :
    State matrix tau :=
  CCL.ProgressivePartialDivision.State.initial
    (fractionalDenominator matrix tau)

/-- Convert retained-state apartness into a modular preparation.  The based
denominator is not confused with the original process: their operational
equivalence is retained explicitly. -/
def preparationAt (matrix : IntegralMatrix) (tau : CoherentNamed)
    (state : State matrix tau)
    (evidence : PossibleApart
      (CCL.ProgressiveCharts.based
        (fractionalDenominator matrix tau).name.process state.source)) :
    DenominatorPreparation (fractionalDenominator matrix tau) where
  prepared := CCL.ProgressivePartialDivision.preparedDenominator state evidence
  apart := CCL.ProgressivePartialDivision.preparedApart state evidence
  equivalent :=
    CCL.ProgressivePartialDivision.preparedDenominatorEquivalent state evidence

/-- Lightweight carrier for one preparation step.  Keeping its recursor
independent of the expanded fractional process avoids elaborating that large
expression while generating the inductive declaration. -/
inductive StepResultPayload.{u, v, w} (readyType : Type u)
    (stateType : Type v) (progressType : stateType -> Type w) :
    Type (max u (max v w))
  | ready (preparation : readyType)
  | progressed (next : stateType) (progress : progressType next)

/-- One finite inspection either returns a directly consumable modular
preparation or performs the canonical generic-division refinement. -/
def StepResult (matrix : IntegralMatrix) (tau : CoherentNamed)
    (state : State matrix tau) : Type 1 :=
  StepResultPayload
    (DenominatorPreparation (fractionalDenominator matrix tau))
    (State matrix tau)
    (fun next => CCL.ProgressivePartialDivision.Progress state next)

/-- Thin adapter over `ProgressivePartialDivision.prepare`. -/
def step (matrix : IntegralMatrix) (tau : CoherentNamed)
    (state : State matrix tau) : StepResult matrix tau state :=
  match CCL.ProgressivePartialDivision.prepare
      (fractionalDenominator matrix tau) state with
  | .prepared evidence => .ready (preparationAt matrix tau state evidence)
  | .progressed next progress => .progressed next progress

/-- The exact manually satisfiable requirement at a retained search state. -/
abbrev Requirement {matrix : IntegralMatrix} {tau : CoherentNamed}
    (state : State matrix tau) :=
  CCL.ProgressivePartialDivision.Requirement state

/-- Evidence remains indexed by that exact retained state. -/
abbrev Evidence {matrix : IntegralMatrix} {tau : CoherentNamed}
    {state : State matrix tau} (requirement : Requirement state) :=
  CCL.ProgressivePartialDivision.Evidence requirement

/-- Expose the unique candidate-apartness requirement without performing
another refinement. -/
def currentRequirement {matrix : IntegralMatrix} {tau : CoherentNamed}
    (state : State matrix tau) : Requirement state :=
  .candidateApartness

/-- Resume at exactly the state which requested the supplied based apartness. -/
def resume (matrix : IntegralMatrix) (tau : CoherentNamed)
    (state : State matrix tau) (requirement : Requirement state)
    (evidence : Evidence requirement) : StepResult matrix tau state :=
  match requirement with
  | .candidateApartness => .ready (preparationAt matrix tau state evidence)

/-- The adapter inherits the generic preflight's empty exclusion family. -/
abbrev Exclusion {matrix : IntegralMatrix} {tau : CoherentNamed}
    (state : State matrix tau) :=
  CCL.ProgressivePartialDivision.Exclusion state

/-- Finite reachability consists solely of actual generic-division refinement
steps. -/
abbrev Reachable {matrix : IntegralMatrix} {tau : CoherentNamed}
    (first last : State matrix tau) :=
  CCL.ProgressivePartialDivision.Reachable first last

/-- Lightweight carrier for a bounded acquisition result. -/
inductive RunResultPayload.{u, v, w} (readyType : Type u)
    (stateType : Type v) (reachableType : stateType -> Type w) :
    Nat -> Type (max u (max v w))
  | ready {fuel : Nat} (final : stateType)
      (reachable : reachableType final) (preparation : readyType) :
      RunResultPayload readyType stateType reachableType fuel
  | exhausted {fuel : Nat} (final : stateType)
      (reachable : reachableType final) :
      RunResultPayload readyType stateType reachableType fuel

/-- Result of a caller-bounded preparation run.  Exhaustion retains the exact
state and means only that the finite fuel ended. -/
def RunResult (matrix : IntegralMatrix) (tau : CoherentNamed)
    (start : State matrix tau) (fuel : Nat) : Type 1 :=
  RunResultPayload
    (DenominatorPreparation (fractionalDenominator matrix tau))
    (State matrix tau) (fun final => Reachable start final) fuel

/-- Structurally recursive bounded acquisition.  Exactly one unit of fuel is
consumed by each certified progress step. -/
def attempt (matrix : IntegralMatrix) (tau : CoherentNamed)
    (start : State matrix tau) :
    (fuel : Nat) -> RunResult matrix tau start fuel
  | 0 => .exhausted start (.refl start)
  | fuel + 1 =>
      match step matrix tau start with
      | .ready preparation => .ready start (.refl start) preparation
      | .progressed next progress =>
          match attempt matrix tau next fuel with
          | .ready final reachable preparation =>
              .ready final (.tail progress reachable) preparation
          | .exhausted final reachable =>
              .exhausted final (.tail progress reachable)

@[simp] theorem attempt_zero (matrix : IntegralMatrix) (tau : CoherentNamed)
    (state : State matrix tau) :
    attempt matrix tau state 0 = .exhausted state (.refl state) := rfl

theorem exclusion_impossible {matrix : IntegralMatrix} {tau : CoherentNamed}
    {state : State matrix tau} (excluded : Exclusion state) : False := by
  exact nomatch excluded

@[simp] theorem resume_is_ready (matrix : IntegralMatrix)
    (tau : CoherentNamed) (state : State matrix tau)
    (evidence : Evidence (currentRequirement state)) :
    resume matrix tau state (currentRequirement state) evidence =
      .ready (preparationAt matrix tau state evidence) := rfl

/-! ## Ready output and schedule independence -/

/-- The ordinary productive fractional output returned after readiness. -/
def readyOutput (matrix : IntegralMatrix) (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) : CoherentNamed :=
  fractionalLinear matrix tau preparation

/-- Different finite schedules which prepare the same exact transformed
denominator produce operationally equivalent outputs. -/
def ready_respects (matrix : IntegralMatrix) (tau : CoherentNamed)
    (first second : DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    NamedEquivalent (readyOutput matrix tau first).name
      (readyOutput matrix tau second).name := by
  simpa only [readyOutput] using
    fractionalLinear_preparation_independent matrix tau first second

/-- A ready transformed output retains the unchanged finite productivity
contract. -/
theorem ready_productive (matrix : IntegralMatrix) (tau : CoherentNamed)
    (preparation : DenominatorPreparation
      (fractionalDenominator matrix tau)) (count : Nat) :
    (readyOutput matrix tau preparation).name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (readyOutput matrix tau preparation).name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (readyOutput matrix tau preparation).name.machine count).emitted.length =
        count :=
  (readyOutput matrix tau preparation).name.productive count

/-! ## Standard-loop adapters -/

/-- Uniform apartness of a terminating nonzero rational name. -/
private def exactApart (value : RFAP.ConstructiveGaussian.Gaussian)
    (nonzero : value ≠ 0) :
    CCL.ProgressiveTransducer.Named.Apart
      (CCL.ProgressiveCoherence.CoherentNamed.exact value).name where
  certificate :=
    { lowerSq := RFAP.ConstructiveGaussian.Gaussian.normSq value
      positive := RFAP.ConstructiveGaussian.Gaussian.normSq_pos nonzero
      lower := by
        intro state candidate inside
        change RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate - value) <= 0 at inside
        have normZero : RFAP.ConstructiveGaussian.Gaussian.normSq
            (candidate - value) = 0 :=
          le_antisymm inside
            (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        have differenceZero :=
          RFAP.ConstructiveGaussian.Gaussian.normSq_eq_zero.mp normZero
        have equal : candidate = value := sub_eq_zero.mp differenceZero
        rw [equal] }

/-- The one-loop denominator needs no search: it is operationally the exact
nonzero constant one. -/
def standardOnePreparation (tau : CoherentNamed) :
    StandardOnePreparation tau where
  prepared := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  apart := exactApart 1 (by decide)
  equivalent := one_denominator_one tau

/-- Bounded zero-loop denominator acquisition from the initial state. -/
def attemptStandardZero (tau : CoherentNamed) (fuel : Nat) :
    RunResult CCL.Riemann.LegendreMonodromy.zeroMatrix tau
      (initial CCL.Riemann.LegendreMonodromy.zeroMatrix tau) fuel :=
  attempt CCL.Riemann.LegendreMonodromy.zeroMatrix tau
    (initial CCL.Riemann.LegendreMonodromy.zeroMatrix tau) fuel

/-- Bounded infinity-loop denominator acquisition from the initial state. -/
def attemptStandardInfinity (tau : CoherentNamed) (fuel : Nat) :
    RunResult CCL.Riemann.LegendreMonodromy.infinityMatrix tau
      (initial CCL.Riemann.LegendreMonodromy.infinityMatrix tau) fuel :=
  attempt CCL.Riemann.LegendreMonodromy.infinityMatrix tau
    (initial CCL.Riemann.LegendreMonodromy.infinityMatrix tau) fuel

/-- Lightweight pair of ready standard preparations. -/
structure StandardReadyPayload (zeroType infinityType : Type 1) where
  zero : zeroType
  infinity : infinityType

def StandardReady (tau : CoherentNamed) : Type 1 :=
  StandardReadyPayload (StandardZeroPreparation tau)
    (StandardInfinityPreparation tau)

end CCL.Riemann.LegendreDenominatorAcquisition
