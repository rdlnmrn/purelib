module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Process.Recipe.Request
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Process.Translation
public import Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples
import Purelib.Integration.Program.Gaussian.Query.Recipe
public import Purelib.Integration.Program.Gaussian.Query.Representation
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation

import Purelib.CCL.Progressive.IntegrationQueries
import Mathlib.Algebra.Ring.Defs
import Purelib.Computation.Query.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic

@[expose] public section

/-!
# Numerical replay across the existing chart operations

The concrete composition apartifies an exact source, divides by it, scales
and translates.  Its representation is derived compositionally from the
actual certified processes.  These regressions exercise chart observations;
they do not stand in for the still-required whole-transducer replay bridge.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Query.Chart.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian (Process)
open Purelib.Examples.Integration.Polynomial.Gaussian

open Purelib.Approximation
open Purelib.CCL
open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Integration

/-- The cached certified constant-one polynomial integration program. -/
def program : Program.Gaussian.Cached.Basic.CachedProgram :=
  Transport.WorkedExamples.oneProgram.certifiedView.program

/-- The original approximation process of the retained integration program. -/
def sourceProcess : Process :=
  program.approximation.toProcess

/-- The source process is apart from zero with squared lower bound one.

Every possible source value is a retained later sample, whose exact constant value proves the bound. -/
def sourceApart : Gaussian.Process.Apart.Possible.PossibleApart
  sourceProcess where
  lowerSq := 1
  positive := by decide
  lower := by
    intro state value possible
    change ∃ later : Nat, (show Nat from state) ≤ later ∧ value =
      program.approximation.sample later at possible
    obtain ⟨later, _, rfl⟩ := possible
    change (1 : Rational) ≤ Data.Gaussian.Norm.Basic.normSq
      (Transport.WorkedExamples.oneProgram.approximation.sample later)
    rw [Transport.WorkedExamples.oneProgram_sample]
    decide

/-- The source process prepared with its retained apartness certificate. -/
def apartProcess : Process := Gaussian.Process.Apart.Preparation.apartify
  sourceApart
/-- The numerical recipe apartifying the original source with lower bound one. -/
def apartRecipe : Process.Recipe := .apart .source 1
/-- The apart recipe represents the actual prepared source process. -/
def apartRepresentation : Program.Gaussian.Query.Representation.Represents
  program
  apartRecipe apartProcess :=
  (Program.Gaussian.Query.Representation.Represents.source
    program).apartified
    sourceApart

/-- The process dividing the exact unit by the retained apart source. -/
def inverseProcess : Process := Process.div
  (Process.exact 1) apartProcess
    (Gaussian.Process.Apart.Preparation.apartifyApart
    sourceApart)
/-- The division recipe retaining the original apart request and inverse accuracy allowance. -/
def inverseRecipe : Process.Recipe :=
  apartRecipe.divided 1 (1 / 8)
/-- The division recipe represents the actual inverse process. -/
def inverseRepresentation : Program.Gaussian.Query.Representation.Represents
  program
  inverseRecipe inverseProcess :=
  apartRepresentation.divided 1
    (Gaussian.Process.Apart.Preparation.apartifyApart
    sourceApart)

/-- The process multiplying the retained inverse by the exact scalar two. -/
def scaledProcess : Process := Process.mul
  (Process.exact 2) inverseProcess
/-- The scaled recipe under the original source replay control. -/
def scaledRecipe : Process.Recipe :=
  inverseRecipe.scaled (Progressive.IntegrationReplay.control
  program) 2
/-- The scaled recipe represents the actual multiplied process. -/
def scaledRepresentation : Program.Gaussian.Query.Representation.Represents
  program
  scaledRecipe scaledProcess :=
  inverseRepresentation.scaled 2

/-- The process translating the retained scaled process by one. -/
def translatedProcess : Process := Gaussian.Process.Translation.translate
  scaledProcess 1
/-- The translated recipe under the original source replay control. -/
def translatedRecipe : Process.Recipe :=
  scaledRecipe.translated (Progressive.IntegrationReplay.control
  program) 1
/-- The translated recipe represents the actual translated process. -/
def translatedRepresentation : Program.Gaussian.Query.Representation.Represents
  program
  translatedRecipe translatedProcess :=
  scaledRepresentation.translated 1

/-- The retained arithmetic-process state whose source refinement index is seven. -/
def state : translatedProcess.State :=
  ((), ((), Gaussian.Process.Apart.Preparation.prepareApartState
    sourceApart (7 : Nat)))

/-- The translated recipe retains center bound 66. -/
theorem retained_bound : translatedRecipe.centerBound
  (Progressive.IntegrationReplay.control program) = 66 := by
  decide +kernel

/-- The retained translated-process state has source index seven. -/
theorem retained_source_index : translatedRepresentation.index
  state = 7 := by decide +kernel

/-- The actual process refinement and numerical recipe select the same source index for every positive target. -/
theorem actual_refinement_matches (target : Rational) (positive : 0 < target) :
    translatedRepresentation.index
      (translatedProcess.refine state target positive) =
      translatedRecipe.refine
        (Progressive.IntegrationReplay.control program)
        (translatedRepresentation.index state) target :=
  translatedRepresentation.refine_eq state target positive

/-- The numerical ball observation at retained source index seven. -/
def observed := translatedRecipe.ball
  (Progressive.IntegrationReplay.control program) 7

/-- The observed numerical ball is exactly center one with radius zero. -/
theorem observed_value : (observed.run
  program.stage).value = .ok ⟨1, 0⟩ := by decide +kernel

/-- The observation records exactly one source request, at index seven. -/
theorem observed_source_queries :
    (observed.run
      program.stage).trace.map
      Computation.Query.Basic.Exchange.query = [7] := by
  rw [observed,
      Process.Recipe.ball_trace]
  rfl

/-- The generated observation trace replays to the same exact ball. -/
theorem replay_generated :
    observed.replayExact
      (observed.run
      program.stage).trace = .ok (.ok ⟨1, 0⟩) := by
  rw [Computation.Query.Protocol.replayExact_run,
    observed_value]

/-- An empty observation trace is rejected as missing index seven. -/
theorem replay_missing : observed.replayExact [] = .error
  (.missing 7) := by decide +kernel

/-- A reply tagged with index eight is rejected when index seven is requested. -/
theorem replay_mismatched :
    observed.replayExact [⟨8,
      program.stage 7⟩] = .error (.mismatch 7 8 (by decide)) :=
      by decide +kernel

/-- The recipe observation projects to the ball of the same retained certified arithmetic-process state. -/
theorem observed_actual_ball :
    ((translatedRecipe.ball
      (Progressive.IntegrationReplay.control program)
      (translatedRepresentation.index state)).run
        program.stage).value =
        .ok (Gaussian.Enclosure.Ball.Data.BallData.ofBall
          (translatedProcess.ball state)) :=
  translatedRepresentation.ball_run state

/-- The actual retained translated-process ball has center one and radius zero. -/
theorem actual_ball_value : Gaussian.Enclosure.Ball.Data.BallData.ofBall
  (translatedProcess.ball state) = ⟨1, 0⟩ := by
  have projected := observed_actual_ball
  rw [retained_source_index] at projected
  change (observed.run
    program.stage).value = .ok _ at projected
  rw [observed_value] at projected
  exact (Except.ok.inj projected).symm

end Purelib.Examples.Integration.Program.Gaussian.Query.Chart.WorkedExamples

end
