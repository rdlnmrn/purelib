module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Positive.Enclosure
import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Positive
public import Purelib.Curves.Legendre.Acquisition.Positive

import Purelib.Curves.Legendre.GuaranteedFold
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.State

open Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.Acquisition

open Purelib.Curves.Legendre.Acquisition.Automatic

open Purelib.Data.Rat

open Purelib.Topology.Knot.Braid

@[expose] public section

/-!
# Finite regression clients for discovered Legendre positivity

The delayed imaginary unit first exhausts a budget, then succeeds from the
retained state. The exact zero client stays unresolved at every finite budget.
These exercise both outcomes without evaluating a large generated period bank.
-/

namespace Test.Curves.Legendre.PositivityAcquisition

open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- The exact Gaussian-rational coefficient type used by the acquisition regressions. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical

/-- The finite Gaussian approximation process type. -/
abbrev Process := Approximation.Gaussian.Process
/-- The retained cross-state coherence certificate for a Gaussian approximation process. -/
abbrev Coherent := Gaussian.Process.Coherence.Basic.Coherent

/-- The exact Gaussian point with zero real coordinate and unit imaginary coordinate. -/
def imaginaryUnit : Gaussian := point 0 1

/-- A two-state process whose first enclosure is inconclusive and whose refinement exposes the exact imaginary unit.

Both states retain the same possible value and witness; refinement changes only the certified enclosure. -/
def delayedProcess : PositivityAcquisition.Process where
  State := Bool
  ball state := if state then
    { center := PositivityAcquisition.imaginaryUnit, radiusSq := 0, radiusSq_nonneg := le_rfl }
    else { center := 0, radiusSq := 4, radiusSq_nonneg := by decide }
  Possible _ value := value = PositivityAcquisition.imaginaryUnit
  witness _ := ⟨imaginaryUnit, rfl⟩
  possible_inside := by
    intro state value equal
    subst value
    cases state <;> decide
  refine _ _ _ := true
  refine_persists := by
    intro state target positive value possible
    exact possible
  accurate := by
    intro state target positive
    exact positive
  centerBound := 1
  centerBound_nonneg := by decide
  center_bounded := by
    intro state
    cases state <;> decide

/-- The initial squared allowance is four and the refined exact allowance is zero. -/
def delayedAllowance (state : Bool) : Fraction.Rational := if state then 0 else 4

/-- The coherence certificate retaining the same imaginary-unit value across both delayed process states. -/
def delayedCoherent : PositivityAcquisition.Coherent PositivityAcquisition.delayedProcess where
  allowance := PositivityAcquisition.delayedAllowance
  allowance_nonneg := by intro state; cases state <;> decide
  ball_radius_le := by intro state; cases state <;> decide
  possible_close := by
    intro left right leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    cases left <;> cases right <;> decide
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

/-- The coherent delayed imaginary-unit name at its original unresolved state. -/
def delayed : Coherent.CoherentNamed where
  name := { process := PositivityAcquisition.delayedProcess, state := false }
  coherent := PositivityAcquisition.delayedCoherent

/-- The original radius-four enclosure does not certify strict imaginary positivity. -/
theorem initial_unresolved : ¬ Positive.PositiveTest (State.initial PositivityAcquisition.delayed).ball := by decide

/-- The retained first refinement certifies strict imaginary positivity of the exact imaginary unit. -/
theorem refined_positive : Positive.PositiveTest (State.advance (State.initial PositivityAcquisition.delayed)).ball :=
  by decide

/-- One unit of work retains its genuine refinement on exhaustion. -/
theorem one_unit_exhausts :
    Search.attempt PositivityAcquisition.delayed (State.initial PositivityAcquisition.delayed) 1 = .exhausted
      (State.advance (State.initial PositivityAcquisition.delayed)) := by
  rw [Search.attempt_succ_of_unresolved (State.initial PositivityAcquisition.delayed)
    PositivityAcquisition.initial_unresolved 0]
  rfl

/-- The retained state succeeds with one further inspection, without a caller-supplied enclosure or denominator
preparation. -/
theorem resumed_succeeds :
    Search.attempt PositivityAcquisition.delayed (State.advance (State.initial PositivityAcquisition.delayed)) 1 =
      .ready (Enclosure.enclosure (State.advance (State.initial PositivityAcquisition.delayed))
        PositivityAcquisition.refined_positive) :=
  Search.attempt_one_of_positive _ PositivityAcquisition.refined_positive

/-- Two units of work refine the original unresolved state and then return its certified positive enclosure. -/
theorem two_units_succeed :
    Search.attempt PositivityAcquisition.delayed (State.initial PositivityAcquisition.delayed) 2 =
      .ready (Enclosure.enclosure (State.advance (State.initial PositivityAcquisition.delayed))
        PositivityAcquisition.refined_positive) := by
  rw [Search.attempt_succ_of_unresolved (State.initial PositivityAcquisition.delayed)
    PositivityAcquisition.initial_unresolved 1]
  exact PositivityAcquisition.resumed_succeeds

/-- Automatic discovery feeds the certified evaluator for any displayed finite word; this example supplies no per-word
certificates. -/
theorem discovered_word_ready (word : ThreeStrand.Word) :
    Purelib.Curves.Legendre.Acquisition.Positive.attemptTransport PositivityAcquisition.delayed word (State.initial
      PositivityAcquisition.delayed) 2 =
      .ready (Positive.guaranteed
        (Enclosure.enclosure (State.advance (State.initial PositivityAcquisition.delayed))
          PositivityAcquisition.refined_positive) word) := by
  unfold Positive.attemptTransport
  rw [PositivityAcquisition.two_units_succeed]

/-- The same discovery prepares every intermediate division as well. -/
theorem discovered_fold_ready (word : ThreeStrand.Word) :
    Purelib.Curves.Legendre.Acquisition.Positive.attemptFold PositivityAcquisition.delayed word (State.initial
      PositivityAcquisition.delayed) 2 =
      .ready (GuaranteedFold.prepareWord
        (Enclosure.enclosure (State.advance (State.initial PositivityAcquisition.delayed))
          PositivityAcquisition.refined_positive) word) := by
  unfold Positive.attemptFold
  rw [PositivityAcquisition.two_units_succeed]

/-- The coherent exact Gaussian zero input. -/
def zeroInput : CoherentNamed := Coherence.exact 0

/-- Every retained state of the exact zero name fails strict imaginary positivity. -/
theorem zero_unresolved (state : Approximation.Gaussian.Acquisition.State PositivityAcquisition.zeroInput) : ¬
    Positive.PositiveTest state.ball := by
  rw [state.ball_eq]
  intro test
  exact (lt_irrefl (0 : Fraction.Rational)) test.1

/-- No finite amount of work invents positivity for the exact zero input. The result is exhaustion, preserving the
finite refinement state. -/
theorem zero_exhausts (state : Approximation.Gaussian.Acquisition.State PositivityAcquisition.zeroInput) (fuel : Nat) :
    Search.attempt PositivityAcquisition.zeroInput state fuel = .exhausted (Schedule.advanceN state fuel) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [Search.attempt_succ_of_unresolved state (PositivityAcquisition.zero_unresolved state) fuel]
      exact inductionHypothesis (State.advance state)

end Test.Curves.Legendre.PositivityAcquisition
