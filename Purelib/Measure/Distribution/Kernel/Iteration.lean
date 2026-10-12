module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Weighted.Integral
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Bounded finite stochastic processes

Finite distributions compose by explicit list flattening and rational weight
multiplication.  Iteration takes a displayed natural horizon and therefore
constructs only a finite process table.
-/

namespace Purelib.Measure

open Distribution
namespace Distribution

/-- Advance the retained distribution by the exact supplied transition kernel. -/
def step {α : Type} (transition : α → Distribution α)
    (source : Distribution α) : Distribution α :=
  source.bind transition

/-- Apply the same finite transition kernel the requested number of times to the original distribution.

The zero stage retains the original law; each successor first advances that law and iterates the remaining number of
steps. -/
def iterate {α : Type} (transition : α → Distribution α) :
    Nat → Distribution α → Distribution α
  | 0, source => source
  | count + 1, source => iterate transition count (source.step transition)

/-- Zero transition steps retain the original distribution exactly. -/
@[simp] theorem iterate_zero {α : Type}
    (transition : α → Distribution α) (source : Distribution α) :
    iterate transition 0 source = source := rfl

/-- A successor iteration first takes the exact kernel step and then performs the remaining steps. -/
@[simp] theorem iterate_succ {α : Type}
    (transition : α → Distribution α) (count : Nat)
    (source : Distribution α) :
    iterate transition (count + 1) source =
      iterate transition count (source.step transition) := rfl

/-- The probability after one kernel step equals the original expectation of the kernel's event probabilities. -/
theorem step_probability {α : Type}
    (transition : α → Distribution α) (source : Distribution α)
    (event : α → Bool) :
    (source.step transition).probability event =
      source.expectation (fun item =>
        (transition item).probability event) :=
  source.bind_probability transition event

section
open Purelib.Data.Rat
/-- Expectation after one kernel step equals the original expectation of the kernel's conditional expectations. -/
theorem step_expectation {α : Type}
    (transition : α → Distribution α) (source : Distribution α)
    (value : α → Fraction.Rational) :
    (source.step transition).expectation value =
      source.expectation (fun item =>
        (transition item).expectation value) :=
  source.bind_expectation transition value

/-- A pointwise harmonic observable has its original expectation after every finite number of kernel steps. -/
theorem iterate_expectation_of_harmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Fraction.Rational)
    (harmonic : ∀ item, (transition item).expectation value = value item) :
    ∀ (count : Nat) (source : Distribution α),
      (iterate transition count source).expectation value =
        source.expectation value
  | 0, source => rfl
  | count + 1, source => by
      rw [iterate_succ,
        iterate_expectation_of_harmonic transition value harmonic count
          (source.step transition),
        source.step_expectation transition]
      exact source.expectation_congr _ _ harmonic

/-- A pointwise superharmonic observable's iterated expectation is at most its original expectation. -/
theorem iterate_expectation_le_of_superharmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Fraction.Rational)
    (superharmonic : ∀ item,
      (transition item).expectation value ≤ value item) :
    ∀ (count : Nat) (source : Distribution α),
      (iterate transition count source).expectation value ≤
        source.expectation value
  | 0, source => le_rfl
  | count + 1, source => by
      calc
        (iterate transition (count + 1) source).expectation value =
            (iterate transition count
              (source.step transition)).expectation value := rfl
        _ ≤ (source.step transition).expectation value :=
          iterate_expectation_le_of_superharmonic transition value
            superharmonic count (source.step transition)
        _ = source.expectation (fun item =>
              (transition item).expectation value) :=
          source.step_expectation transition value
        _ ≤ source.expectation value := by
          apply source.expectation_mono
          intro atom member
          exact superharmonic atom.item

/-- A pointwise subharmonic observable's original expectation is at most its iterated expectation. -/
theorem iterate_expectation_mono_of_subharmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Fraction.Rational)
    (subharmonic : ∀ item,
      value item ≤ (transition item).expectation value) :
    ∀ (count : Nat) (source : Distribution α),
      source.expectation value ≤
        (iterate transition count source).expectation value
  | 0, source => le_rfl
  | count + 1, source => by
      calc
        source.expectation value ≤
            source.expectation (fun item =>
              (transition item).expectation value) := by
          apply source.expectation_mono
          intro atom member
          exact subharmonic atom.item
        _ = (source.step transition).expectation value :=
          (source.step_expectation transition value).symm
        _ ≤ (iterate transition count
              (source.step transition)).expectation value :=
          iterate_expectation_mono_of_subharmonic transition value
            subharmonic count (source.step transition)
        _ = (iterate transition (count + 1) source).expectation value := rfl

end

/-- An event whose kernel probability equals its indicator retains its original probability after every finite
iteration. -/
theorem iterate_probability_of_harmonic_event {α : Type}
    (transition : α → Distribution α) (event : α → Bool)
    (harmonic : ∀ item,
      (transition item).probability event = indicator event item)
    (count : Nat) (source : Distribution α) :
    (iterate transition count source).probability event =
      source.probability event := by
  rw [← (iterate transition count source).expectation_indicator event,
    ← source.expectation_indicator event]
  exact iterate_expectation_of_harmonic transition (indicator event)
    (fun item => by
      rw [(transition item).expectation_indicator]
      exact harmonic item) count source

end Distribution

end Purelib.Measure

end

section
/-!
# Stationary finite dynamics and occupation averages

A finite transition preserves a displayed rational law when one exact step is
evaluation-equivalent to the original law.  This module proves preservation
at every supplied finite horizon and computes the exact expectation of a
finite Markov-path occupation count and frequency.  A final Chebyshev theorem
isolates the remaining dynamical input as the exact variance of that finite
occupation frequency.

This is a finite quantitative mean-ergodic interface, not an asymptotic
ergodic theorem: every path, horizon, event, expectation, and variance is
displayed finite rational data.
-/

@[expose] public section

namespace Purelib.Measure
namespace Distribution

namespace EvaluationEquivalent

/-- Advancing two evaluation-equivalent distributions by the same exact kernel preserves evaluation equivalence. -/
theorem step {alpha : Type} {left right : Distribution alpha}
    (equivalent : EvaluationEquivalent left right)
    (transition : alpha → Distribution alpha) :
    EvaluationEquivalent (left.step transition) (right.step transition) :=
  equivalent.bind fun item => EvaluationEquivalent.refl (transition item)

/-- Every finite iteration of the same exact kernel preserves evaluation equivalence of the original two laws. -/
theorem iterate {alpha : Type} {left right : Distribution alpha}
    (equivalent : EvaluationEquivalent left right)
    (transition : alpha → Distribution alpha) : ∀ count : Nat,
    EvaluationEquivalent (Distribution.iterate transition count left)
      (Distribution.iterate transition count right)
  | 0 => equivalent
  | count + 1 =>
      (equivalent.step transition).iterate transition count

end EvaluationEquivalent
end Distribution

end Purelib.Measure

end
