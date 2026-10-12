module
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Request.Addition
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace Purelib.Approximation.Gaussian.Process

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Data.Rat

section Process

/-- Add two stateful finite enclosure processes using pairs of their original states.

Possible sums retain both operand readings; refinement requests one quarter of the output target from each original
process. -/
@[expose] public def add (left right :
  Process) : Process where
  State := left.State × right.State
  ball state := (left.ball state.1).add (right.ball state.2)
  Possible state value := ∃ x y : Data.Gaussian.Basic.Canonical,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x + y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x + y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact Enclosure.Ball.contains_add
      (left.possible_inside xPossible) (right.possible_inside yPossible)
  refine state target positive :=
    let inputPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    (left.refine state.1 (Name.additiveInputTarget target) inputPositive,
      right.refine state.2 (Name.additiveInputTarget target) inputPositive)
  refine_persists := by
    rintro state target positive value
      ⟨x, y, xPossible, yPossible, equal⟩
    exact ⟨x, y,
      left.refine_persists state.1 _ _ xPossible,
      right.refine_persists state.2 _ _ yPossible,
      equal⟩
  accurate := by
    intro state target positive
    apply Name.add_radius_lt
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  center_bounded := by
    intro state
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.center_bounded state.1)
          (right.center_bounded state.2)) (by decide))

/-- Negate a stateful finite enclosure process while retaining its original states and refinement operation.

Possible readings retain the original source reading and its negation identity. -/
@[expose] public def neg (process :
  Process) : Process where
  State := process.State
  ball state := (process.ball state).neg
  Possible state value := ∃ source : Data.Gaussian.Basic.Canonical,
    process.Possible state source ∧ value = -source
  witness state := by
    rcases process.witness state with ⟨source, possible⟩
    exact ⟨-source, source, possible, rfl⟩
  possible_inside := by
    rintro state value ⟨source, possible, rfl⟩
    exact Enclosure.Ball.contains_neg
      (process.possible_inside possible)
  refine := process.refine
  refine_persists := by
    rintro state target positive value ⟨source, possible, equal⟩
    exact ⟨source, process.refine_persists state target positive possible, equal⟩
  accurate := process.accurate
  centerBound := process.centerBound
  centerBound_nonneg := process.centerBound_nonneg
  center_bounded := by
    intro state
    change Data.Gaussian.Norm.Basic.normSq (-(process.ball state).center) ≤ process.centerBound
    rw [Data.Gaussian.Norm.Basic.normSq_neg]
    exact process.center_bounded state

/-- Subtract stateful enclosure processes by adding the left process to the negated right process. -/
@[expose] public def sub (left right :
  Process) : Process := left.add right.neg
end Process

end Purelib.Approximation.Gaussian.Process

end
