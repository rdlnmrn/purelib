module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite tail budgets

A potentially unbounded sum or refinement is observed through a displayed
partial amount and a nonnegative rational remainder budget.  Advancing a
budget is a wholly finite conservation calculation.
-/

namespace Purelib.Approximation

set_option genInjectivity false in
/-- A displayed partial amount with a certified nonnegative uncomputed tail. -/
structure TailBudget where
  /-- The displayed partial amount already computed. -/ amount : Fraction.Rational
  /-- The retained rational budget for the uncomputed tail. -/ remainder : Fraction.Rational
  /-- The uncomputed tail budget is nonnegative. -/ remainder_nonnegative : 0 ≤ remainder

constructive_injectivity TailBudget

namespace TailBudget

/-- The finite enclosure supplied by a partial amount and its tail budget. -/
def bound (budget : Approximation.TailBudget) : Rat.Interval where
  lower := budget.amount
  upper := budget.amount + budget.remainder
  valid := le_add_of_nonneg_right budget.remainder_nonnegative

/-- The width of the budget enclosure is exactly its retained remainder. -/
theorem bound_width (budget : Approximation.TailBudget) :
    budget.bound.width = budget.remainder := by
  dsimp only [Interval.width, Approximation.TailBudget.bound]
  ring1

/-- A budget meets a finite accuracy request exactly when its displayed tail does. -/
def Resolves (budget : Approximation.TailBudget) (epsilon : Fraction.Rational) : Prop :=
  budget.remainder < epsilon

/-- A resolved tail budget has enclosure width below the requested tolerance. -/
theorem bound_width_lt {budget : Approximation.TailBudget} {epsilon : Fraction.Rational}
    (resolves : budget.Resolves epsilon) :
    budget.bound.width < epsilon := by
  rw [Approximation.TailBudget.bound_width]
  exact resolves

/-- Advance by a displayed nonnegative contribution and a smaller tail. -/
def advance (budget : Approximation.TailBudget) (added newTail : Fraction.Rational)
    (newTailNonnegative : 0 ≤ newTail) : Approximation.TailBudget where
  amount := budget.amount + added
  remainder := newTail
  remainder_nonnegative := newTailNonnegative

/-- Exact finite conservation of the old remainder between the displayed new contribution and the new remainder. -/
def Conserves (budget : Approximation.TailBudget) (added newTail : Fraction.Rational) : Prop :=
  budget.remainder = added + newTail

/-- A nonnegative conserved advance narrows the old finite enclosure. -/
theorem advance_bound_refines (budget : Approximation.TailBudget)
    (added newTail : Fraction.Rational) (addedNonnegative : 0 ≤ added)
    (newTailNonnegative : 0 ≤ newTail)
    (conserves : budget.Conserves added newTail) :
    Interval.Refines (budget.advance added newTail newTailNonnegative).bound
      budget.bound := by
  constructor
  · dsimp only [Approximation.TailBudget.bound, Approximation.TailBudget.advance]
    exact le_add_of_nonneg_right addedNonnegative
  · dsimp only [Approximation.TailBudget.bound, Approximation.TailBudget.advance]
    rw [conserves]
    exact le_of_eq (by ring1)

/-- Any two explicitly supplied totals compatible with the same finite tail budget differ by at most that tail in both
directions. -/
theorem compatible_pairwise {budget : Approximation.TailBudget} {left right : Fraction.Rational}
    (leftInside : budget.bound.Contains left)
    (rightInside : budget.bound.Contains right) :
    left - right ≤ budget.remainder ∧ right - left ≤ budget.remainder := by
  simpa only [Approximation.TailBudget.bound_width] using
    Interval.pairwise_difference_le leftInside rightInside

end TailBudget

end Purelib.Approximation

end
