import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Bounds

/-!
# Finite tail budgets

A potentially unbounded sum or refinement is observed through a displayed
partial amount and a nonnegative rational remainder budget.  Advancing a
budget is a wholly finite conservation calculation.
-/

namespace FiniteMeasure

/-- A displayed partial amount with a certified nonnegative uncomputed tail. -/
structure TailBudget where
  amount : Coordinate
  remainder : Coordinate
  remainder_nonnegative : 0 ≤ remainder

namespace TailBudget

/-- The finite enclosure supplied by a partial amount and its tail budget. -/
def bound (budget : TailBudget) : Bound where
  lower := budget.amount
  upper := budget.amount + budget.remainder
  valid := le_add_of_nonneg_right budget.remainder_nonnegative

theorem bound_width (budget : TailBudget) :
    budget.bound.width = budget.remainder := by
  dsimp only [Bound.width, bound]
  ring1

/-- A budget meets a finite accuracy request exactly when its displayed tail
does. -/
def Resolves (budget : TailBudget) (epsilon : Coordinate) : Prop :=
  budget.remainder < epsilon

theorem bound_width_lt {budget : TailBudget} {epsilon : Coordinate}
    (resolves : budget.Resolves epsilon) :
    budget.bound.width < epsilon := by
  rw [bound_width]
  exact resolves

/-- Advance by a displayed nonnegative contribution and a smaller tail. -/
def advance (budget : TailBudget) (added newTail : Coordinate)
    (newTailNonnegative : 0 ≤ newTail) : TailBudget where
  amount := budget.amount + added
  remainder := newTail
  remainder_nonnegative := newTailNonnegative

/-- Exact finite conservation of the old remainder between the displayed
new contribution and the new remainder. -/
def Conserves (budget : TailBudget) (added newTail : Coordinate) : Prop :=
  budget.remainder = added + newTail

/-- A nonnegative conserved advance narrows the old finite enclosure. -/
theorem advance_bound_refines (budget : TailBudget)
    (added newTail : Coordinate) (addedNonnegative : 0 ≤ added)
    (newTailNonnegative : 0 ≤ newTail)
    (conserves : budget.Conserves added newTail) :
    Bound.Refines (budget.advance added newTail newTailNonnegative).bound
      budget.bound := by
  constructor
  · dsimp only [bound, advance]
    exact le_add_of_nonneg_right addedNonnegative
  · dsimp only [bound, advance]
    rw [conserves]
    exact le_of_eq (by ring1)

/-- Any two explicitly supplied totals compatible with the same finite tail
budget differ by at most that tail in both directions. -/
theorem compatible_pairwise {budget : TailBudget} {left right : Coordinate}
    (leftInside : budget.bound.Contains left)
    (rightInside : budget.bound.Contains right) :
    left - right ≤ budget.remainder ∧ right - left ≤ budget.remainder := by
  simpa only [bound_width] using
    Bound.pairwise_difference_le leftInside rightInside

end TailBudget

end FiniteMeasure
