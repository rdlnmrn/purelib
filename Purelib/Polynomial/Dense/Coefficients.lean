module

public import Mathlib.Algebra.Notation.Defs

/-! Exact retained endpoints of descending coefficient tables. -/

/-!
# Retained constant coefficients of descending coefficient tables

The original last-entry accumulator selects the displayed constant coefficient.
Its certificates preserve that same observation under prefix removal and appending.
-/

namespace Purelib.Polynomial.Dense.Coefficients

variable {K : Type*} [Zero K]

/-- Last coefficient, with zero only for the empty list.

The original accumulator overwrites each preceding entry with its successor.
Its final retained value is the descending table's displayed constant coefficient. -/
@[expose] public def constantCoefficient : List K → K
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

/-- A singleton coefficient list has its only entry as constant coefficient. -/
@[simp] public theorem constantCoefficient_singleton (coefficient : K) :
    constantCoefficient [coefficient] = coefficient := rfl

/-- Removing a leading coefficient from a list with at least two entries preserves its constant coefficient.

The original accumulator overwrites its leading value with the next entry.
Its unchanged tail therefore retains the same final coefficient. -/
@[simp] public theorem constantCoefficient_cons_cons
    (leading next : K) (remaining : List K) :
    constantCoefficient (leading :: next :: remaining) =
      constantCoefficient (next :: remaining) := rfl

/-- Appending a final coefficient makes it the constant coefficient of the descending list.

The original last-entry accumulator consumes the appended coefficient last.
Structural recursion preserves the original preceding list and final entry. -/
public theorem constantCoefficient_append_singleton
    (coefficients : List K) (coefficient : K) :
    constantCoefficient (coefficients ++ [coefficient]) =
      coefficient := by
  induction coefficients with
  | nil => rfl
  | cons leading remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next remaining =>
          rw [List.cons_append, List.cons_append,
            constantCoefficient_cons_cons]
          exact inductionHypothesis

end Purelib.Polynomial.Dense.Coefficients
