module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Retained constant coefficients of descending rational tables

The original last-entry accumulator selects the displayed constant coefficient.
Its certificates preserve that same observation under prefix removal and appending.
-/

namespace Purelib.Polynomial.Dense.Rational.Coefficients

open Purelib.Data.Rat

/-- Last rational coefficient, with zero only for the empty list.

The original accumulator overwrites each preceding entry with its successor.
Its final retained value is the descending table's displayed constant coefficient. -/
@[expose] public def rationalConstantCoefficient : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | coefficient :: remaining =>
      remaining.foldl (fun _ next => next) coefficient

/-- A singleton rational coefficient list has its only entry as constant coefficient. -/
@[simp] public theorem rationalConstantCoefficient_singleton (coefficient : Fraction.Rational) :
    rationalConstantCoefficient [coefficient] = coefficient := rfl

/-- Removing a leading coefficient from a list with at least two entries preserves its constant coefficient.

The original accumulator overwrites its leading value with the next entry.
Its unchanged tail therefore retains the same final coefficient. -/
@[simp] public theorem rationalConstantCoefficient_cons_cons
    (leading next : Fraction.Rational) (remaining : List Fraction.Rational) :
    rationalConstantCoefficient (leading :: next :: remaining) =
      rationalConstantCoefficient (next :: remaining) := rfl

/-- Appending a final rational coefficient makes it the constant coefficient of the descending list.

The original last-entry accumulator consumes the appended coefficient last.
Structural recursion preserves the original preceding list and final entry. -/
public theorem rationalConstantCoefficient_append_singleton
    (coefficients : List Fraction.Rational) (coefficient : Fraction.Rational) :
    rationalConstantCoefficient (coefficients ++ [coefficient]) =
      coefficient := by
  induction coefficients with
  | nil => rfl
  | cons leading remaining inductionHypothesis =>
      cases remaining with
      | nil => rfl
      | cons next remaining =>
          rw [List.cons_append, List.cons_append,
            rationalConstantCoefficient_cons_cons]
          exact inductionHypothesis

end Purelib.Polynomial.Dense.Rational.Coefficients
