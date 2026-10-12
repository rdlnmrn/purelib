module
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data.Rat

@[expose] public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Decide

/-- The canonical carrier's structural equality test. -/
def equal (left right : Fraction.Rational) : Bool := decide (left = right)

/-- The Boolean canonical-rational equality test returns true exactly for equal records. -/
theorem equal_eq_true_iff (left right : Fraction.Rational) :
    equal left right = true ↔ left = right := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true

/-- Decide structural equality of canonical rational records. -/
def rationalDecEq (left right : Fraction.Rational) : Decidable (left = right) :=
  inferInstance

/-- Decide weak comparison of canonical rationals by their cross-products. -/
def rationalDecLE (left right : Fraction.Rational) : Decidable (left ≤ right) :=
  inferInstance

/-- Decide strict comparison of canonical rationals by their concrete order. -/
def rationalDecLT (left right : Fraction.Rational) : Decidable (left < right) :=
  inferInstance

/-- Return the Boolean result of canonical rational weak comparison. -/
def lessEqual (left right : Fraction.Rational) : Bool := decide (left ≤ right)

/-- The Boolean weak-comparison test returns true exactly when the rational comparison holds. -/
theorem lessEqual_eq_true_iff (left right : Fraction.Rational) :
    lessEqual left right = true ↔ left ≤ right := by
  constructor
  · exact of_decide_eq_true
  · exact decide_eq_true
end Purelib.Data.Rat.Fraction.Decide

end
