module
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Finite convergence certificates

The usual monotone, Fatou, and dominated convergence theorems concern
completed limits.  This module retains their executable finite content:
displayed monotone chains have monotone rational integrals, displayed lower
envelopes satisfy the finite Fatou inequality, and an integrable rational
error envelope gives an explicit accuracy certificate.

No sequence, limit, supremum, extended value, or completed function space is
formed.
-/

namespace Purelib.Data.Rat

/-- Require each adjacent pair of a displayed rational list to be weakly increasing.

Empty and singleton lists satisfy the predicate. Longer lists retain the first weak
comparison and the same condition on the original tail. -/
def MonotoneCoordinateChain : List Rational → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      first ≤ second ∧ MonotoneCoordinateChain (second :: remaining)

namespace Content
end Content
namespace Content
end Content
namespace Content
namespace IntegralErrorBudget
end IntegralErrorBudget
namespace MonotoneIntegralBudget
end MonotoneIntegralBudget

end Content

end Purelib.Data.Rat

namespace Purelib.Data.List.Rat

open Purelib.Data.Rat.Fraction

/-- Compute the largest retained rational input together with a supplied floor.

Structural recursion examines exactly the finite list. The empty list
returns its supplied floor, so no element or global bound is chosen.
-/
def maximum (floor : Rational) : List Rational → Rational
  | [] => floor
  | value :: remaining => max value (maximum floor remaining)

/-- The supplied floor is bounded by the maximum of every finite input list. -/
theorem floor_le_maximum (floor : Rational) (values : List Rational) : floor ≤ maximum floor values := by
  induction values with
  | nil => exact Order.Basic.le_refl floor
  | cons value remaining induction =>
      exact Order.Basic.le_trans _ _ _ induction
        (Order.Basic.le_max_right value (maximum floor remaining))

/-- Every actual rational list member is bounded by its retained finite maximum. -/
theorem le_maximum_of_mem (floor : Rational) {values : List Rational} {value : Rational}
    (member : value ∈ values) : value ≤ maximum floor values := by
  induction values with
  | nil => nomatch member
  | cons head remaining induction =>
      cases member with
      | head => exact Order.Basic.le_max_left value (maximum floor remaining)
      | tail _ tail =>
          exact Order.Basic.le_trans _ _ _ (induction tail)
            (Order.Basic.le_max_right head (maximum floor remaining))

/-- A nonnegative supplied floor makes the computed finite maximum nonnegative. -/
theorem maximum_nonneg {floor : Rational} (nonnegative : 0 ≤ floor) (values : List Rational) :
    0 ≤ maximum floor values :=
  Order.Basic.le_trans _ _ _ nonnegative (floor_le_maximum floor values)

end Purelib.Data.List.Rat

end
