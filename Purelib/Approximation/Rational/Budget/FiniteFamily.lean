module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

section
/-!
# Simultaneous finite event-frequency sampling

One explicit finite iid sample can estimate every event probability in a
displayed finite event list.  The requested failure budget is split over
`events.length + 1`, each event uses the uniform Bernoulli variance bound, and
finite subadditivity controls the union of all deviation events.

This is the finite constructive core of a uniform empirical-frequency bound;
there is no infinite event class, supremum, or asymptotic empirical process.
-/

@[expose] public section

namespace Purelib.Approximation.Rational.Budget

section Distribution

/-- Positive rational failure share assigned to each event in a displayed finite family. -/
def eventFamilyFailureShare {α : Type}
    (events : List (α → Bool)) (failure : Fraction.Rational) : Fraction.Rational :=
  failure / (Nat.succ events.length : Fraction.Rational)

/-- A positive failure budget gives each event in the displayed finite family a positive share. -/
theorem eventFamilyFailureShare_positive {α : Type}
    (events : List (α → Bool)) {failure : Fraction.Rational}
    (failurePositive : 0 < failure) :
    0 < eventFamilyFailureShare events failure :=
  Fraction.Order.Field.div_pos_direct failurePositive
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _))

/-- The event count times its common failure share is strictly below the positive total failure budget. -/
theorem length_mul_eventFamilyFailureShare_lt {α : Type}
    (events : List (α → Bool)) {failure : Fraction.Rational}
    (failurePositive : 0 < failure) :
    (events.length : Fraction.Rational) * eventFamilyFailureShare events failure <
      failure := by
  have denominatorPositive :
      0 < (Nat.succ events.length : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _)
  have castLess : (events.length : Fraction.Rational) <
      (Nat.succ events.length : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct (Nat.lt_succ_self _)
  have scaledLess : failure * (events.length : Fraction.Rational) <
      failure * (Nat.succ events.length : Fraction.Rational) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      failurePositive castLess
  calc
    (events.length : Fraction.Rational) * eventFamilyFailureShare events failure =
        (failure * (events.length : Fraction.Rational)) /
          (Nat.succ events.length : Fraction.Rational) := by
      unfold eventFamilyFailureShare
      calc
        (events.length : Fraction.Rational) *
            (failure / (Nat.succ events.length : Fraction.Rational)) =
          (events.length : Fraction.Rational) *
            (failure * (Nat.succ events.length : Fraction.Rational)⁻¹) := by
          rw [Fraction.Field.div_eq_mul_inv_direct]
        _ = ((events.length : Fraction.Rational) * failure) *
            (Nat.succ events.length : Fraction.Rational)⁻¹ :=
          (Fraction.Field.mul_assoc
            (events.length : Fraction.Rational) failure
            (Nat.succ events.length : Fraction.Rational)⁻¹).symm
        _ = (failure * (events.length : Fraction.Rational)) *
            (Nat.succ events.length : Fraction.Rational)⁻¹ := by
          rw [Fraction.Field.mul_comm
            (events.length : Fraction.Rational) failure]
        _ = (failure * (events.length : Fraction.Rational)) /
            (Nat.succ events.length : Fraction.Rational) := by
          rw [Fraction.Field.div_eq_mul_inv_direct]
    _ < failure :=
      (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
        scaledLess
end Distribution

end Purelib.Approximation.Rational.Budget

end
