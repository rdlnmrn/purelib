module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the finite Chebyshev identity

Only the polynomial recurrence in Exercise 8.4 is retained.  The source's
alternative notation using a square root in a completed decimal field is not
needed for, and adds no content to, this exact identity.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.Basic

variable {K : Type*} [ExplicitField K]

/-- The Chebyshev polynomial of the first kind, as a primitive-recursive
finite field expression. -/
def chebyshevFirst : Nat → K → K
  | 0, _ => 1
  | 1, value => value
  | index + 2, value =>
      2 * value * chebyshevFirst (index + 1) value -
        chebyshevFirst index value

open Purelib.Polynomial
/-- The index-zero first-kind Chebyshev value is one. -/
@[simp] theorem chebyshevFirst_zero (value : K) :
    chebyshevFirst 0 value = 1 := rfl

/-- The index-one first-kind Chebyshev value is the argument. -/
@[simp] theorem chebyshevFirst_one (value : K) :
    chebyshevFirst 1 value = value := rfl

/-- Twice the argument times the previous Chebyshev value minus its predecessor. -/
@[simp] theorem chebyshevFirst_succ_succ (index : Nat) (value
  : K) :
    chebyshevFirst (index + 2) value =
      2 * value * chebyshevFirst (index + 1) value -
        chebyshevFirst index value := rfl

/-- Product-to-sum in subtraction-free natural coordinates:
`2T_(a+b)T_b = T_(a+2b)+T_a`. -/
theorem chebyshevFirst_product_add_sub :
    ∀ offset step : Nat, ∀ value : K,
      2 * chebyshevFirst (offset + step) value *
          chebyshevFirst step value =
        chebyshevFirst (offset + step + step) value +
          chebyshevFirst offset value
  | offset, 0, value => by
      simp only [Nat.add_zero, chebyshevFirst_zero]
      ring1
  | offset, 1, value => by
      rw [show offset + 1 + 1 = offset + 2 by omega0,
        chebyshevFirst_succ_succ, chebyshevFirst_one]
      ring1
  | offset, step + 2, value => by
      have previous := chebyshevFirst_product_add_sub
        (offset + 1) (step + 1) value
      have beforePrevious := chebyshevFirst_product_add_sub
        (offset + 2) step value
      rw [show offset + 1 + (step + 1) =
          offset + step + 2 by omega0] at previous
      rw [show offset + 2 + step =
          offset + step + 2 by omega0] at beforePrevious
      have upperRecurrence :
          2 * value *
                chebyshevFirst
                  (offset + step + 2 + (step + 1)) value -
              chebyshevFirst (offset + step + 2 + step) value =
            chebyshevFirst
              (offset + (step + 2) + (step + 2)) value := by
        rw [show offset + step + 2 + (step + 1) =
            (offset + step + 2 + step) + 1 by omega0,
          ← chebyshevFirst_succ_succ]
        congr 1
      have lowerRecurrence :
          2 * value * chebyshevFirst (offset + 1) value -
              chebyshevFirst (offset + 2) value =
            chebyshevFirst offset value := by
        rw [chebyshevFirst_succ_succ]
        ring1
      rw [show offset + (step + 2) = offset + step + 2 by omega0]
      rw [chebyshevFirst_succ_succ]
      calc
        2 * chebyshevFirst (offset + step + 2) value *
            (2 * value * chebyshevFirst (step + 1) value -
              chebyshevFirst step value) =
          2 * value *
              (2 * chebyshevFirst (offset + step + 2) value *
                chebyshevFirst (step + 1) value) -
            (2 * chebyshevFirst (offset + step + 2) value *
              chebyshevFirst step value) := by ring1
        _ = 2 * value *
              (chebyshevFirst (offset + step + 2 + (step + 1)) value +
                chebyshevFirst (offset + 1) value) -
            (chebyshevFirst (offset + step + 2 + step) value +
              chebyshevFirst (offset + 2) value) := by
                rw [previous, beforePrevious]
        _ = chebyshevFirst (offset + (step + 2) + (step + 2)) value +
              chebyshevFirst offset value := by
                rw [show 2 * value *
                      (chebyshevFirst
                          (offset + step + 2 + (step + 1)) value +
                        chebyshevFirst (offset + 1) value) -
                      (chebyshevFirst
                          (offset + step + 2 + step) value +
                        chebyshevFirst (offset + 2) value) =
                    (2 * value * chebyshevFirst
                        (offset + step + 2 + (step + 1)) value -
                      chebyshevFirst (offset + step + 2 + step) value) +
                    (2 * value * chebyshevFirst (offset + 1) value -
                      chebyshevFirst (offset + 2) value) by ring1]
                rw [upperRecurrence, lowerRecurrence]
end Purelib.Polynomial.Recurrence.Chebyshev.First.Basic

end
