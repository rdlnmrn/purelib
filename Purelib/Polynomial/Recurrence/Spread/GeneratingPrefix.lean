module
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Algebra.FiniteSum.Prefix

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Polynomial

@[expose] public section

/-!
# Divine Proportions, Chapter 8: finite generating prefixes

Exercise 8.10 presents an infinite generating series.  The finite constructive
content is stronger computationally: for every requested cutoff we evaluate
exactly that prefix and exhibit its complete three-term boundary remainder.
The source's rational expression is recovered coefficient-by-coefficient as
the remainder moves strictly beyond the requested prefix; no infinite series
or completed power-series object is introduced.
-/

namespace Purelib.Polynomial.Recurrence.Spread.GeneratingPrefix

open Purelib.Algebra

/-- The first `count` positive-index spread-polynomial terms, evaluated at a
requested finite indeterminate value `variable`. -/
def spreadGeneratingPrefix
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) : R :=
  FiniteSum.Prefix.prefixSum count (fun index =>
    Recurrence.Spread.Basic.spreadPolynomial (index + 1) value * indeterminate ^ (index + 1))

/-- The generating prefix with no terms is zero. -/
@[simp] theorem spreadGeneratingPrefix_zero
    {R : Type*} [CommRing R] (value indeterminate : R) :
    Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix 0 value indeterminate = 0 := rfl

/-- Extending a generating prefix appends its next weighted spread polynomial. -/
theorem spreadGeneratingPrefix_succ
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) :
    Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix (count + 1) value indeterminate =
      Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix count value indeterminate +
        Recurrence.Spread.Basic.spreadPolynomial (count + 1) value *
          indeterminate ^ (count + 1) := by
  unfold Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix
  rw [FiniteSum.Prefix.prefixSum_succ_last]

/-- The cubic multiplier for the finite spread generating-prefix identity.

It is the sum of the cubed linear factor and the spread-dependent correction term. -/
def spreadGeneratingDenominator
    {R : Type*} [CommRing R] (value indeterminate : R) : R :=
  (1 - indeterminate) ^ 3 +
    4 * value * indeterminate * (1 - indeterminate)

/-- An exact generating identity with three finite boundary terms.

Multiplying the requested prefix by its cubic denominator leaves the displayed numerator and the complete three-term
remainder beyond the cutoff. -/
theorem exercise_8_10
    {R : Type*} [CommRing R]
    (count : Nat) (value indeterminate : R) :
    Recurrence.Spread.GeneratingPrefix.spreadGeneratingDenominator value indeterminate *
        Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix count value indeterminate =
      value * indeterminate * (1 + indeterminate) -
        Recurrence.Spread.Basic.spreadPolynomial (count + 1) value *
          indeterminate ^ (count + 1) +
        (Recurrence.Spread.Basic.spreadPolynomial count value +
            Recurrence.Spread.Basic.spreadPolynomial (count + 1) value - 2 * value) *
          indeterminate ^ (count + 2) -
        Recurrence.Spread.Basic.spreadPolynomial count value * indeterminate ^ (count + 3) := by
  induction count with
  | zero =>
      simp only [Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix_zero,
        Recurrence.Spread.Basic.spreadPolynomial_zero,
        Recurrence.Spread.Basic.spreadPolynomial_one, zero_mul, mul_zero, zero_add,
        pow_one, -eq_self, -iff_self]
      ring1
  | succ count inductionHypothesis =>
      rw [Recurrence.Spread.GeneratingPrefix.spreadGeneratingPrefix_succ, mul_add,
        inductionHypothesis]
      rw [show count + 1 + 1 = count + 2 by omega0,
        show count + 1 + 2 = count + 3 by omega0,
        show count + 1 + 3 = count + 4 by omega0]
      rw [Recurrence.Spread.Basic.spreadPolynomial_succ_succ]
      rw [show indeterminate ^ (count + 2) =
          indeterminate ^ (count + 1) * indeterminate by rw [pow_succ],
        show indeterminate ^ (count + 3) =
          indeterminate ^ (count + 1) * indeterminate ^ 2 by
            rw [show count + 3 = count + 1 + 2 by omega0, pow_add],
        show indeterminate ^ (count + 4) =
          indeterminate ^ (count + 1) * indeterminate ^ 3 by
            rw [show count + 4 = count + 1 + 3 by omega0, pow_add]]
      unfold Recurrence.Spread.GeneratingPrefix.spreadGeneratingDenominator
      ring1

end Purelib.Polynomial.Recurrence.Spread.GeneratingPrefix
