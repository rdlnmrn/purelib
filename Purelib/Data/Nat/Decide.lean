module

import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Remainder

/-!
# Boolean tests on natural numbers

Equality and strict-order tests use the original natural decision procedures.
The divisibility test checks the remainder from ordinary total natural division;
its certificate retains the quotient as the factor when that remainder is zero.
-/

namespace Purelib.Data.Nat.Decide

/-- Test equality of two natural numbers. -/
@[expose] public def natEquals (left right : Nat) : Bool := decide (left = right)

/-- The natural equality test returns true exactly when its inputs are equal. -/
public theorem natEquals_eq_true (left right : Nat) :
    natEquals left right = true ↔ left = right :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- Test strict order between two natural numbers. -/
@[expose] public def natLess (left right : Nat) : Bool := decide (left < right)

/-- The natural strict-order test returns true exactly when the first input is smaller. -/
public theorem natLess_eq_true (left right : Nat) :
    natLess left right = true ↔ left < right :=
  ⟨of_decide_eq_true, decide_eq_true⟩

/-- Test divisibility of a natural number by its exact remainder.

The original total remainder operation handles every displayed divisor. A zero
divisor passes exactly for a zero dividend; a positive divisor passes exactly
when ordinary division leaves no remainder. -/
@[expose] public def divisibilityTest (divisor number : Nat) : Bool :=
  decide (number % divisor = 0)

/-- The divisibility test returns true exactly when the divisor divides the number.

A zero remainder retains the ordinary quotient as a natural multiplication
witness. Conversely, a supplied multiplication witness certifies a zero remainder
by the direct remainder identity, including the zero-divisor case. -/
public theorem divisibilityTest_eq_true (divisor number : Nat) :
    divisibilityTest divisor number = true ↔ divisor ∣ number := by
  constructor
  · intro accepted
    have zeroRemainder : number % divisor = 0 := of_decide_eq_true accepted
    refine ⟨number / divisor, ?_⟩
    have reconstruct := Division.mod_add_div number divisor
    rewrite [zeroRemainder, Nat.zero_add] at reconstruct
    exact reconstruct.symm
  · rintro ⟨factor, equation⟩
    apply decide_eq_true
    have multipleRemainder := Remainder.mul_add_mod divisor factor 0
    rewrite [Nat.add_zero] at multipleRemainder
    change (divisor * factor) % divisor = 0 at multipleRemainder
    rewrite [equation]
    exact multipleRemainder

/-- Decide natural divisibility by the original remainder equality procedure.

The original natural equality decision is transported by the retained Boolean
certificate. The complete decision record keeps the same remainder algorithm
and constructor branch, with direct proofs of divisibility or its failure. -/
public instance (priority := 1001) decidableDivisibility
    (divisor number : Nat) : Decidable (divisor ∣ number) :=
  decidable_of_decidable_of_iff (p := number % divisor = 0)
    ⟨fun vanishes => (divisibilityTest_eq_true divisor number).mp
        (decide_eq_true vanishes),
      fun retained => of_decide_eq_true
        ((divisibilityTest_eq_true divisor number).mpr retained)⟩

end Purelib.Data.Nat.Decide
