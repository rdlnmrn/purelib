module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Nat.Bounds.Linear
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Values
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

namespace Purelib.Geometry

variable {K : Type*} [ExplicitField K]

end Purelib.Geometry

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Polynomial.Recurrence.Spread.Roots.Seven

open _root_.Purelib.Geometry
/-- The cubic factor for seven is coprime, by five explicit Bezout
identities, to every additional factor occurring in `S₁,...,S₆`. -/
public theorem
  spreadPolynomial_nonzero_before_seven
  [Nontrivial K]
    (value : K) (valueNonzero : value ≠ 0)
    (cubicZero :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0)
    (twoNonzero : (2 : K) ≠ 0) (index : Nat)
    (indexPositive : 1 ≤ index) (indexBelowSeven : index < 7) :
    Recurrence.Spread.Basic.spreadPolynomial index value ≠ 0 := by
  let cubic :=
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3
  have cubicIsZero : cubic = 0 := cubicZero
  have oneMinusValueNonzero : (1 : K) - value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -cubic +
          (8 - 48 * value + 64 * value ^ 2) * (1 - value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have threeMinusFourValueNonzero : (3 : K) - 4 * value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = cubic +
          (-2 + 16 * value - 16 * value ^ 2) * (3 - 4 * value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have oneMinusTwoValueNonzero : (1 : K) - 2 * value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -cubic +
          (8 - 40 * value + 32 * value ^ 2) * (1 - 2 * value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have fiveFactorNonzero :
      (5 : K) - 20 * value + 16 * value ^ 2 ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = (-2 + 4 * value) * cubic +
          (3 - 16 * value + 16 * value ^ 2) *
            (5 - 20 * value + 16 * value ^ 2) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have sixFactorNonzero :
      (3 : K) - 16 * value + 16 * value ^ 2 ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = (-2 + 4 * value) * cubic +
          (5 - 20 * value + 16 * value ^ 2) *
            (3 - 16 * value + 16 * value ^ 2) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    have sixteenAsProduct : (16 : K) = 4 * 4 := by ring1
    rw [sixteenAsProduct]
    exact ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have spreadOneNonzero : Recurrence.Spread.Basic.spreadPolynomial 1 value ≠ 0 := by
    rw [Recurrence.Spread.Basic.spreadPolynomial_one]
    exact valueNonzero
  have spreadTwoNonzero : Recurrence.Spread.Basic.spreadPolynomial 2 value ≠ 0 := by
    rw [Purelib.Polynomial.Recurrence.Spread.Values.spreadPolynomial_two_formula]
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero fourNonzero valueNonzero)
      oneMinusValueNonzero
  have spreadThreeNonzero : Recurrence.Spread.Basic.spreadPolynomial 3 value ≠ 0 := by
    rw [Recurrence.Spread.Values.spreadPolynomial_three]
    exact ExplicitField.mul_ne_zero valueNonzero
      (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero threeMinusFourValueNonzero)
  have spreadFourNonzero : Recurrence.Spread.Basic.spreadPolynomial 4 value ≠ 0 := by
    rw [Purelib.Polynomial.Recurrence.Spread.Values.spreadPolynomial_four_formula]
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero sixteenNonzero valueNonzero)
        oneMinusValueNonzero)
      (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero oneMinusTwoValueNonzero)
  have spreadFiveNonzero : Recurrence.Spread.Basic.spreadPolynomial 5 value ≠ 0 := by
    rw [Recurrence.Spread.Values.spreadPolynomial_five_formula]
    exact ExplicitField.mul_ne_zero valueNonzero
      (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero fiveFactorNonzero)
  have spreadSixNonzero : Recurrence.Spread.Basic.spreadPolynomial 6 value ≠ 0 := by
    rw [Purelib.Polynomial.Recurrence.Spread.Values.spreadPolynomial_six_formula]
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero fourNonzero valueNonzero)
        oneMinusValueNonzero)
      (Purelib.Algebra.Field.ExplicitField.square_nonzero_of_nonzero sixFactorNonzero)
  have possibilities :
      index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 :=
    Purelib.Data.Nat.Bounds.Linear.eq_one_through_six_of_bounds index indexPositive indexBelowSeven
  rcases possibilities with first | second | third | fourth | fifth | sixth
  · subst index
    exact spreadOneNonzero
  · subst index
    exact spreadTwoNonzero
  · subst index
    exact spreadThreeNonzero
  · subst index
    exact spreadFourNonzero
  · subst index
    exact spreadFiveNonzero
  · subst index
    exact spreadSixNonzero
end Purelib.Polynomial.Recurrence.Spread.Roots.Seven
end

namespace Purelib.Geometry

variable {K : Type*} [ExplicitField K]

end Purelib.Geometry

end
