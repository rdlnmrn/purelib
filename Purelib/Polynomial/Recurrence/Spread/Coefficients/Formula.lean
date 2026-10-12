module
public import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Array

import Purelib.Algebra.NatCast
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: the spread coefficient array

Exercise 8.9 writes every spread polynomial as a finite binomial-coefficient
sum.  Its displayed coefficient contains a quotient.  We first identify it
with the integral entry obtained by adding two shifted copies of Pascal's
triangle.  This gives a division-free theorem over every commutative ring;
the source's quotient notation is recovered only when its finitely many
denominators are supplied as nonzero.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Formula

/-- The division-free finite sum in Exercise 8.9, ordered by increasing
power of `-4s`. -/
def spreadCoefficientExpansion
    {R : Type*} [CommRing R] (row : Nat) (value : R) : R :=
  FiniteSum.Prefix.prefixSum row (fun index =>
    (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (index + 1) : R) * value *
      (-4 * value) ^ index)

/-- The empty spread-coefficient expansion is zero. -/
@[simp] theorem spreadCoefficientExpansion_zero
    {R : Type*} [CommRing R] (value : R) :
    spreadCoefficientExpansion 0 value = 0 := rfl

/-- The first spread-coefficient expansion equals its argument. -/
@[simp] theorem spreadCoefficientExpansion_one
    {R : Type*} [CommRing R] (value : R) :
    spreadCoefficientExpansion 1 value = value := by
  unfold spreadCoefficientExpansion
  rw [FiniteSum.Prefix.prefixSum_succ, FiniteSum.Prefix.prefixSum_zero, add_zero]
  change ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient 1 1 : Nat) : R) * value *
    (-4 * value) ^ 0 = value
  have coefficient : Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient 1 1 = 1 := rfl
  rw [coefficient, Nat.cast_one, one_mul, pow_zero, mul_one]

/-- The spread-array sum obeys the same second-order recurrence as the
spread polynomials. -/
theorem spreadCoefficientExpansion_recurrence
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    spreadCoefficientExpansion (row + 2) value =
      2 * (1 - 2 * value) *
          spreadCoefficientExpansion (row + 1) value -
        spreadCoefficientExpansion row value + 2 * value := by
  let term : Nat → Nat → R := fun current index =>
    (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient current (index + 1) : R) * value *
      (-4 * value) ^ index
  let shifted : Nat → R := fun index =>
    match index with
    | 0 => 2 * value
    | previous + 1 => (-4 * value) * term (row + 1) previous
  have pointwise : ∀ index : Nat,
      term (row + 2) index + term row index =
        2 * term (row + 1) index + shifted index := by
    intro index
    have coefficientRecurrence :=
      Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_recurrence row index
    have castRecurrence := congrArg
      (fun coefficient : Nat => (coefficient : R)) coefficientRecurrence
    simp only [NatCast.add, NatCast.mul, Nat.cast_ofNat] at castRecurrence
    cases index with
    | zero =>
        simp only [term, shifted, pow_zero]
        calc
          (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 2) (0 + 1) : R) * value * 1 +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (0 + 1) : R) * value * 1 =
              ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 2) (0 + 1) : R) +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (0 + 1) : R)) * value := by
            ring1
          _ = (2 * (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1) (0 + 1) : R) +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1) 0 : R)) * value := by
            rw [castRecurrence]
          _ = 2 *
                ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1) (0 + 1) : R) *
                  value * 1) +
              2 * value := by
            rw [Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_zero]
            simp only [Nat.cast_ofNat]
            ring1
    | succ previous =>
        simp only [term, shifted, pow_succ]
        calc
          (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 2) (previous + 1 + 1) : R) *
                  value * ((-4 * value) ^ previous * (-4 * value)) +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (previous + 1 + 1) : R) *
                  value * ((-4 * value) ^ previous * (-4 * value)) =
              ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 2)
                    (previous + 1 + 1) : R) +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row
                    (previous + 1 + 1) : R)) *
                  value * ((-4 * value) ^ previous * (-4 * value)) := by
            ring1
          _ = (2 * (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1)
                    (previous + 1 + 1) : R) +
                (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1)
                    (previous + 1) : R)) *
                  value * ((-4 * value) ^ previous * (-4 * value)) := by
            rw [castRecurrence]
          _ = 2 *
                ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1)
                    (previous + 1 + 1) : R) * value *
                      ((-4 * value) ^ previous * (-4 * value))) +
              (-4 * value) *
                ((Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient (row + 1)
                    (previous + 1) : R) * value *
                      (-4 * value) ^ previous) := by
            ring1
  have previousPadding :
      FiniteSum.Prefix.prefixSum (row + 2) (term row) =
        FiniteSum.Prefix.prefixSum row (term row) := by
    rw [show row + 2 = (row + 1) + 1 by omega0,
      FiniteSum.Prefix.prefixSum_succ_last,
      FiniteSum.Prefix.prefixSum_succ_last]
    dsimp only [term]
    rw [Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_eq_zero_of_lt (by omega0 : row < row + 1),
      Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_eq_zero_of_lt (by omega0 : row < row + 2)]
    simp only [Nat.cast_zero, zero_mul, add_zero, -eq_self, -iff_self]
    rfl
  have currentPadding :
      FiniteSum.Prefix.prefixSum (row + 2) (term (row + 1)) =
        FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)) := by
    rw [show row + 2 = (row + 1) + 1 by omega0,
      FiniteSum.Prefix.prefixSum_succ_last]
    dsimp only [term]
    rw [Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient_eq_zero_of_lt
      (by omega0 : row + 1 < row + 2)]
    simp only [Nat.cast_zero, zero_mul, add_zero, -eq_self, -iff_self]
    rfl
  have shiftedSum :
      FiniteSum.Prefix.prefixSum (row + 2) shifted =
        2 * value +
          (-4 * value) *
            FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)) := by
    change
      2 * value +
          FiniteSum.Prefix.prefixSum (row + 1)
            (fun index => (-4 * value) * term (row + 1) index) = _
    rw [FiniteSum.Prefix.prefixSum_mul_left]
  have sumEquation :
      FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) +
          FiniteSum.Prefix.prefixSum (row + 2) (term row) =
        2 * FiniteSum.Prefix.prefixSum (row + 2) (term (row + 1)) +
          FiniteSum.Prefix.prefixSum (row + 2) shifted := by
    calc
      FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) +
            FiniteSum.Prefix.prefixSum (row + 2) (term row) =
          FiniteSum.Prefix.prefixSum (row + 2)
            (fun index => term (row + 2) index + term row index) :=
        (FiniteSum.Prefix.prefixSum_add _ _ _).symm
      _ = FiniteSum.Prefix.prefixSum (row + 2)
            (fun index =>
              2 * term (row + 1) index + shifted index) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro index indexBound
          exact pointwise index
      _ = FiniteSum.Prefix.prefixSum (row + 2)
              (fun index => 2 * term (row + 1) index) +
            FiniteSum.Prefix.prefixSum (row + 2) shifted :=
        FiniteSum.Prefix.prefixSum_add _ _ _
      _ = 2 * FiniteSum.Prefix.prefixSum (row + 2) (term (row + 1)) +
            FiniteSum.Prefix.prefixSum (row + 2) shifted := by
        rw [FiniteSum.Prefix.prefixSum_mul_left]
  unfold spreadCoefficientExpansion
  change
    FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) = _
  rw [previousPadding, currentPadding, shiftedSum] at sumEquation
  change
    FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) =
      2 * (1 - 2 * value) *
          FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)) -
        FiniteSum.Prefix.prefixSum row (term row) + 2 * value
  calc
    FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) =
        (FiniteSum.Prefix.prefixSum (row + 2) (term (row + 2)) +
            FiniteSum.Prefix.prefixSum row (term row)) -
          FiniteSum.Prefix.prefixSum row (term row) := by ring1
    _ = (2 * FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)) +
          (2 * value +
            (-4 * value) *
              FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)))) -
        FiniteSum.Prefix.prefixSum row (term row) := by rw [sumEquation]
    _ = 2 * (1 - 2 * value) *
          FiniteSum.Prefix.prefixSum (row + 1) (term (row + 1)) -
        FiniteSum.Prefix.prefixSum row (term row) + 2 * value := by ring1

/-- The finite integer coefficient expansion evaluates to the spread polynomial.

Each coefficient is cast into the supplied commutative ring; the equality holds at every natural index without dividing
by a field element. -/
theorem exercise_8_9_integer_coefficients
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    Recurrence.Spread.Basic.spreadPolynomial row value =
      spreadCoefficientExpansion row value := by
  let agreesAt := fun current : Nat =>
    Recurrence.Spread.Basic.spreadPolynomial current value =
      spreadCoefficientExpansion current value
  have allPairs : ∀ current : Nat,
      agreesAt current ∧ agreesAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · rfl
        · unfold agreesAt
          simp only [Nat.zero_add, Recurrence.Spread.Basic.spreadPolynomial_one,
            spreadCoefficientExpansion_one,
            -eq_self, -iff_self]
          rfl
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold agreesAt
          rw [show Nat.succ current + 1 = current + 2 by omega0,
            Recurrence.Spread.Basic.spreadPolynomial_succ_succ,
            spreadCoefficientExpansion_recurrence,
            inductionHypothesis.1, inductionHypothesis.2]
  exact (allPairs row).1
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Formula

end
