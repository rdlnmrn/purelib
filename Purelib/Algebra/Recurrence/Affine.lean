module

public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Affine recurrences and finite stability on short intervals

The recurrence consumes the original coefficient and forcing at each bounded
index. A comparison uses only its local inequalities. A finite product
estimate gives a factor of two whenever the sum of the nonnegative growth
increments is at most one half; the factor does not depend on the step count.
-/

public section

namespace Purelib.Algebra.Recurrence.Affine

open Purelib.Algebra.FiniteSum
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

universe u

/-- Execute a finite affine recurrence on the original indexed coefficients and forcing values.

The initial value is retained at count zero. Each successor reads its own
coefficient and forcing once and applies them to the preceding result.
-/
@[expose] def iterate {K : Type u} [Mul K] [Add K]
    (coefficient forcing : Nat → K) (initial : K) : Nat → K
  | 0 => initial
  | count + 1 => coefficient count * iterate coefficient forcing initial count + forcing count

/-- The recurrence at count zero is the supplied initial value. -/
theorem iterate_zero {K : Type u} [Mul K] [Add K]
    (coefficient forcing : Nat → K) (initial : K) :
    iterate coefficient forcing initial 0 = initial := rfl

/-- The successor recurrence consumes the same preceding value and the next original pair of scalars. -/
theorem iterate_succ {K : Type u} [Mul K] [Add K]
    (coefficient forcing : Nat → K) (initial : K) (count : Nat) :
    iterate coefficient forcing initial (count + 1) =
      coefficient count * iterate coefficient forcing initial count + forcing count := rfl

/-- Local affine upper bounds compare a retained finite trace with the independently executed recurrence.

Only coefficients at indices below the displayed count must be nonnegative.
The forcing may have either sign. No endpoint comparison is an input.
-/
theorem comparison (coefficient forcing values : Nat → Rational) (initial : Rational) (count : Nat)
    (start : values 0 ≤ initial)
    (nonnegative : ∀ index, index < count → 0 ≤ coefficient index)
    (steps : ∀ index, index < count →
      values (index + 1) ≤ coefficient index * values index + forcing index) :
    values count ≤ iterate coefficient forcing initial count := by
  induction count with
  | zero => exact start
  | succ count ih =>
    have prior : values count ≤ iterate coefficient forcing initial count :=
      ih (fun index before => nonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
        (fun index before => steps index (Nat.lt_trans before (Nat.lt_succ_self count)))
    exact (steps count (Nat.lt_succ_self count)).trans
      (Order.Arithmetic.add_le_add_right_direct
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct prior
          (nonnegative count (Nat.lt_succ_self count))) (forcing count))

/-- The multiplicative growth is the same affine recurrence with unit initial value and zero forcing. -/
private def amplification (rate : Nat → Rational) : Nat → Rational :=
  iterate (fun index => 1 + rate index) (fun _ => 0) 1

/-- The original amplification advances by its next nonnegative-growth multiplier. -/
private theorem amplification_succ (rate : Nat → Rational) (count : Nat) :
    amplification rate (count + 1) = (1 + rate count) * amplification rate count := by
  change (1 + rate count) * amplification rate count + 0 = _
  ring1

/-- Nonnegative rates give nonnegative total growth, amplification at least one and a finite product-complement bound.

The product-complement estimate is algebraic and needs no smallness premise.
The successor subtracts exactly the nonnegative correction involving the
new rate and the original accumulated growth.
-/
private theorem amplification_bounds (rate : Nat → Rational) (count : Nat)
    (nonnegative : ∀ index, index < count → 0 ≤ rate index) :
    0 ≤ Prefix.coordinateSum rate count ∧
      1 ≤ amplification rate count ∧
        amplification rate count * (1 - Prefix.coordinateSum rate count) ≤ 1 := by
  induction count with
  | zero =>
    change (0 : Rational) ≤ 0 ∧ (1 : Rational) ≤ 1 ∧ 1 * (1 - (0 : Rational)) ≤ 1
    refine ⟨Order.Basic.le_refl _, Order.Basic.le_refl _, ?_⟩
    rewrite [show (1 : Rational) * (1 - 0) = 1 by ring1]
    exact Order.Basic.le_refl _
  | succ count ih =>
    have prior := ih (fun index before => nonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
    have rateNonnegative := nonnegative count (Nat.lt_succ_self count)
    have productNonnegative : (0 : Rational) ≤ amplification rate count :=
      (show (0 : Rational) ≤ 1 by decide +kernel).trans prior.2.1
    have multiplier : (1 : Rational) ≤ 1 + rate count :=
      (show (1 : Rational) = 1 + 0 by ring1).trans_le
        (Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) rateNonnegative)
    have sumNonnegative : (0 : Rational) ≤ Prefix.coordinateSum rate (count + 1) :=
      (show (0 : Rational) = 0 + 0 by ring1).trans_le
        (Order.Arithmetic.add_le_add_direct prior.1 rateNonnegative)
    have productLower : (1 : Rational) ≤ amplification rate (count + 1) :=
      prior.2.1.trans
        (((Field.one_mul (amplification rate count)).symm.trans_le
          (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct multiplier productNonnegative)).trans_eq
            (amplification_succ rate count).symm)
    have correction : (0 : Rational) ≤ amplification rate count * rate count *
        (Prefix.coordinateSum rate count + rate count) :=
      Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct productNonnegative rateNonnegative)
        ((show (0 : Rational) = 0 + 0 by ring1).trans_le
          (Order.Arithmetic.add_le_add_direct prior.1 rateNonnegative))
    have decreasing : (1 + rate count) * amplification rate count *
        (1 - (Prefix.coordinateSum rate count + rate count)) ≤
          amplification rate count * (1 - Prefix.coordinateSum rate count) :=
      Order.Arithmetic.le_of_sub_nonneg_direct
        (correction.trans_eq (by ring1))
    refine ⟨sumNonnegative, productLower, ?_⟩
    rewrite [amplification_succ, Prefix.coordinateSum_succ]
    exact decreasing.trans prior.2.2

/-- A total growth budget at most one half bounds amplification by two, independently of the number of steps. -/
private theorem amplification_le_two (rate : Nat → Rational) (count : Nat)
    (nonnegative : ∀ index, index < count → 0 ≤ rate index)
    (small : Prefix.coordinateSum rate count ≤ (1 / 2 : Rational)) :
    amplification rate count ≤ 2 := by
  have retained := amplification_bounds rate count nonnegative
  have positiveProduct : (0 : Rational) ≤ amplification rate count :=
    (show (0 : Rational) ≤ 1 by decide +kernel).trans retained.2.1
  have half : (1 / 2 : Rational) ≤ 1 - Prefix.coordinateSum rate count :=
    (show (1 / 2 : Rational) = 1 - 1 / 2 by decide +kernel).trans_le
      (Order.Arithmetic.sub_le_sub_left_direct small 1)
  have paid := (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct half positiveProduct).trans retained.2.2
  have halfDouble : (1 / 2 : Rational) * 2 = 1 := by decide +kernel
  calc
    amplification rate count = (amplification rate count * (1 / 2 : Rational)) * 2 := by
      rewrite [show (amplification rate count * (1 / 2 : Rational)) * 2 =
        amplification rate count * ((1 / 2 : Rational) * 2) by ring1, halfDouble]
      exact (Field.mul_one_direct _).symm
    _ ≤ 1 * 2 := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (by decide +kernel)
    _ = 2 := by ring1

/-- The original affine recurrence is bounded by its actual amplification times initial value plus total forcing.

Each nonnegative forcing is retained at its original index. Amplification
at least one pays that same forcing when extending the accumulated sum.
-/
private theorem iterate_le_amplification (rate forcing : Nat → Rational) (initial : Rational) (count : Nat)
    (rateNonnegative : ∀ index, index < count → 0 ≤ rate index)
    (forcingNonnegative : ∀ index, index < count → 0 ≤ forcing index) :
    iterate (fun index => 1 + rate index) forcing initial count ≤
      amplification rate count * (initial + Prefix.coordinateSum forcing count) := by
  induction count with
  | zero =>
    change initial ≤ 1 * (initial + 0)
    rewrite [show (1 : Rational) * (initial + 0) = initial by ring1]
    exact Order.Basic.le_refl _
  | succ count ih =>
    have previous := ih
      (fun index before => rateNonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
      (fun index before => forcingNonnegative index (Nat.lt_trans before (Nat.lt_succ_self count)))
    have multiplierNonnegative : (0 : Rational) ≤ 1 + rate count :=
      (show (0 : Rational) = 0 + 0 by ring1).trans_le
        (Order.Arithmetic.add_le_add_direct (by decide +kernel)
          (rateNonnegative count (Nat.lt_succ_self count)))
    have forcingPaid : forcing count ≤ amplification rate (count + 1) * forcing count :=
      (Field.one_mul (forcing count)).symm.trans_le
        (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (amplification_bounds rate (count + 1) rateNonnegative).2.1
          (forcingNonnegative count (Nat.lt_succ_self count)))
    calc
      _ = (1 + rate count) * iterate (fun index => 1 + rate index) forcing initial count + forcing count := rfl
      _ ≤ (1 + rate count) * (amplification rate count *
          (initial + Prefix.coordinateSum forcing count)) + forcing count :=
        Order.Arithmetic.add_le_add_right_direct
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct previous multiplierNonnegative) _
      _ ≤ (1 + rate count) * (amplification rate count *
          (initial + Prefix.coordinateSum forcing count)) + amplification rate (count + 1) * forcing count :=
        Order.Arithmetic.add_le_add_direct (Order.Basic.le_refl _) forcingPaid
      _ = _ := by rewrite [amplification_succ, Prefix.coordinateSum_succ]; ring1

/-- A nonnegative local affine error recurrence on a short interval has a step-count-independent stability bound.

The original finite rate sum must be at most one half. The returned factor
two multiplies the supplied initial error and the actual sum of local
defects, so refining a partition does not introduce an exponential factor
depending on its number of cells. No final trace agreement is assumed.
-/
theorem short_interval_stability (rate forcing values : Nat → Rational) (initial : Rational) (count : Nat)
    (initialNonnegative : 0 ≤ initial) (start : values 0 ≤ initial)
    (rateNonnegative : ∀ index, index < count → 0 ≤ rate index)
    (forcingNonnegative : ∀ index, index < count → 0 ≤ forcing index)
    (small : Prefix.coordinateSum rate count ≤ (1 / 2 : Rational))
    (steps : ∀ index, index < count →
      values (index + 1) ≤ (1 + rate index) * values index + forcing index) :
    values count ≤ 2 * (initial + Prefix.coordinateSum forcing count) := by
  have multiplierNonnegative (index : Nat) (before : index < count) : (0 : Rational) ≤ 1 + rate index :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct (by decide +kernel) (rateNonnegative index before))
  have totalNonnegative : (0 : Rational) ≤ initial + Prefix.coordinateSum forcing count :=
    (show (0 : Rational) = 0 + 0 by ring1).trans_le
      (Order.Arithmetic.add_le_add_direct initialNonnegative
        (amplification_bounds forcing count forcingNonnegative).1)
  exact (comparison (fun index => 1 + rate index) forcing values initial count start multiplierNonnegative steps).trans
    ((iterate_le_amplification rate forcing initial count rateNonnegative forcingNonnegative).trans
      (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (amplification_le_two rate count rateNonnegative small) totalNonnegative))

end Purelib.Algebra.Recurrence.Affine

end
