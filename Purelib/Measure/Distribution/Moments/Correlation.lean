module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Root-free finite rational correlation

The ordinary correlation coefficient may require an irrational square root.
Its square does not: covariance squared divided by the product of the two
variances is exact rational data.  Under an explicitly positive variance
product it lies in the unit interval by finite Cauchy--Schwarz.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Divide squared covariance by the product of the two original variances.

This rational expression uses total division; normalization bounds and equality characterizations separately require a
positive variance product. -/
def squaredCorrelation {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.covariance left right ^ 2 /
    (distribution.variance left * distribution.variance right)

/-- Squared correlation is nonnegative for the exact pair of observables. -/
theorem squaredCorrelation_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    0 ≤ distribution.squaredCorrelation left right := by
  unfold squaredCorrelation
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (distribution.variance_nonneg left)
      (distribution.variance_nonneg right))

/-- Squared correlation is at most one when the product of the original variances is positive. -/
theorem squaredCorrelation_le_one {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    distribution.squaredCorrelation left right ≤ 1 := by
  unfold squaredCorrelation
  apply (Fraction.Order.Field.div_le_iff_pos positive).2
  simpa only [one_mul] using
    distribution.covariance_sq_le_variance_mul left right

/-- Squared correlation lies between zero and one when the original variance product is positive. -/
theorem squaredCorrelation_mem_unit {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    0 ≤ distribution.squaredCorrelation left right ∧
      distribution.squaredCorrelation left right ≤ 1 :=
  ⟨distribution.squaredCorrelation_nonnegative left right,
    distribution.squaredCorrelation_le_one left right positive⟩

/-- Squared correlation is unchanged by exchanging the two exact observables. -/
theorem squaredCorrelation_symm {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.squaredCorrelation left right =
      distribution.squaredCorrelation right left := by
  unfold squaredCorrelation
  rw [distribution.covariance_symm left right]
  congr 1
  ring1

/-- An observable with positive variance has squared correlation one with itself. -/
theorem squaredCorrelation_self {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (positive : 0 < distribution.variance value) :
    distribution.squaredCorrelation value value = 1 := by
  unfold squaredCorrelation
  rw [distribution.covariance_self]
  let denominator := distribution.variance value *
    distribution.variance value
  have denominatorPositive : 0 < denominator :=
    Fraction.Order.Arithmetic.mul_pos_direct positive positive
  apply Fraction.Field.mul_right_cancel_of_ne denominatorPositive.ne'
  calc
    (distribution.variance value ^ 2 / denominator) * denominator =
        distribution.variance value ^ 2 :=
      Fraction.Field.div_mul_cancel_of_ne
        (distribution.variance value ^ 2) denominator denominatorPositive.ne'
    _ = denominator := by
      dsimp only [denominator]
      ring1
    _ = 1 * denominator := by ring1

/-- For a positive variance product, squared correlation is zero exactly when covariance is zero. -/
theorem squaredCorrelation_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    distribution.squaredCorrelation left right = 0 ↔
      distribution.covariance left right = 0 := by
  let denominator := distribution.variance left * distribution.variance right
  constructor
  · intro correlationZero
    have multiplied := congrArg (fun value => value * denominator)
      correlationZero
    unfold squaredCorrelation at multiplied
    dsimp only [denominator] at multiplied
    have squareZero : distribution.covariance left right ^ 2 = 0 := by
      calc
        distribution.covariance left right ^ 2 =
            (distribution.covariance left right ^ 2 /
              (distribution.variance left * distribution.variance right)) *
                (distribution.variance left * distribution.variance right) :=
          (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne').symm
        _ = 0 * (distribution.variance left *
              distribution.variance right) := multiplied
        _ = 0 := by ring1
    exact Fraction.Order.Arithmetic.sq_eq_zero_direct _ |>.mp squareZero
  · intro covarianceZero
    unfold squaredCorrelation
    rw [covarianceZero]
    exact Fraction.Field.zero_div_direct _

/-- For a positive variance product, squared correlation is one exactly when squared covariance equals that product. -/
theorem squaredCorrelation_eq_one_iff {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    distribution.squaredCorrelation left right = 1 ↔
      distribution.covariance left right ^ 2 =
        distribution.variance left * distribution.variance right := by
  let denominator := distribution.variance left * distribution.variance right
  constructor
  · intro correlationOne
    have multiplied := congrArg (fun value => value * denominator)
      correlationOne
    unfold squaredCorrelation at multiplied
    dsimp only [denominator] at multiplied
    calc
      distribution.covariance left right ^ 2 =
          (distribution.covariance left right ^ 2 /
            (distribution.variance left * distribution.variance right)) *
              (distribution.variance left * distribution.variance right) :=
        (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne').symm
      _ = 1 * (distribution.variance left *
            distribution.variance right) := multiplied
      _ = distribution.variance left * distribution.variance right := by ring1
  · intro equality
    unfold squaredCorrelation
    apply Fraction.Field.mul_right_cancel_of_ne positive.ne'
    calc
      (distribution.covariance left right ^ 2 /
            (distribution.variance left * distribution.variance right)) *
          (distribution.variance left * distribution.variance right) =
        distribution.covariance left right ^ 2 :=
          Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'
      _ = distribution.variance left * distribution.variance right := equality
      _ = 1 * (distribution.variance left *
          distribution.variance right) := by ring1

end Distribution

end Purelib.Measure
