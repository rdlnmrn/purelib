import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Moments

/-!
# Root-free finite rational correlation

The ordinary correlation coefficient may require an irrational square root.
Its square does not: covariance squared divided by the product of the two
variances is exact rational data.  Under an explicitly positive variance
product it lies in the unit interval by finite Cauchy--Schwarz.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact squared correlation of two finite rational observables.  The
positive-variance hypotheses needed for its statistical interpretation are
kept on the theorems rather than hidden in the executable quotient. -/
def squaredCorrelation {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) : Coordinate :=
  distribution.covariance left right ^ 2 /
    (distribution.variance left * distribution.variance right)

theorem squaredCorrelation_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    0 ≤ distribution.squaredCorrelation left right := by
  unfold squaredCorrelation
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (distribution.variance_nonneg left)
      (distribution.variance_nonneg right))

/-- Root-free correlation bound. -/
theorem squaredCorrelation_le_one {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    distribution.squaredCorrelation left right ≤ 1 := by
  unfold squaredCorrelation
  apply (RFAP.ConstructiveFraction.div_le_iff_pos positive).2
  simpa only [one_mul] using
    distribution.covariance_sq_le_variance_mul left right

theorem squaredCorrelation_mem_unit {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (positive :
      0 < distribution.variance left * distribution.variance right) :
    0 ≤ distribution.squaredCorrelation left right ∧
      distribution.squaredCorrelation left right ≤ 1 :=
  ⟨distribution.squaredCorrelation_nonnegative left right,
    distribution.squaredCorrelation_le_one left right positive⟩

/-- Squared correlation is symmetric. -/
theorem squaredCorrelation_symm {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.squaredCorrelation left right =
      distribution.squaredCorrelation right left := by
  unfold squaredCorrelation
  rw [distribution.covariance_symm left right]
  congr 1
  ring1

/-- Every positive-variance observable has squared self-correlation one. -/
theorem squaredCorrelation_self {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (positive : 0 < distribution.variance value) :
    distribution.squaredCorrelation value value = 1 := by
  unfold squaredCorrelation
  rw [distribution.covariance_self]
  let denominator := distribution.variance value *
    distribution.variance value
  have denominatorPositive : 0 < denominator :=
    RFAP.ConstructiveFraction.mul_pos_direct positive positive
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne denominatorPositive.ne'
  calc
    (distribution.variance value ^ 2 / denominator) * denominator =
        distribution.variance value ^ 2 :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        (distribution.variance value ^ 2) denominator denominatorPositive.ne'
    _ = denominator := by
      dsimp only [denominator]
      ring1
    _ = 1 * denominator := by ring1

/-- With positive variance product, zero squared correlation is equivalent
to zero covariance. -/
theorem squaredCorrelation_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
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
          (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne').symm
        _ = 0 * (distribution.variance left *
              distribution.variance right) := multiplied
        _ = 0 := by ring1
    exact RFAP.ConstructiveFraction.sq_eq_zero_direct _ |>.mp squareZero
  · intro covarianceZero
    unfold squaredCorrelation
    rw [covarianceZero]
    exact RFAP.ConstructiveFraction.zero_div_direct _

/-- Squared correlation reaches one exactly when the root-free covariance
Cauchy--Schwarz inequality is an equality. -/
theorem squaredCorrelation_eq_one_iff {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
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
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne').symm
      _ = 1 * (distribution.variance left *
            distribution.variance right) := multiplied
      _ = distribution.variance left * distribution.variance right := by ring1
  · intro equality
    unfold squaredCorrelation
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne positive.ne'
    calc
      (distribution.covariance left right ^ 2 /
            (distribution.variance left * distribution.variance right)) *
          (distribution.variance left * distribution.variance right) =
        distribution.covariance left right ^ 2 :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne'
      _ = distribution.variance left * distribution.variance right := equality
      _ = 1 * (distribution.variance left *
          distribution.variance right) := by ring1

end Distribution

end FiniteMeasure
