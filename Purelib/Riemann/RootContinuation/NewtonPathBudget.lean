module
import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# A finite Newton tolerance chosen before the requested grid

The cached weight pays both the full source polygon and total increment
using a request-independent occurrence cap. No square root or search for a
successful mesh is needed; all subsequent refinement counts disappear.
-/

namespace Purelib.Riemann.RootContinuation.NewtonPathBudget

open Purelib.Data.Rat.Fraction (Rational)

set_option genInjectivity false in
open Purelib.Data in
/-- A positive path target with cached occurrence weight and a common bounded scale.

For count n, the weight is 64 n⁴ + 4 n² and the scale is the smaller of one and target divided by one plus weight. Both
polygon-area and total-increment allowances consume this same scale. -/
structure PathBudget (count : Nat) (target : Rat.Fraction.Rational) where
  /-- The retained path target is strictly positive. -/ positive : 0 < target
  /-- The cached rational weight for both occurrence-count bounds. -/ weight : Rat.Fraction.Rational
  /-- The cached weight equals 64 times count to the fourth plus four times count squared. -/ weight_eq : weight = 64 *
    (count : Rat.Fraction.Rational) ^ 4 + 4 * (count : Rat.Fraction.Rational) ^ 2
  /-- The cached common scale for the path and band requests. -/ scale : Rat.Fraction.Rational
  /-- The scale equals the minimum of one and target divided by weight plus one. -/ scale_eq : scale = min 1 (target /
    (weight + 1))

constructive_injectivity PathBudget

namespace PathBudget

variable {count : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data in
/-- The rational fourth power of a natural count is nonnegative. -/
private theorem fourth_nonnegative (count : Nat) : (0 : Rat.Fraction.Rational) ≤ (count : Rat.Fraction.Rational) ^ 4 :=
  (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct ((count : Rat.Fraction.Rational) ^ 2)).trans_eq (by ring1)

open Purelib.Riemann in
open Purelib.Data in
/-- The retained path-budget weight is nonnegative. -/
theorem weight_nonnegative (budget : RootContinuation.NewtonPathBudget.PathBudget count target) : 0 ≤ budget.weight :=
  by
  rw [budget.weight_eq]
  exact add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (RootContinuation.NewtonPathBudget.PathBudget.fourth_nonnegative _))
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Cache the occurrence weight and common scale for a positive path target. -/
@[expose] def build (count : Nat) (target : Rat.Fraction.Rational) (positive : 0 < target) :
  RootContinuation.NewtonPathBudget.PathBudget count target :=
  let n := Rational.Budget.Aggregate.countCoordinate count
  let weight := 64 * n ^ 4 + 4 * n ^ 2
  ⟨positive, weight, by dsimp only [weight, n]; rw [Rational.Budget.Aggregate.countCoordinate_eq],
    min 1 (target / (weight + 1)), rfl⟩

open Purelib.Riemann in
open Purelib.Data in
/-- The retained path-budget scale is strictly positive. -/
theorem scale_positive (budget : RootContinuation.NewtonPathBudget.PathBudget count target) : 0 < budget.scale := by
  rw [budget.scale_eq]
  exact Rat.Fraction.Order.Basic.lt_min (by decide) (Rat.Fraction.Order.Field.div_pos_direct budget.positive
    (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct budget.weight_nonnegative (by decide)))

open Purelib.Riemann in
/-- The retained path-budget scale is at most one. -/
theorem scale_le_one (budget : RootContinuation.NewtonPathBudget.PathBudget count target) : budget.scale ≤ 1 := by
  rw [budget.scale_eq]
  exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _

open Purelib.Riemann
open Purelib.Data
/-- The retained weight times the common scale is strictly below the target. -/
theorem weighted_paid (budget : RootContinuation.NewtonPathBudget.PathBudget count target) : budget.weight *
  budget.scale < target := by
  have denominator := Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct budget.weight_nonnegative (by
      decide : (0 : Rat.Fraction.Rational) < 1)
  calc
    _ < (budget.weight + 1) * budget.scale :=
      Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by
          have strict := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct (by
              decide : (0 : Rat.Fraction.Rational) < 1) budget.weight
          rw [show budget.weight + 0 = budget.weight by ring1] at strict
          exact strict) budget.scale_positive
    _ ≤ (budget.weight + 1) * (target / (budget.weight + 1)) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by rw [budget.scale_eq]; exact Rat.Fraction.Order.Basic.min_le_right _ _) denominator.le
    _ = target := by
      rw [Rat.Fraction.Field.mul_comm]
      exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'

/-- The fourth-power occurrence area allowance is strictly below the target. -/
theorem area_paid (budget : RootContinuation.NewtonPathBudget.PathBudget count target) :
    64 * (count : Rat.Fraction.Rational) ^ 4 * budget.scale ^ 2 < target := by
  have square : budget.scale ^ 2 ≤ budget.scale := by
    simpa only [pow_two, mul_one] using
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.scale_le_one budget.scale_positive.le
  have coefficient : (0 : Rat.Fraction.Rational) ≤ 64 * (count : Rat.Fraction.Rational) ^ 4 :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (RootContinuation.NewtonPathBudget.PathBudget.fourth_nonnegative _)
  have weight : 64 * (count : Rat.Fraction.Rational) ^ 4 ≤ budget.weight := by
    rw [budget.weight_eq]
    have nonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 4)
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (count : Rat.Fraction.Rational))
    have bound := Rat.Fraction.Order.Arithmetic.add_le_add_direct (le_refl (64 * (count : Rat.Fraction.Rational) ^ 4))
      nonnegative
    rw [show 64 * (count : Rat.Fraction.Rational) ^ 4 + 0 = 64 * (count : Rat.Fraction.Rational) ^ 4 by ring1] at bound
    exact bound
  exact ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square coefficient).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weight budget.scale_positive.le)).trans_lt
      budget.weighted_paid

/-- The squared-occurrence total-increment allowance is strictly below the target. -/
theorem total_paid (budget : RootContinuation.NewtonPathBudget.PathBudget count target) : 4 * (count :
  Rat.Fraction.Rational) ^ 2 * budget.scale < target := by
  have weight : 4 * (count : Rat.Fraction.Rational) ^ 2 ≤ budget.weight := by
    rw [budget.weight_eq]
    have nonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rat.Fraction.Rational)
      ≤ 64) (RootContinuation.NewtonPathBudget.PathBudget.fourth_nonnegative count)
    have bound := Rat.Fraction.Order.Arithmetic.add_le_add_direct nonnegative (le_refl (4 * (count :
      Rat.Fraction.Rational) ^ 2))
    rw [show 0 + 4 * (count : Rat.Fraction.Rational) ^ 2 = 4 * (count : Rat.Fraction.Rational) ^ 2 by ring1] at bound
    exact bound
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weight budget.scale_positive.le).trans_lt
    budget.weighted_paid

/-- The common scale pays the combined tolerance and one-sixteenth band increment. -/
theorem increment_le (budget : RootContinuation.NewtonPathBudget.PathBudget count target) :
    3 * budget.scale + 4 * (budget.scale / 16) ≤ 4 * budget.scale := by
  have small := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide : (4 : Rat.Fraction.Rational) ≤ 16)
    (Rat.Fraction.Order.Field.div_nonneg_direct budget.scale_positive.le (by decide : (0 : Rat.Fraction.Rational) ≤ 16))
  have cancel : (16 : Rat.Fraction.Rational) * (budget.scale / 16) = budget.scale := by
    rw [Rat.Fraction.Field.mul_comm]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  rw [cancel] at small
  exact (add_le_add le_rfl small).trans_eq (by ring1)

end PathBudget
end Purelib.Riemann.RootContinuation.NewtonPathBudget
