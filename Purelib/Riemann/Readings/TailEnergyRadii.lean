module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Curves.Hyperelliptic.Periods.Matrix.Positivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Purelib.Polynomial.Geometry.EvaluationLower

import Purelib.Curves.Hyperelliptic.Periods.Normalization.SynchronizedNormalization
import Purelib.Riemann.Readings.TailSynchronizedEnergy
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Integration.Energy

public section

/-! Finite radii paying both normalized perturbation budgets from a retained
positive energy floor. The calculation does not require all-sample inversion. -/
namespace Purelib.Riemann.Readings.TailEnergyRadii

open Purelib.Riemann.Periods.PeriodMatrix (NormalizedPeriodData)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat}

section
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
/-- Allocate a quarter of the energy after dividing by one plus the vector's budget slope. -/
@[expose] def comparison (vector : Geometry.EvaluationLower.RationalVector genus) (energy : Rat.Fraction.Rational) :
  Rat.Fraction.Rational :=
  energy / (1 + Prepared.budgetSlope vector) / 4

/-- One plus the retained vector's nonnegative budget slope is strictly positive. -/
theorem denominator_positive (vector : Geometry.EvaluationLower.RationalVector genus) :
    0 < 1 + Prepared.budgetSlope vector :=
  (by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
    (le_add_of_nonneg_right (Prepared.budgetSlope_nonnegative vector))

end

open Purelib.Data in
open Purelib.Polynomial in
/-- A positive energy floor gives a strictly positive comparison radius. -/
theorem comparison_positive (vector : Geometry.EvaluationLower.RationalVector genus) {energy : Rat.Fraction.Rational}
    (positive : 0 < energy) : 0 < comparison vector energy :=
  Field.div_pos_direct (Field.div_pos_direct positive (denominator_positive
    vector)) (by decide)

section
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
/-- Choose a radius satisfying the target, comparison and shared energy restrictions.

Take the minimum of the target radius, the comparison refinement radius and the comparison radius itself. -/
@[expose] def refinement (vector : Geometry.EvaluationLower.RationalVector genus) (energy target :
  Rat.Fraction.Rational) : Rat.Fraction.Rational :=
  min (Prepared.targetRadius target)
    (min (Prepared.comparisonRefinementRadius (comparison vector energy)) (comparison
      vector energy))

/-- Positive energy and target give a strictly positive refinement radius. -/
theorem refinement_positive (vector : Geometry.EvaluationLower.RationalVector genus) {energy target :
  Rat.Fraction.Rational}
    (energyPositive : 0 < energy) (targetPositive : 0 < target) :
    0 < refinement vector energy target :=
  Basic.lt_min (Prepared.targetRadius_positive
    targetPositive)
    (Basic.lt_min
      (Prepared.comparisonRefinementRadius_positive (comparison_positive vector
      energyPositive))
      (comparison_positive vector energyPositive))

/-- The chosen refinement radius has squared refinement target strictly below the requested target. -/
theorem refinement_target (vector : Geometry.EvaluationLower.RationalVector genus) {energy target :
  Rat.Fraction.Rational}
    (energyPositive : 0 < energy) (targetPositive : 0 < target) :
    Rat.Quadratic.Bounds.squaredRefinementTarget (refinement vector energy target) < target :=
  (Arithmetic.pow_le_pow_direct (refinement_positive vector energyPositive targetPositive).le
    (Basic.min_le_left _ _) 2).trans_lt
      (Prepared.targetRadius_sq_lt_target targetPositive)

/-- The chosen refinement radius has squared target strictly below the retained comparison target. -/
theorem refinement_comparison (vector : Geometry.EvaluationLower.RationalVector genus) {energy target :
  Rat.Fraction.Rational}
    (energyPositive : 0 < energy) (targetPositive : 0 < target) :
    Rat.Quadratic.Bounds.squaredRefinementTarget (refinement vector energy target) <
      Hyperelliptic.Periods.Normalization.SynchronizedNormalization.comparisonTarget (comparison vector energy) :=
  (Arithmetic.pow_le_pow_direct (refinement_positive vector energyPositive targetPositive).le
    ((Basic.min_le_right _ _).trans (Basic.min_le_left _
      _)) 2).trans_lt
      (Prepared.comparisonRefinementRadius_sq_lt_target (comparison_positive vector
        energyPositive))

end

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The vector's comparison perturbation budget is at most a quarter of the energy floor. -/
theorem comparison_budget (vector : Geometry.EvaluationLower.RationalVector genus) {energy : Rat.Fraction.Rational}
    (positive : 0 < energy) : Prepared.budgetSlope vector * comparison vector energy ≤
      energy / 4 := by
  calc
    _ ≤ (1 + Prepared.budgetSlope vector) * comparison vector energy :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_left (by decide))
        (comparison_positive vector positive).le
    _ = energy / 4 := by
      unfold comparison
      calc
        _ = (energy / (1 + Prepared.budgetSlope vector) * (1 +
          Prepared.budgetSlope vector)) / 4 := by
          simp only [-eq_self, -iff_self, Rat.Fraction.Field.div_eq_mul_inv_direct]
          ring1
        _ = energy / 4 := by
          rw [Field.ExplicitField.div_mul_cancel energy (ne_of_gt (denominator_positive vector))]

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.LinearAlgebra in
/-- The two normalized perturbation budgets together are strictly below the retained energy floor.

The same vector, positive energy and target determine both radii; each budget is at most one quarter of that energy. -/
theorem budgets_lt_energy {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) (vector : Geometry.EvaluationLower.RationalVector genus)
    {energy target : Rat.Fraction.Rational} (energyPositive : 0 < energy) (targetPositive : 0 < target) :
    Matrix.Rational.Budget.totalBudget (Matrix.Rational.Budget.automaticBudget
      vector
      (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius data (refinement vector energy target)
        (refinement_positive vector energyPositive targetPositive))) +
    Matrix.Rational.Budget.totalBudget (Matrix.Rational.Budget.automaticBudget
      vector
      (Hyperelliptic.Periods.Matrix.Positivity.automaticRadius data (comparison vector energy)
        (comparison_positive vector energyPositive))) < energy := by
  rw [Prepared.automaticBudget_eq_budgetSlope_mul,
    Prepared.automaticBudget_eq_budgetSlope_mul]
  have first : Prepared.budgetSlope vector * refinement vector energy target ≤ energy /
    4 :=
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      ((Basic.min_le_right _ _).trans
        (Basic.min_le_right _ _))
        (Prepared.budgetSlope_nonnegative vector)).trans
        (comparison_budget vector energyPositive)
  have combined := Arithmetic.add_le_add_direct first (comparison_budget vector energyPositive)
  apply combined.trans_lt
  have half : energy / 2 < energy := by
    apply (Field.div_lt_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 2)).mpr
    calc
      energy = energy * 1 := by ring1
      _ < energy * 2 := Arithmetic.mul_lt_mul_of_pos_left_direct energyPositive (by decide)
  calc
    energy / 4 + energy / 4 = energy / 2 := by
      simp only [-eq_self, -iff_self, Rat.Fraction.Field.div_eq_mul_inv_direct]
      rw [← mul_add, show (4 : Rat.Fraction.Rational)⁻¹ + (4 : Rat.Fraction.Rational)⁻¹ = (2 : Rat.Fraction.Rational)⁻¹
        by decide]
    _ < energy := half

end Purelib.Riemann.Readings.TailEnergyRadii
