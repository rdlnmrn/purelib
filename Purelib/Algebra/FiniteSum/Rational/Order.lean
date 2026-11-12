module
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Algebra

/-! Bounds for the original finite sums of rational coordinates. -/

public section

namespace Purelib.Algebra.FiniteSum.Rational.Order

namespace IndexedBudget

/-- Pointwise rational bounds pass to a finite sum.

Both families share the same finite index type, and a weak inequality is supplied at each index. -/
theorem sumFin_le {count : Nat} {left right : Fin count → Fraction.Rational}
    (le : ∀ index, left index ≤ right index) : FiniteSum.Fin.sumFin left ≤ FiniteSum.Fin.sumFin right := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
      exact Fraction.Order.Arithmetic.add_le_add_direct (le 0)
        (inductionHypothesis (fun index => le index.succ))

end IndexedBudget

/-- Every retained nonnegative weight is bounded by its original finite sum.

The selected index singles out one summand. The remaining entries retain
their nonnegative bounds, and pointwise comparison transports this singleton
family to the same original ordered sum. -/
theorem weight_le_sum {count : Nat} (weights : Fin count → Fraction.Rational)
    (nonnegative : ∀ index, 0 ≤ weights index) (index : Fin count) :
    weights index ≤ FiniteSum.Fin.sumFin weights := by
  have bounded := IndexedBudget.sumFin_le
    (left := fun other => if other = index then weights other else 0)
    (right := weights) (fun other => by
      by_cases same : other = index
      · rewrite [if_pos same]
        exact le_rfl
      · rewrite [if_neg same]
        exact nonnegative other)
  rewrite [FiniteSum.Fin.sumFin_ite_eq] at bounded
  exact bounded

/-- Every retained entry of a nonnegative rational family is bounded by its original finite sum. -/
theorem entry_le_sumFin {count : Nat} (values : Fin count → Fraction.Rational)
    (nonnegative : ∀ index, 0 ≤ values index) (selected : Fin count) :
    values selected ≤ FiniteSum.Fin.sumFin values := by
  apply (FiniteSum.Fin.sumFin_ite_eq selected values).symm.le.trans
  apply IndexedBudget.sumFin_le
  intro index
  by_cases same : index = selected
  · rewrite [if_pos same]
    exact le_rfl
  · rewrite [if_neg same]
    exact nonnegative index

/-- A diagonal sum of products of nonnegative entries is bounded by the product of the two original sums. -/
theorem sumFin_mul_le {count : Nat} (left right : Fin count → Fraction.Rational)
    (leftNonnegative : ∀ index, 0 ≤ left index) (rightNonnegative : ∀ index, 0 ≤ right index) :
    FiniteSum.Fin.sumFin (fun index => left index * right index) ≤
      FiniteSum.Fin.sumFin left * FiniteSum.Fin.sumFin right := by
  apply (IndexedBudget.sumFin_le (fun index =>
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (entry_le_sumFin right rightNonnegative index) (leftNonnegative index))).trans
  exact (FiniteSum.Fin.sumFin_mul_right left (FiniteSum.Fin.sumFin right)).le

/-- A finite family of nonnegative rational weights has nonnegative total.

Zero weights and the empty family are allowed. -/
theorem weight_sum_nonnegative {count : Nat} (weights : Fin count → Fraction.Rational)
    (nonnegative : ∀ index, 0 ≤ weights index) : 0 ≤ FiniteSum.Fin.sumFin weights := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    exact add_nonneg (nonnegative 0) (ih _ (fun index => nonnegative index.succ))

namespace Positivity

/-- Finite rational sums preserve pointwise weak inequalities.

The two families use the same explicit finite dimension. -/
theorem sumFin_mono {count : Nat} (left right : Fin count -> Fraction.Rational)
    (pointwise : forall index, left index <= right index) :
    FiniteSum.Fin.sumFin left <=
      FiniteSum.Fin.sumFin right := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ,
        FiniteSum.Fin.sumFin_succ]
      exact add_le_add (pointwise 0)
        (inductionHypothesis
          (fun index : Fin count => left index.succ)
          (fun index : Fin count => right index.succ)
          (fun index => pointwise index.succ))

end Positivity

end Purelib.Algebra.FiniteSum.Rational.Order
