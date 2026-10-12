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
