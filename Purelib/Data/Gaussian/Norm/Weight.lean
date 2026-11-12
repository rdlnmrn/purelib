module

public import Purelib.Algebra.Ring.Weight
public import Purelib.Data.Gaussian.Norm.Basic
-- The exposed weight retains the original squared triangle certificate.
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! The original Gaussian quadrance supplies a rational squared weight. -/

public section

namespace Purelib.Data.Gaussian.Norm

open Purelib.Algebra.Ring
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)

/-- Retain the original executable Gaussian quadrance with its exact product law.

The uniform product multiplier is one; the underlying scalar operations and
the original two rational coordinates are unchanged.
-/
@[expose] def weight : Weight Gaussian.Basic.Canonical where
  value := Basic.normSq
  nonnegative := Basic.normSq_nonneg
  zero := Basic.normSq_zero
  neg := Basic.normSq_neg
  add_le := Bounds.normSq_add_le_two
  multiplier := 1
  one_le_multiplier := le_rfl
  mul_le left right := by
    rewrite [one_mul, Basic.normSq_mul]
    exact le_rfl

/-- Pointwise squared-norm bounds control the same finite Gaussian sum. -/
theorem normSq_sumFin_le {count : Nat} (values : Fin count → Gaussian.Basic.Canonical)
    (bounds : Fin count → Rational) (bounded : ∀ index, Basic.normSq (values index) ≤ bounds index) :
    Basic.normSq (sumFin values) ≤ (2 : Rational) ^ count * sumFin bounds :=
  (weight.sum_le values).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (IndexedBudget.sumFin_le bounded)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) count))

/-- Separate pointwise bounds on two Gaussian factors control their same finite sum of products. -/
theorem normSq_sumFin_mul_le {count : Nat} (left right : Fin count → Gaussian.Basic.Canonical)
    (leftBounds rightBounds : Fin count → Rational)
    (leftBound : ∀ index, Basic.normSq (left index) ≤ leftBounds index)
    (rightBound : ∀ index, Basic.normSq (right index) ≤ rightBounds index) :
    Basic.normSq (sumFin (fun index => left index * right index)) ≤
      (2 : Rational) ^ count * sumFin (fun index => leftBounds index * rightBounds index) := by
  apply normSq_sumFin_le
  intro index
  rewrite [Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct (leftBound index) (rightBound index)
    (Basic.normSq_nonneg _) ((Basic.normSq_nonneg _).trans (leftBound index))

end Purelib.Data.Gaussian.Norm

end
