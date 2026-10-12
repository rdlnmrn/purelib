module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Sign.Products
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Interval.UniformLocalEquality
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

public section

/-!
# Sign constancy from a uniform finite clearance

A coefficient-computed Lipschitz bound and a positive squared-value floor
force one sign throughout a rational interval.  The proof uses a bounded
midpoint subdivision, not an intermediate-value theorem or a root set.
The subdivision is proof-only: a consumer computes its sign at one point.
-/

namespace Purelib.Polynomial.Dense.Rational.Sign.Interval.Uniform

/-- A positive uniform squared clearance fixes the sign throughout a rational interval.

The coefficient-computed Lipschitz bound supplies a positive local radius.
Finite midpoint subdivisions extend the same nonnegative decision between
any two retained interval points. -/
theorem sign_eq_of_squared_lower (polynomial : (Dense.Basic.DensePolynomial Fraction.Rational)) (interval :
  Data.Rat.Interval.Bounds)
    {lower : Fraction.Rational} (positive : 0 < lower)
    (clearance : ∀ point, interval.Contains point → lower ≤ polynomial.eval point ^ 2)
    {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
    decide (0 ≤ polynomial.eval x) = decide (0 ≤ polynomial.eval y) := by
  let slope := Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound polynomial interval
  have slopeNonnegative : 0 ≤ slope := (Dense.Rational.Bounds.Lipschitz.denseHornerSqBounds_nonneg polynomial
    interval).2
  have denominatorPositive : 0 < 2 * (slope + 1) :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      slopeNonnegative (by decide))
  let radius := lower / (2 * (slope + 1))
  have radiusPositive : 0 < radius := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have small : slope * radius < lower := by
    calc
      _ ≤ (slope + 1) * radius := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right (by decide)) radiusPositive.le
      _ = lower / 2 := by
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
        calc
          _ = radius * (2 * (slope + 1)) := by ring1
          _ = lower := Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
      _ < lower := (Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : Fraction.Rational) < 2)).2
        ((by ring1 : lower = lower * 1).trans_lt
          (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive (by decide)))
  apply interval.eq_of_uniform_local (fun point => decide (0 ≤ polynomial.eval point)) radiusPositive
    (xInside := xInside) (yInside := yInside)
  intro left right leftInside rightInside close
  apply Data.Rat.Sign.Products.nonnegative_sign_eq_of_mul_pos
  apply Data.Rat.Sign.Products.mul_pos_of_sub_sq_lt_sq
  exact (Dense.Rational.Bounds.Lipschitz.eval_sub_sq_le polynomial interval leftInside rightInside).trans_lt
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close slopeNonnegative).trans_lt
      (small.trans_le (clearance right rightInside)))

end Purelib.Polynomial.Dense.Rational.Sign.Interval.Uniform

end
