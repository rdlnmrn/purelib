module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

/-!
# Endpoint bounds for affine rational coefficient tables

The original coefficient list selects an exact zero, constant or affine
endpoint bound. Higher-degree tables retain the original finite Horner
majorant, with the same interval and coefficient order.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.AffineHorner

open Fraction.Order
open Purelib.Geometry.Rational

/-- An affine rational value squared is bounded by the larger endpoint square.

The retained interval bounds are transported through multiplication by the
same slope and addition of the same intercept. A negative slope reverses
the two endpoint comparisons while retaining their maximum. -/
private theorem affine_sq_le (a b : Fraction.Rational) (interval : Data.Rat.Interval.Bounds)
    {x : Fraction.Rational} (inside : interval.Contains x) :
    (a * x + b) ^ 2 ≤ max ((a * interval.lower + b) ^ 2) ((a * interval.upper + b) ^ 2) := by
  by_cases nonnegative : 0 ≤ a
  · exact Box.sq_le_endpoint_max
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct inside.1 nonnegative) (le_refl b))
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2 nonnegative) (le_refl b))
  · have nonpositive : a ≤ 0 := (Arithmetic.lt_of_not_ge_direct nonnegative).le
    have negativeNonnegative : 0 ≤ -a := by
      calc
        0 = -(0 : Fraction.Rational) := rfl
        _ ≤ -a := Arithmetic.neg_le_neg_direct nonpositive
    have reversed : ∀ {left right : Fraction.Rational}, left ≤ right → a * right ≤ a * left := by
      intro left right ordered
      have flipped := Arithmetic.neg_le_neg_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct ordered negativeNonnegative)
      calc
        a * right = -((-a) * right) := by ring1
        _ ≤ -((-a) * left) := flipped
        _ = a * left := by ring1
    have lower := Arithmetic.add_le_add_direct (reversed inside.2) (le_refl b)
    have upper := Arithmetic.add_le_add_direct (reversed inside.1) (le_refl b)
    exact (Box.sq_le_endpoint_max lower upper).trans_eq (Basic.max_comm _ _)

set_option backward.match.sparseCases false in
/-- Compute the original coefficient-dispatched squared-value bound.

Empty and constant tables use their exact values, two coefficients use the
maximum of the original affine endpoint squares, and longer tables retain
the original finite Horner majorant. -/
@[expose] public def coefficientSqBound (p : Dense.Rational.Basic.CoordinatePolynomial)
    (interval : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  match p.coeffs with
  | [] => 0
  | [b] => b ^ 2
  | [a, b] => max ((a * interval.lower + b) ^ 2) ((a * interval.upper + b) ^ 2)
  | _ => Dense.Rational.Bounds.Horner.evalSqBound p interval

/-- The dispatched bound encloses every squared polynomial value on its interval.

The original empty, constant and affine tables reduce to their scalar
values; longer coefficient tables use the same finite Horner certificate. -/
public theorem eval_sq_le_coefficientSqBound (p : Dense.Rational.Basic.CoordinatePolynomial)
    (interval : Data.Rat.Interval.Bounds) {x : Fraction.Rational} (inside : interval.Contains x) :
    p.eval x ^ 2 ≤ coefficientSqBound p interval := by
  cases p with
  | mk coefficients =>
    cases coefficients with
    | nil =>
        change (0 : Fraction.Rational) ^ 2 ≤ 0
        rewrite [pow_two, Fraction.Field.zero_mul_direct]
        exact Basic.le_refl _
    | cons a tail =>
      cases tail with
      | nil =>
          change ((0 : Fraction.Rational) * x + a) ^ 2 ≤ a ^ 2
          calc
            ((0 : Fraction.Rational) * x + a) ^ 2 = a ^ 2 := by
              rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add]
            _ ≤ a ^ 2 := le_rfl
      | cons b tail =>
        cases tail with
        | nil =>
            change (((0 : Fraction.Rational) * x + a) * x + b) ^ 2 ≤
              max ((a * interval.lower + b) ^ 2) ((a * interval.upper + b) ^ 2)
            calc
              (((0 : Fraction.Rational) * x + a) * x + b) ^ 2 = (a * x + b) ^ 2 := by
                rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add]
              _ ≤ _ := affine_sq_le a b interval inside
        | cons c tail =>
          exact Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
            ⟨a :: b :: c :: tail⟩ interval inside

/-- The dispatched bound never exceeds the original finite Horner bound.

Both affine endpoint squares are enclosed by the original Horner
certificate on that same interval. Higher-degree tables keep that bound
unchanged, and the empty table retains the Horner nonnegativity bound. -/
public theorem coefficientSqBound_le_previous (p : Dense.Rational.Basic.CoordinatePolynomial)
    (interval : Data.Rat.Interval.Bounds) :
    coefficientSqBound p interval ≤ Dense.Rational.Bounds.Horner.evalSqBound p interval := by
  cases p with
  | mk coefficients =>
    cases coefficients with
    | nil => exact Dense.Rational.Bounds.Horner.evalSqBound_nonneg ⟨[]⟩ interval
    | cons a tail =>
      cases tail with
      | nil =>
          have bound := Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
            (⟨[a]⟩ : Dense.Rational.Basic.CoordinatePolynomial) interval ⟨le_rfl, interval.valid⟩
          change ((0 : Fraction.Rational) * interval.lower + a) ^ 2 ≤ _ at bound
          rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add] at bound
          exact bound
      | cons b tail =>
        cases tail with
        | nil =>
          apply Basic.max_le
          · have bound := Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
              (⟨[a, b]⟩ : Dense.Rational.Basic.CoordinatePolynomial) interval ⟨le_rfl, interval.valid⟩
            change (((0 : Fraction.Rational) * interval.lower + a) * interval.lower + b) ^ 2 ≤ _ at bound
            rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add] at bound
            exact bound
          · have bound := Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
              (⟨[a, b]⟩ : Dense.Rational.Basic.CoordinatePolynomial) interval ⟨interval.valid, le_rfl⟩
            change (((0 : Fraction.Rational) * interval.upper + a) * interval.upper + b) ^ 2 ≤ _ at bound
            rw [Fraction.Field.zero_mul_direct, Fraction.Field.zero_add] at bound
            exact bound
        | cons c tail => exact le_rfl

end Purelib.Polynomial.Dense.Rational.Bounds.AffineHorner
