module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Sign constancy from a uniform finite clearance

A coefficient-computed Lipschitz bound and a positive squared-value floor
force one sign throughout a rational interval.  The proof uses a bounded
midpoint subdivision, not an intermediate-value theorem or a root set.
The subdivision is proof-only: a consumer computes its sign at one point.
-/

namespace Purelib.Data.Rat.Interval.Bounds

open Purelib.Data.Rat in
/-- Uniform local equality extends across a rational interval once the supplied finite contraction depth meets the
square-distance bound.

The proof repeatedly inserts rational midpoints inside the same interval. Each finite step contracts the squared
displacement enough to reach the given local equality hypothesis, then composes the two endpoint equalities. -/
private theorem eq_at_depth {Alpha : Type} (value : Fraction.Rational →
  Alpha)
    (interval : Bounds) (radius : Fraction.Rational)
    (localEq : ∀ {x y}, interval.Contains x → interval.Contains y →
      (x - y) ^ 2 ≤ radius → value x = value y)
    (depth : Nat) {x y : Fraction.Rational}
    (xInside : interval.Contains x) (yInside : interval.Contains y)
    (small : (2 / 3 : Fraction.Rational) ^ depth * (x - y) ^ 2 ≤ radius) :
    value x = value y := by
  induction depth generalizing x y with
  | zero => exact localEq xInside yInside (by simpa only [pow_zero, _root_.one_mul] using small)
  | succ depth ih =>
      let middle := (x + y) / 2
      have twiceMiddle : middle * 2 = x + y := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      have middleInside : interval.Contains middle := by
        constructor
        · apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2) ?_ (by decide)
          rw [twiceMiddle]
          exact (by ring1 : interval.lower * 2 = interval.lower + interval.lower).trans_le
            (add_le_add xInside.1 yInside.1)
        · apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2) ?_ (by decide)
          rw [twiceMiddle]
          exact (add_le_add xInside.2 yInside.2).trans_eq (by ring1)
      have leftTwice : (x - middle) * 2 = x - y := by
        calc
          _ = x * 2 - middle * 2 := by ring1
          _ = x - y := by rw [twiceMiddle]; ring1
      have leftWidth : (x - middle) ^ 2 ≤ (2 / 3 : Fraction.Rational) * (x - y) ^ 2 := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 4) ?_ (by decide)
        calc
          _ = ((x - middle) * 2) ^ 2 := by ring1
          _ = (x - y) ^ 2 := by rw [leftTwice]
          _ = 1 * (x - y) ^ 2 := by ring1
          _ ≤ ((2 / 3 : Fraction.Rational) * 4) * (x - y) ^ 2 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide)
              (Fraction.Order.Arithmetic.sq_nonneg_direct _)
          _ = _ := by ring1
      have rightWidth : (middle - y) ^ 2 = (x - middle) ^ 2 := by
        apply congrArg (fun value : Fraction.Rational => value ^ 2)
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = middle * 2 - y * 2 := by ring1
          _ = (x + y) - y * 2 := by rw [twiceMiddle]
          _ = x - y := by ring1
          _ = _ := leftTwice.symm
      have leftSmall : (2 / 3 : Fraction.Rational) ^ depth * (x - middle) ^ 2 ≤ radius := by
        calc
          _ ≤ (2 / 3 : Fraction.Rational) ^ depth * ((2 / 3 : Fraction.Rational) * (x - y) ^ 2) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftWidth
              (Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth).le
          _ = (2 / 3 : Fraction.Rational) ^ (depth + 1) * (x - y) ^ 2 := by rw [pow_succ]; ring1
          _ ≤ _ := small
      exact (ih xInside middleInside leftSmall).trans
        (ih middleInside yInside (by rw [rightWidth]; exact leftSmall))

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- A function uniformly locally constant at a positive square-radius is constant on the whole retained rational
interval.

Compute a sufficient finite geometric depth from the endpoint square distance and the supplied positive radius. Repeated
midpoint subdivision transports local equality across the original interval without an infinite or compactness argument.
-/
theorem eq_of_uniform_local {Alpha : Type} (value : Fraction.Rational →
  Alpha)
    (interval : Bounds) {radius : Fraction.Rational} (positive : 0 < radius)
    (localEq : ∀ {x y}, interval.Contains x → interval.Contains y →
      (x - y) ^ 2 ≤ radius → value x = value y)
    {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
    value x = value y :=
  eq_at_depth value interval radius localEq
    (Contraction.geometricDepth ((x - y) ^ 2) radius) xInside yInside
    (Contraction.geometricDepth_sufficient (Fraction.Order.Arithmetic.sq_nonneg_direct _) positive)

end Purelib.Data.Rat.Interval.Bounds

end
