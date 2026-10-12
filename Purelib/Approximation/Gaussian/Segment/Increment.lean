module
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Interval.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Removing a fourth-order increment remainder by finite subdivision

A squared increment estimate `A * d² + R * d⁴` implies `A * d²` on the
whole rational segment.  The proof splits at displayed midpoints a bounded
number of times.  A putative positive gap determines the finite depth which
disproves it; no limit, completion, or unbounded search is involved.
-/

namespace Purelib.Approximation.Gaussian.Segment.Increment
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Finite midpoint subdivision reduces the quartic increment allowance by the displayed two-thirds power.

At each natural depth, both endpoints remain in the original rational interval and the quadratic coefficient is
unchanged. -/
private theorem at_depth (value : Fraction.Rational →
  Data.Gaussian.Basic.Canonical) (interval : Data.Rat.Interval.Bounds)
    (quadratic quartic : Fraction.Rational) (quarticNonnegative : 0 ≤ quartic)
    (localBound : ∀ {x y}, interval.Contains x → interval.Contains y →
      Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤ quadratic * (x - y) ^ 2 + quartic * (x - y) ^ 4)
    (depth : Nat) {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
    Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤
      quadratic * (x - y) ^ 2 + quartic * (2 / 3 : Fraction.Rational) ^ depth * (x - y) ^ 4 := by
  induction depth generalizing x y with
  | zero => simpa only [pow_zero, Fraction.Field.mul_one_direct] using localBound xInside yInside
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
          _ = _ := by rw [twiceMiddle]; ring1
      have rightEq : middle - y = x - middle := by
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = middle * 2 - y * 2 := by ring1
          _ = (x + y) - y * 2 := by rw [twiceMiddle]
          _ = x - y := by ring1
          _ = _ := leftTwice.symm
      have squareEq : 4 * (x - middle) ^ 2 = (x - y) ^ 2 := by
        calc
          _ = ((x - middle) * 2) ^ 2 := by ring1
          _ = _ := by rw [leftTwice]
      have fourthLe : 4 * (x - middle) ^ 4 ≤ (2 / 3 : Fraction.Rational) * (x - y) ^ 4 := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 4) ?_ (by decide)
        calc
          _ = ((x - middle) * 2) ^ 4 := by ring1
          _ = (x - y) ^ 4 := by rw [leftTwice]
          _ = 1 * (x - y) ^ 4 := by ring1
          _ ≤ ((2 / 3 : Fraction.Rational) * 4) * (x - y) ^ 4 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide)
              (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct (x - y)) 2
              |>.trans_eq (by ring1))
          _ = _ := by ring1
      have rightBound := ih middleInside yInside
      rw [rightEq] at rightBound
      calc
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (value x - value middle) +
          Data.Gaussian.Norm.Basic.normSq (value middle - value y)) :=
          Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
        _ ≤ 2 * ((quadratic * (x - middle) ^ 2 + quartic * (2 / 3 : Fraction.Rational) ^ depth * (x - middle) ^ 4) +
            (quadratic * (x - middle) ^ 2 + quartic * (2 / 3 : Fraction.Rational) ^ depth * (x - middle) ^ 4)) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (ih xInside middleInside) rightBound)
            (by decide)
        _ = quadratic * (4 * (x - middle) ^ 2) + quartic * (2 / 3 : Fraction.Rational) ^ depth * (4 * (x - middle) ^ 4)
          := by
          ring1
        _ ≤ quadratic * (x - y) ^ 2 + quartic * (2 / 3 : Fraction.Rational) ^ depth * ((2 / 3 : Fraction.Rational) * (x
          - y) ^ 4) :=
          add_le_add (le_of_eq (congrArg (quadratic * ·) squareEq))
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct fourthLe
              (Fraction.Order.Arithmetic.mul_nonneg_direct quarticNonnegative (Fraction.Order.Arithmetic.pow_pos_direct
              (by decide) depth).le))
        _ = _ := by rw [pow_succ]; ring1

/-- Finite midpoint refinement removes the Taylor remainder completely from the global increment estimate. The function
is used only at finitely many rational parameters in each proof request. -/
theorem remove_quartic (value : Fraction.Rational →
  Data.Gaussian.Basic.Canonical) (interval : Data.Rat.Interval.Bounds)
    (quadratic quartic : Fraction.Rational) (quarticNonnegative : 0 ≤ quartic)
    (localBound : ∀ {x y}, interval.Contains x → interval.Contains y →
      Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤ quadratic * (x - y) ^ 2 + quartic * (x - y) ^ 4)
    {x y : Fraction.Rational} (xInside : interval.Contains x) (yInside : interval.Contains y) :
    Data.Gaussian.Norm.Basic.normSq (value x - value y) ≤ quadratic * (x - y) ^ 2 := by
  apply le_of_not_gt
  intro contrary
  let gap := Data.Gaussian.Norm.Basic.normSq (value x - value y) - quadratic * (x - y) ^ 2
  have gapPositive : 0 < gap := Fraction.Order.Arithmetic.sub_pos_direct contrary
  have scaleNonnegative : 0 ≤ quartic * (x - y) ^ 4 := Fraction.Order.Arithmetic.mul_nonneg_direct quarticNonnegative
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct (x - y)) 2 |>.trans_eq (by
      ring1))
  let depth := Contraction.geometricDepth (quartic * (x - y) ^ 4) (gap / 2)
  have small : (2 / 3 : Fraction.Rational) ^ depth * (quartic * (x - y) ^ 4) ≤ gap / 2 :=
    Contraction.geometricDepth_sufficient scaleNonnegative (Fraction.Order.Field.div_pos_direct gapPositive (by decide))
  have halfLt : gap / 2 < gap := (Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : Fraction.Rational) < 2)).2
    ((by ring1 : gap = gap * 1).trans_lt (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct gapPositive (by
      decide)))
  have impossible : Data.Gaussian.Norm.Basic.normSq (value x - value y) <
    Data.Gaussian.Norm.Basic.normSq (value x - value y) := by
    calc
      _ ≤ quadratic * (x - y) ^ 2 + quartic * (2 / 3 : Fraction.Rational) ^ depth * (x - y) ^ 4 :=
        at_depth value interval quadratic quartic quarticNonnegative localBound
          depth xInside yInside
      _ = quadratic * (x - y) ^ 2 + (2 / 3 : Fraction.Rational) ^ depth * (quartic * (x - y) ^ 4) := by ring1
      _ ≤ quadratic * (x - y) ^ 2 + gap / 2 := add_le_add le_rfl small
      _ < quadratic * (x - y) ^ 2 + gap := Fraction.Order.Arithmetic.add_lt_add_left_direct halfLt _
      _ = _ := by dsimp [gap]; ring1
  exact lt_irrefl _ impossible

end Purelib.Approximation.Gaussian.Segment.Increment

end
