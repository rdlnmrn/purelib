module
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Finite removal of a rational increment remainder

A local lower increment estimate with a nonnegative quadratic remainder
implies the corresponding linear bound over the whole rational segment.
Each putative positive gap determines a finite midpoint-subdivision depth.
-/

public section

namespace Purelib.Approximation.Rational.Segment.Increment

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Each finite midpoint subdivision contracts the retained quadratic remainder. -/
private theorem at_depth (value : Fraction.Rational → Fraction.Rational) (interval : Purelib.Data.Rat.Interval)
    (linear remainder : Fraction.Rational) (nonnegative : 0 ≤ remainder)
    (localBound : ∀ {first last}, interval.Contains first → interval.Contains last → last ≤ first →
      linear * (first - last) - remainder * (first - last) ^ 2 ≤ value first - value last)
    (depth : Nat) {first last : Fraction.Rational} (firstInside : interval.Contains first)
    (lastInside : interval.Contains last) (ordered : last ≤ first) :
    linear * (first - last) - remainder * (2 / 3 : Fraction.Rational) ^ depth * (first - last) ^ 2 ≤
      value first - value last := by
  induction depth generalizing first last with
  | zero =>
      simpa only [pow_zero, Fraction.Field.mul_one_direct] using localBound firstInside lastInside ordered
  | succ depth inductionHypothesis =>
      let segment : Purelib.Data.Rat.Interval := ⟨last, first, ordered⟩
      let middle := segment.midpoint
      have middleInside : interval.Contains middle :=
        ⟨lastInside.1.trans segment.midpoint_contains.1, segment.midpoint_contains.2.trans firstInside.2⟩
      have lastMiddle : last ≤ middle := segment.midpoint_contains.1
      have middleFirst : middle ≤ first := segment.midpoint_contains.2
      have twiceMiddle : middle * 2 = last + first :=
        Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      have leftTwice : (first - middle) * 2 = first - last := by
        calc
          _ = first * 2 - middle * 2 := by ring1
          _ = _ := by rw [twiceMiddle]; ring1
      have rightEq : middle - last = first - middle := by
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = middle * 2 - last * 2 := by ring1
          _ = first - last := by rw [twiceMiddle]; ring1
          _ = _ := leftTwice.symm
      have halves : (first - middle) ^ 2 + (middle - last) ^ 2 ≤
          (2 / 3 : Fraction.Rational) * (first - last) ^ 2 := by
        apply Arithmetic.le_of_mul_le_mul_right_direct (c := 2) _ (by decide)
        calc
          _ = ((first - middle) * 2) ^ 2 := by rw [rightEq]; ring1
          _ = (first - last) ^ 2 := by rw [leftTwice]
          _ = 1 * (first - last) ^ 2 := by ring1
          _ ≤ ((2 / 3 : Fraction.Rational) * 2) * (first - last) ^ 2 :=
            Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide)
              (Arithmetic.sq_nonneg_direct _)
          _ = _ := by ring1
      have factorNonnegative : 0 ≤ remainder * (2 / 3 : Fraction.Rational) ^ depth :=
        Arithmetic.mul_nonneg_direct nonnegative
          (Arithmetic.pow_pos_direct (by decide) depth).le
      have cost := Arithmetic.mul_le_mul_of_nonneg_left_direct halves factorNonnegative
      have firstBound := inductionHypothesis firstInside middleInside middleFirst
      have secondBound := inductionHypothesis middleInside lastInside lastMiddle
      have combined := Arithmetic.add_le_add_direct firstBound secondBound
      have combinedIdentity : (value first - value middle) + (value middle - value last) =
          value first - value last := by ring1
      rw [combinedIdentity] at combined
      have estimate : linear * (first - last) -
          (remainder * (2 / 3 : Fraction.Rational) ^ depth) *
            ((first - middle) ^ 2 + (middle - last) ^ 2) ≤ value first - value last := by
        have identity : (linear * (first - middle) - remainder * (2 / 3 : Fraction.Rational) ^ depth *
            (first - middle) ^ 2) + (linear * (middle - last) -
              remainder * (2 / 3 : Fraction.Rational) ^ depth * (middle - last) ^ 2) =
            linear * (first - last) - (remainder * (2 / 3 : Fraction.Rational) ^ depth) *
              ((first - middle) ^ 2 + (middle - last) ^ 2) := by ring1
        rw [identity] at combined
        exact combined
      have lower := Arithmetic.sub_le_sub_left_direct cost (linear * (first - last))
      have bound := lower.trans estimate
      rw [pow_succ]
      have identity : linear * (first - last) - remainder * ((2 / 3 : Fraction.Rational) ^ depth * (2 / 3)) *
          (first - last) ^ 2 = linear * (first - last) -
            (remainder * (2 / 3 : Fraction.Rational) ^ depth) *
              ((2 / 3 : Fraction.Rational) * (first - last) ^ 2) := by ring1
      rw [identity]
      exact bound

/-- Finite midpoint subdivision removes a quadratic lower-increment remainder.

The local estimate holds on every ordered pair of rational points in the
retained interval. A positive separating gap determines one finite depth;
its contracted remainder contradicts that gap without selecting a limit. -/
theorem remove_quadratic (value : Fraction.Rational → Fraction.Rational) (interval : Purelib.Data.Rat.Interval)
    (linear remainder : Fraction.Rational) (nonnegative : 0 ≤ remainder)
    (localBound : ∀ {first last}, interval.Contains first → interval.Contains last → last ≤ first →
      linear * (first - last) - remainder * (first - last) ^ 2 ≤ value first - value last)
    {first last : Fraction.Rational} (firstInside : interval.Contains first)
    (lastInside : interval.Contains last) (ordered : last ≤ first) :
    linear * (first - last) ≤ value first - value last := by
  apply Arithmetic.le_of_not_gt_direct
  intro contrary
  let gap := linear * (first - last) - (value first - value last)
  have positive : 0 < gap := Arithmetic.sub_pos_direct contrary
  have scaleNonnegative : 0 ≤ remainder * (first - last) ^ 2 :=
    Arithmetic.mul_nonneg_direct nonnegative (Arithmetic.sq_nonneg_direct _)
  let depth := Contraction.geometricDepth (remainder * (first - last) ^ 2) (gap / 2)
  have small : (2 / 3 : Fraction.Rational) ^ depth * (remainder * (first - last) ^ 2) ≤ gap / 2 :=
    Contraction.geometricDepth_sufficient scaleNonnegative
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  have halfLt : gap / 2 < gap := Fraction.Order.Field.half_lt_self positive
  have approximation := at_depth value interval linear remainder nonnegative localBound depth
    firstInside lastInside ordered
  have lower := Arithmetic.sub_le_sub_left_direct small (linear * (first - last))
  have identity : linear * (first - last) - remainder * (2 / 3 : Fraction.Rational) ^ depth * (first - last) ^ 2 =
      linear * (first - last) - (2 / 3 : Fraction.Rational) ^ depth * (remainder * (first - last) ^ 2) := by ring1
  rw [identity] at approximation
  have gapBound := lower.trans approximation
  have impossible : linear * (first - last) - gap < linear * (first - last) - gap / 2 :=
    Arithmetic.sub_lt_sub_left_direct halfLt _
  have exactGap : linear * (first - last) - gap = value first - value last := by dsimp only [gap]; ring1
  rw [exactGap] at impossible
  exact (not_lt_of_ge gapBound) impossible

end Purelib.Approximation.Rational.Segment.Increment

end
