module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Exact rational separation

The separation of two rational endpoints is the maximum of their two directed
differences. Finite scalar order and arithmetic give its symmetry, triangle
bounds and compatibility with rational translation and scaling.
-/

public section

namespace Purelib.Data.Rat.Distance

open Fraction.Order

/-- Compute the exact rational distance as the maximum of the two directed differences.

Both directed differences are computed in the canonical rational carrier; the larger is nonnegative and vanishes exactly
when the endpoints agree. This definition needs no real-valued distance or completion. -/
@[expose] def rationalSeparation (left right : Fraction.Rational) : Fraction.Rational :=
  max (left - right) (right - left)

/-- Exchanging the endpoints preserves rational separation.

The two directed differences exchange places. Commutativity of the retained
canonical rational maximum identifies the resulting values. -/
theorem rationalSeparation_symm (left right : Fraction.Rational) :
    Distance.rationalSeparation left right = Distance.rationalSeparation right left := by
  unfold Distance.rationalSeparation
  exact Basic.max_comm _ _

/-- The exact rational separation is nonnegative.

Total order makes one of the two directed differences nonnegative.
That same difference is bounded above by the retained rational maximum. -/
theorem rationalSeparation_nonneg (left right : Fraction.Rational) :
    0 ≤ Distance.rationalSeparation left right := by
  by_cases order : left ≤ right
  · exact (Arithmetic.sub_nonneg_direct order).trans
      (Basic.le_max_right _ _)
  · have reverse : right ≤ left :=
      (Arithmetic.lt_of_not_ge_direct order).le
    exact (Arithmetic.sub_nonneg_direct reverse).trans
      (Basic.le_max_left _ _)

/-- Rational separation satisfies the triangle inequality through any middle rational.

Each directed endpoint difference decomposes through the displayed middle
point. The two retained maxima bound the corresponding directed summands. -/
theorem rationalSeparation_triangle
    (left middle right : Fraction.Rational) :
    Distance.rationalSeparation left right ≤
      Distance.rationalSeparation left middle + Distance.rationalSeparation middle right := by
  apply Basic.max_le
  · calc
      left - right = (left - middle) + (middle - right) := by ring1
      _ ≤ Distance.rationalSeparation left middle +
          Distance.rationalSeparation middle right :=
        add_le_add (Basic.le_max_left _ _) (Basic.le_max_left _ _)
  · calc
      right - left = (middle - left) + (right - middle) := by ring1
      _ ≤ Distance.rationalSeparation left middle +
          Distance.rationalSeparation middle right :=
        add_le_add (Basic.le_max_right _ _) (Basic.le_max_right _ _)

/-- The separation between two sums is bounded by the sum of their component separations.

Each directed sum difference is the sum of its two component differences.
Their retained maxima bound both directions and hence bound the resulting maximum. -/
theorem rationalSeparation_add_le
    (leftFirst leftSecond rightFirst rightSecond : Fraction.Rational) :
    Distance.rationalSeparation (leftFirst + leftSecond) (rightFirst + rightSecond) ≤
      Distance.rationalSeparation leftFirst rightFirst +
        Distance.rationalSeparation leftSecond rightSecond := by
  apply Basic.max_le
  · calc
      leftFirst + leftSecond - (rightFirst + rightSecond) =
          (leftFirst - rightFirst) + (leftSecond - rightSecond) := by ring1
      _ ≤ Distance.rationalSeparation leftFirst rightFirst +
          Distance.rationalSeparation leftSecond rightSecond :=
        add_le_add (Basic.le_max_left _ _) (Basic.le_max_left _ _)
  · calc
      rightFirst + rightSecond - (leftFirst + leftSecond) =
          (rightFirst - leftFirst) + (rightSecond - leftSecond) := by ring1
      _ ≤ Distance.rationalSeparation leftFirst rightFirst +
          Distance.rationalSeparation leftSecond rightSecond :=
        add_le_add (Basic.le_max_right _ _) (Basic.le_max_right _ _)

/-- Negating both endpoints preserves rational separation. -/
theorem rationalSeparation_neg (left right : Fraction.Rational) :
    Distance.rationalSeparation (-left) (-right) =
      Distance.rationalSeparation left right := by
  unfold Distance.rationalSeparation
  calc
    max (-left - -right) (-right - -left) =
        max (right - left) (left - right) := by
      congr 1 <;> ring1
    _ = max (left - right) (right - left) := Basic.max_comm _ _

/-- The separation between two differences is bounded by the sum of their component separations. -/
theorem rationalSeparation_sub_le
    (leftFirst leftSecond rightFirst rightSecond : Fraction.Rational) :
    Distance.rationalSeparation (leftFirst - leftSecond)
        (rightFirst - rightSecond) ≤
      Distance.rationalSeparation leftFirst rightFirst +
        Distance.rationalSeparation leftSecond rightSecond := by
  change Distance.rationalSeparation (leftFirst + -leftSecond)
      (rightFirst + -rightSecond) ≤
    Distance.rationalSeparation leftFirst rightFirst +
      Distance.rationalSeparation leftSecond rightSecond
  calc
    Distance.rationalSeparation (leftFirst + -leftSecond)
        (rightFirst + -rightSecond) ≤
      Distance.rationalSeparation leftFirst rightFirst +
        Distance.rationalSeparation (-leftSecond) (-rightSecond) :=
      Distance.rationalSeparation_add_le _ _ _ _
    _ = Distance.rationalSeparation leftFirst rightFirst +
        Distance.rationalSeparation leftSecond rightSecond := by
      rw [Distance.rationalSeparation_neg]

/-- Separation of two rationals equals separation of their difference from zero. -/
theorem rationalSeparation_eq_sub_zero
    (left right : Fraction.Rational) :
    Distance.rationalSeparation left right =
      Distance.rationalSeparation (left - right) 0 := by
  unfold Distance.rationalSeparation
  congr 1 <;> ring1

/-- The separation of a nonnegative rational from zero is that rational.

The supplied nonnegative bound places the negated value below the original
value. The retained maximum of the two directed differences selects that value. -/
theorem rationalSeparation_zero_of_nonneg
    {value : Fraction.Rational} (nonnegative : 0 ≤ value) :
    Distance.rationalSeparation value 0 = value := by
  unfold Distance.rationalSeparation
  calc
    max (value - 0) (0 - value) = value - 0 := by
      apply Basic.max_eq_left
      calc
        0 - value = -value := by ring1
        _ ≤ value := Arithmetic.neg_le_self_of_nonnegative nonnegative
        _ = value - 0 := by ring1
    _ = value := by ring1

/-- The separation of a nonpositive rational from zero is its negation.

The supplied nonpositive bound places the original value below its negation.
The retained maximum of the two directed differences selects the negated value. -/
theorem rationalSeparation_zero_of_nonpos
    {value : Fraction.Rational} (nonpositive : value ≤ 0) :
    Distance.rationalSeparation value 0 = -value := by
  unfold Distance.rationalSeparation
  have negated := Arithmetic.neg_le_neg_direct nonpositive
  have negativeNonnegative : 0 ≤ -value := by
    calc
      0 = -(0 : Fraction.Rational) := by ring1
      _ ≤ -value := negated
  calc
    max (value - 0) (0 - value) = 0 - value := by
      apply Basic.max_eq_right
      calc
        value - 0 = value := by ring1
        _ ≤ 0 := nonpositive
        _ ≤ -value := negativeNonnegative
        _ = 0 - value := by ring1
    _ = -value := by ring1

/-- The distance of a sum from zero is at most the sum of the component distances from zero.

The two directed differences of the sum decompose into component differences.
The corresponding retained maxima bound each summand in both directions. -/
theorem rationalSeparation_add_zero_le (left right : Fraction.Rational) :
    Distance.rationalSeparation (left + right) 0 ≤
      Distance.rationalSeparation left 0 + Distance.rationalSeparation right 0 := by
  apply Basic.max_le
  · calc
      left + right - 0 = (left - 0) + (right - 0) := by ring1
      _ ≤ Distance.rationalSeparation left 0 + Distance.rationalSeparation right 0 :=
        add_le_add (Basic.le_max_left _ _) (Basic.le_max_left _ _)
  · calc
      0 - (left + right) = (0 - left) + (0 - right) := by ring1
      _ ≤ Distance.rationalSeparation left 0 + Distance.rationalSeparation right 0 :=
        add_le_add (Basic.le_max_right _ _) (Basic.le_max_right _ _)

/-- The distance of a product from zero is the product of the component distances from zero.

The four sign cases use the supplied rational weak order and multiplier
bounds. Each retained distance selects its original value or its negation
according to that sign, giving the displayed product identity. -/
theorem rationalSeparation_mul_zero (left right : Fraction.Rational) :
    Distance.rationalSeparation (left * right) 0 =
      Distance.rationalSeparation left 0 * Distance.rationalSeparation right 0 := by
  by_cases leftNonnegative : 0 ≤ left
  · by_cases rightNonnegative : 0 ≤ right
    · have productNonnegative :=
        Arithmetic.mul_nonneg_direct
          leftNonnegative rightNonnegative
      rw [Distance.rationalSeparation_zero_of_nonneg productNonnegative,
        Distance.rationalSeparation_zero_of_nonneg leftNonnegative,
        Distance.rationalSeparation_zero_of_nonneg rightNonnegative]
    · have rightNonpositive : right ≤ 0 :=
        (Arithmetic.lt_of_not_ge_direct
          rightNonnegative).le
      have productNonpositive : left * right ≤ 0 := by
        calc
          left * right ≤ left * 0 :=
            Arithmetic.mul_le_mul_of_nonneg_left_direct
              rightNonpositive leftNonnegative
          _ = 0 := by ring1
      rw [Distance.rationalSeparation_zero_of_nonpos productNonpositive,
        Distance.rationalSeparation_zero_of_nonneg leftNonnegative,
        Distance.rationalSeparation_zero_of_nonpos rightNonpositive]
      ring1
  · have leftNonpositive : left ≤ 0 :=
      (Arithmetic.lt_of_not_ge_direct leftNonnegative).le
    by_cases rightNonnegative : 0 ≤ right
    · have productNonpositive : left * right ≤ 0 := by
        calc
          left * right ≤ 0 * right :=
            Arithmetic.mul_le_mul_of_nonneg_right_direct
              leftNonpositive rightNonnegative
          _ = 0 := by ring1
      rw [Distance.rationalSeparation_zero_of_nonpos productNonpositive,
        Distance.rationalSeparation_zero_of_nonpos leftNonpositive,
        Distance.rationalSeparation_zero_of_nonneg rightNonnegative]
      ring1
    · have rightNonpositive : right ≤ 0 :=
        (Arithmetic.lt_of_not_ge_direct
          rightNonnegative).le
      have productNonnegative : 0 ≤ left * right :=
        Arithmetic.product_nonnegative_of_both_nonpositive
          leftNonpositive rightNonpositive
      rw [Distance.rationalSeparation_zero_of_nonneg productNonnegative,
        Distance.rationalSeparation_zero_of_nonpos leftNonpositive,
        Distance.rationalSeparation_zero_of_nonpos rightNonpositive]
      ring1

/-- Scaling both endpoints multiplies their separation by the scalar's distance from zero. -/
theorem rationalSeparation_scale (factor left right : Fraction.Rational) :
    Distance.rationalSeparation (factor * left) (factor * right) =
      Distance.rationalSeparation factor 0 * Distance.rationalSeparation left right := by
  calc
    Distance.rationalSeparation (factor * left) (factor * right) =
        Distance.rationalSeparation (factor * left - factor * right) 0 :=
      Distance.rationalSeparation_eq_sub_zero _ _
    _ = Distance.rationalSeparation (factor * (left - right)) 0 := by
      congr 1
      ring1
    _ = Distance.rationalSeparation factor 0 * Distance.rationalSeparation (left - right) 0 :=
      Distance.rationalSeparation_mul_zero factor (left - right)
    _ = Distance.rationalSeparation factor 0 * Distance.rationalSeparation left right := by
      exact congrArg (fun magnitude => Distance.rationalSeparation factor 0 * magnitude)
        (Distance.rationalSeparation_eq_sub_zero left right).symm

/-- Two rationals have zero separation exactly when they are equal.

A zero retained maximum bounds both directed differences by zero. Scalar
translation gives opposite endpoint bounds, so antisymmetry identifies
the endpoints; identical endpoints give two zero differences. -/
theorem rationalSeparation_eq_zero_iff (left right : Fraction.Rational) :
    Distance.rationalSeparation left right = 0 ↔ left = right := by
  constructor
  · intro zero
    have leftRight : left - right ≤ 0 :=
      (Basic.le_max_left (left - right) (right - left)).trans_eq zero
    have rightLeft : right - left ≤ 0 :=
      (Basic.le_max_right (left - right) (right - left)).trans_eq zero
    have leftLeRight : left ≤ right := by
      have translated := Arithmetic.add_le_add_right_direct leftRight right
      calc
        left = (left - right) + right := by ring1
        _ ≤ 0 + right := translated
        _ = right := by ring1
    have rightLeLeft : right ≤ left := by
      have translated := Arithmetic.add_le_add_right_direct rightLeft left
      calc
        right = (right - left) + left := by ring1
        _ ≤ 0 + left := translated
        _ = left := by ring1
    exact Basic.Compatibility.le_antisymm _ _ leftLeRight rightLeLeft
  · intro same
    subst right
    unfold Distance.rationalSeparation
    calc
      max (left - left) (left - left) = max (0 : Fraction.Rational) 0 :=
        congrArg₂ max (by ring1) (by ring1)
      _ = 0 := Basic.max_self 0

/-- For increasing endpoints, rational separation is the right endpoint minus the left.

The supplied endpoint comparison makes the right-minus-left difference
nonnegative and the opposite difference nonpositive. The retained maximum
therefore selects the right-minus-left difference. -/
theorem rationalSeparation_eq_right_sub_of_le
    {left right : Fraction.Rational} (order : left ≤ right) :
    Distance.rationalSeparation left right = right - left := by
  unfold Distance.rationalSeparation
  apply Basic.max_eq_right
  calc
    left - right ≤ right - right :=
      Arithmetic.sub_le_sub_right_direct order right
    _ = 0 := by ring1
    _ ≤ right - left :=
      Arithmetic.sub_nonneg_direct order

/-- For decreasing endpoints, rational separation is the left endpoint minus the right. -/
theorem rationalSeparation_eq_left_sub_of_le
    {left right : Fraction.Rational} (order : right ≤ left) :
    Distance.rationalSeparation left right = left - right := by
  rw [Distance.rationalSeparation_symm,
    Distance.rationalSeparation_eq_right_sub_of_le order]

/-- Subtracting the same rational from both endpoints preserves separation. -/
theorem rationalSeparation_sub_same_right
    (left right shift : Fraction.Rational) :
    Distance.rationalSeparation (left - shift) (right - shift) =
      Distance.rationalSeparation left right := by
  unfold Distance.rationalSeparation
  congr 1 <;> ring1

/-- Subtracting both endpoints from a common anchor preserves their separation.

The common anchor cancels from each directed difference, reversing their
order. Commutativity of the retained maximum identifies the resulting separation. -/
theorem rationalSeparation_same_left_sub
    (anchor left right : Fraction.Rational) :
    Distance.rationalSeparation (anchor - left) (anchor - right) =
      Distance.rationalSeparation left right := by
  unfold Distance.rationalSeparation
  rw [Basic.max_comm]
  congr 1 <;> ring1

end Purelib.Data.Rat.Distance
