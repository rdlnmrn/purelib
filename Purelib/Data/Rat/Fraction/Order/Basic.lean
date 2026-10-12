module
public import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Rat.Fraction

import Mathlib.Algebra.Order.Ring.Defs

import Mathlib.Order.Defs.LinearOrder
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

public section

/-!
# Casts and order for canonical fractions

Natural and integer casts are related directly to denominator-one canonical
records.  Weak order is sign-safe cross multiplication; strict order is its
constructive asymmetric part and is proved equivalent to strict integer
cross multiplication.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data

namespace Order.Basic

/-- Compare canonical rationals by integer cross-products of their positive-denominator records. -/
@[expose] def LessEqual (left right : Rational) : Prop :=
  left.num * (right.den : Int) ≤ right.num * (left.den : Int)

/-- Use the concrete integer cross-product comparison as canonical rational weak order. -/
instance instLE : LE Rational := ⟨LessEqual⟩

/-- Use weak comparison and failure of reverse comparison as canonical rational strict order. -/
instance instLT : LT Rational :=
  ⟨fun left right => left ≤ right ∧ ¬right ≤ left⟩

/-- Decide canonical rational weak order by the retained integer cross-products. -/
instance instDecidableLE : DecidableLE Rational := fun left right =>
  inferInstanceAs (Decidable
    (left.num * (right.den : Int) ≤ right.num * (left.den : Int)))

/-- Decide strict rational order by its concrete asymmetric weak comparisons. -/
instance instDecidableLT : DecidableLT Rational := fun left right =>
  inferInstanceAs (Decidable (left ≤ right ∧ ¬right ≤ left))

/-- A canonical rational is weakly bounded by itself. -/
theorem le_refl (source : Rational) : source ≤ source :=
  Int.Order.le_refl _

/-- Weak rational bounds compose through their retained positive denominators.

Cross multiplication by the outer denominators preserves each integer bound.
Cancelling the shared positive middle denominator gives the resulting bound. -/
theorem le_trans (first second third : Rational)
    (firstSecond : first ≤ second) (secondThird : second ≤ third) :
    first ≤ third := by
  apply Int.Order.int_le_of_mul_le_mul_right
    (Int.Order.natCast_pos second.den_pos)
  have thirdDenominatorNonnegative : 0 ≤ (third.den : Int) :=
    Int.natCast_nonneg _
  have firstDenominatorNonnegative : 0 ≤ (first.den : Int) :=
    Int.natCast_nonneg _
  have firstScaled :=
    Int.Order.mul_le_mul_of_nonneg_right firstSecond thirdDenominatorNonnegative
  have secondScaled :=
    Int.Order.mul_le_mul_of_nonneg_right secondThird firstDenominatorNonnegative
  change
    (first.num * (third.den : Int)) * (second.den : Int) ≤
      (third.num * (first.den : Int)) * (second.den : Int)
  calc
    (first.num * (third.den : Int)) * (second.den : Int) =
        (first.num * (second.den : Int)) * (third.den : Int) := by ring1
    _ ≤ (third.num * (first.den : Int)) * (second.den : Int) := by
      have middle : (second.num * (first.den : Int)) * (third.den : Int) =
          (second.num * (third.den : Int)) * (first.den : Int) := by ring1
      have final : (third.num * (second.den : Int)) * (first.den : Int) =
          (third.num * (first.den : Int)) * (second.den : Int) := by ring1
      rw [middle] at firstScaled
      rw [final] at secondScaled
      exact Int.Order.le_trans firstScaled secondScaled

/-- Opposite weak bounds identify the canonical rational records.

Antisymmetry of the displayed integer cross products gives their equivalence,
and canonical fraction uniqueness identifies the retained records. -/
theorem le_antisymm (left right : Rational)
    (leftRight : left ≤ right) (rightLeft : right ≤ left) : left = right :=
  eq_of_cross (Int.Order.le_antisymm leftRight rightLeft)

/-- Equip the concrete rational cross-product relation with reflexivity, transitivity and antisymmetry. -/
instance instPartialOrder : PartialOrder Rational where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

/-- Any two canonical rationals are weakly ordered in one direction. -/
theorem le_total (left right : Rational) : left ≤ right ∨ right ≤ left :=
  Int.Order.le_total (left.num * (right.den : Int))
    (right.num * (left.den : Int))

/-- Select the smaller canonical rational using the decidable weak order. -/
instance instMin : Min Rational := minOfLe
/-- Select the larger canonical rational using the decidable weak order. -/
instance instMax : Max Rational := maxOfLe
/-- Compare canonical rationals using their strict comparison and structural equality. -/
instance instOrd : Ord Rational :=
  ⟨fun left right => compareOfLessAndEq left right⟩

/-- Equip canonical rational records with their executable total cross-product order.

The order is built directly from stored numerator/denominator cross-products and the existing structural equality
decision, retaining executable minimum, maximum and comparison. -/
instance instLinearOrder : LinearOrder Rational where
  le_total := le_total
  toDecidableLE := instDecidableLE
  toDecidableEq := inferInstance
  toDecidableLT := instDecidableLT
  compare_eq_compareOfLessAndEq := by intros; rfl

end Order.Basic
/-- Return the greater of a canonical rational and its negation.

The absolute value uses the original decidable cross order, maximum and
negation operations. It retains the same canonical rational carrier and
display selected by that comparison. -/
@[expose] def abs (source : Rational) : Rational :=
  max source (-source)

namespace Order.Basic

/-- Strict order is strict integer cross multiplication. -/
theorem lt_iff_cross (left right : Rational) :
    left < right ↔
      left.num * (right.den : Int) < right.num * (left.den : Int) :=
  by
    change
      (left.num * (right.den : Int) ≤ right.num * (left.den : Int) ∧
        ¬right.num * (left.den : Int) ≤ left.num * (right.den : Int)) ↔ _
    exact Int.Order.lt_iff_le_and_not_ge.symm

/-- The sign of a canonical rational is the sign of its stored numerator. -/
theorem zero_lt_iff_num_pos (source : Rational) :
    0 < source ↔ 0 < source.num := by
  constructor
  · intro positive
    have cross := (lt_iff_cross 0 source).mp positive
    change (0 : Int) * (source.den : Int) < source.num * 1 at cross
    rw [Int.Arithmetic.zero_mul, Int.Arithmetic.mul_one] at cross
    exact cross
  · intro positive
    apply (lt_iff_cross 0 source).mpr
    change (0 : Int) * (source.den : Int) < source.num * 1
    rw [Int.Arithmetic.zero_mul, Int.Arithmetic.mul_one]
    exact positive

/-- Equivalent positive-denominator displays have numerators with the same strict sign.

Both denominators are strictly positive. Their cross-product equality therefore
preserves and reflects strict positivity of the integer numerators. -/
theorem numerator_pos_iff_of_equivalent {left right : RawFraction}
    (equivalent : Equivalent left right) :
    0 < left.num ↔ 0 < right.num := by
  constructor
  · intro leftPositive
    have productPositive :
        0 < left.num * (right.den : Int) :=
      Int.Order.mul_pos leftPositive (Int.Order.natCast_pos right.den_pos)
    rw [equivalent] at productPositive
    exact Int.Order.pos_of_mul_pos_left productPositive
      (Int.Order.natCast_pos left.den_pos)
  · intro rightPositive
    have productPositive :
        0 < right.num * (left.den : Int) :=
      Int.Order.mul_pos rightPositive (Int.Order.natCast_pos left.den_pos)
    rw [← equivalent] at productPositive
    exact Int.Order.pos_of_mul_pos_left productPositive
      (Int.Order.natCast_pos right.den_pos)

/-- The concrete strict order is exactly positivity of the explicit difference.

The original positive denominators identify strict cross-product order with the
sign of the explicit subtraction numerator. -/
theorem lt_iff_zero_lt_sub (left right : Rational) :
    left < right ↔ 0 < right - left := by
  have differenceDisplay := add_equivalent right (-left)
  have numeratorSigns :
      0 < (right - left).num ↔
        0 < right.num * (left.den : Int) + (-left.num) * (right.den : Int) :=
    numerator_pos_iff_of_equivalent differenceDisplay
  have differenceSigns :
      left.num * (right.den : Int) < right.num * (left.den : Int) ↔
        0 < right.num * (left.den : Int) + (-left.num) * (right.den : Int) := by
    constructor
    · intro strict
      have positive := Int.Order.sub_pos.mpr strict
      rw [Int.sub_eq_add_neg, ← Int.Arithmetic.neg_mul] at positive
      exact positive
    · intro positive
      apply Int.Order.sub_pos.mp
      rw [Int.sub_eq_add_neg, ← Int.Arithmetic.neg_mul]
      exact positive
  exact (lt_iff_cross left right).trans
    (differenceSigns.trans
      (numeratorSigns.symm.trans (zero_lt_iff_num_pos (right - left)).symm))

end Order.Basic
end Purelib.Data.Rat.Fraction

end

public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Order.Basic.Compatibility

/-- Mutual weak comparisons identify the exact canonical rational records. -/
theorem le_antisymm (a b : Fraction.Rational) (hab : a ≤ b)
  (hba : b ≤ a) : a = b :=
  _root_.Purelib.Data.Rat.Fraction.Order.Basic.le_antisymm a b hab hba

/-- Compose two weak comparisons of canonical rationals. -/
theorem le_trans (a b c : Fraction.Rational) (hab : a ≤ b)
  (hbc : b ≤ c) : a ≤ c :=
  _root_.Purelib.Data.Rat.Fraction.Order.Basic.le_trans a b c hab hbc
end Purelib.Data.Rat.Fraction.Order.Basic.Compatibility

end

namespace Purelib.Data.Rat.Fraction.Order.Basic

/-- The canonical rational minimum does not exceed its left argument.

The retained decidable comparison chooses either input. Totality supplies
the reverse comparison when the left input is not below the right. -/
public theorem min_le_left (left right : Rational) : min left right ≤ left := by
  change (if left ≤ right then left else right) ≤ left
  by_cases forward : left ≤ right
  · rw [if_pos forward]
  · rw [if_neg forward]
    cases le_total left right with
    | inl bound => exact (forward bound).elim
    | inr reverse => exact reverse

/-- The canonical rational minimum does not exceed its right argument.

The retained comparison chooses the left input when it is bounded by the
right; otherwise the minimum is the right input itself. -/
public theorem min_le_right (left right : Rational) : min left right ≤ right := by
  change (if left ≤ right then left else right) ≤ right
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact forward
  · rw [if_neg forward]

/-- A weakly smaller left rational is the retained minimum.

The canonical decidable comparison selects the same supplied left value;
its weak comparison is the exact condition for that branch.
-/
public theorem min_eq_left {left right : Rational} (forward : left ≤ right) :
    min left right = left := by
  change (if left ≤ right then left else right) = left
  rw [if_pos forward]

/-- A weakly smaller right rational is the retained minimum.

If the comparison selects the left value, both supplied inequalities
identify the two rationals. Otherwise the retained branch is the right value.
-/
public theorem min_eq_right {left right : Rational} (reverse : right ≤ left) :
    min left right = right := by
  change (if left ≤ right then left else right) = right
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact le_antisymm left right forward reverse
  · rw [if_neg forward]

/-- A common weak rational lower bound is below the retained minimum.

The unchanged decidable comparison selects one of the two original inputs.
Its supplied lower bound gives the same comparison with the retained result. -/
public theorem le_min {lower left right : Rational}
    (leftBound : lower ≤ left) (rightBound : lower ≤ right) :
    lower ≤ min left right := by
  change lower ≤ if left ≤ right then left else right
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact leftBound
  · rw [if_neg forward]
    exact rightBound

/-- Increasing both rational inputs increases their retained minimum weakly.

The original lower minimum bounds each of its inputs. Composing these bounds
with the supplied input comparisons bounds the unchanged upper minimum. -/
public theorem min_le_min {left₁ right₁ left₂ right₂ : Rational}
    (leftBound : left₁ ≤ left₂) (rightBound : right₁ ≤ right₂) :
    min left₁ right₁ ≤ min left₂ right₂ :=
  le_min
    (le_trans _ _ _ (min_le_left _ _) leftBound)
    (le_trans _ _ _ (min_le_right _ _) rightBound)

/-- A common strict rational lower bound is below the retained minimum.

The retained minimum selects one of the original inputs; its supplied
strict lower bound applies in that same comparison branch. -/
public theorem lt_min {lower left right : Rational}
    (leftBound : lower < left) (rightBound : lower < right) :
    lower < min left right := by
  change lower < if left ≤ right then left else right
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact leftBound
  · rw [if_neg forward]
    exact rightBound

/-- The left canonical rational argument does not exceed the retained maximum.

The retained comparison chooses the right input when it bounds the left;
otherwise the maximum is the left input itself. -/
public theorem le_max_left (left right : Rational) : left ≤ max left right := by
  change left ≤ if left ≤ right then right else left
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact forward
  · rw [if_neg forward]

/-- The right canonical rational argument does not exceed the retained maximum.

The retained comparison selects either input. Totality gives the reverse
comparison when the left input is not below the right. -/
public theorem le_max_right (left right : Rational) : right ≤ max left right := by
  change right ≤ if left ≤ right then right else left
  by_cases forward : left ≤ right
  · rw [if_pos forward]
  · rw [if_neg forward]
    cases le_total left right with
    | inl bound => exact (forward bound).elim
    | inr reverse => exact reverse

/-- Bounding both canonical rational inputs bounds their retained maximum.

The maximum selects one original input by its decidable weak comparison;
the corresponding supplied bound proves the result. -/
public theorem max_le {left right upper : Rational}
    (leftBound : left ≤ upper) (rightBound : right ≤ upper) :
    max left right ≤ upper := by
  change (if left ≤ right then right else left) ≤ upper
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact rightBound
  · rw [if_neg forward]
    exact leftBound

/-- A common strict upper bound bounds the retained rational maximum.

The decidable weak comparison selects one of the two unchanged inputs.
Its supplied strict upper bound applies in that same retained branch. -/
public theorem max_lt {left right upper : Rational}
    (leftBound : left < upper) (rightBound : right < upper) :
    max left right < upper := by
  change (if left ≤ right then right else left) < upper
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact rightBound
  · rw [if_neg forward]
    exact leftBound

/-- A weakly smaller right input leaves the canonical rational maximum at the left.

The retained comparison either selects the left input immediately or proves
both input bounds. Antisymmetry identifies the selected right input in the latter case. -/
public theorem max_eq_left {left right : Rational} (reverse : right ≤ left) :
    max left right = left := by
  change (if left ≤ right then right else left) = left
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    exact (le_antisymm left right forward reverse).symm
  · rw [if_neg forward]

/-- A weakly smaller left input leaves the canonical rational maximum at the right.

The supplied weak comparison selects the right argument in the original
decidable-comparison branch of the maximum operation. -/
public theorem max_eq_right {left right : Rational} (forward : left ≤ right) :
    max left right = right := by
  change (if left ≤ right then right else left) = right
  rw [if_pos forward]

/-- The retained maximum of a canonical rational with itself is that rational.

Reflexivity selects the right occurrence of the same retained rational
in the original comparison branch of the maximum operation. -/
public theorem max_self (value : Rational) : max value value = value :=
  max_eq_right (le_refl value)

/-- Swapping the canonical rational inputs preserves their retained maximum.

Both input values bound the swapped maximum from below. Applying the
maximum bound in each direction and antisymmetry identifies the two results. -/
public theorem max_comm (left right : Rational) : max left right = max right left :=
  le_antisymm _ _
    (max_le (le_max_right right left) (le_max_left right left))
    (max_le (le_max_right left right) (le_max_left left right))

/-- Reassociating three canonical rational arguments preserves their retained maximum.

Each input bounds either nested maximum from below. The common upper bounds
and antisymmetry identify the two results of the original comparison operation. -/
public theorem max_assoc (first second third : Rational) :
    max (max first second) third = max first (max second third) := by
  apply le_antisymm
  · apply max_le
    · apply max_le
      · exact le_max_left _ _
      · exact le_trans _ _ _ (le_max_left second third) (le_max_right _ _)
    · exact le_trans _ _ _ (le_max_right second third) (le_max_right _ _)
  · apply max_le
    · exact le_trans _ _ _ (le_max_left first second) (le_max_left _ _)
    · apply max_le
      · exact le_trans _ _ _ (le_max_right first second) (le_max_left _ _)
      · exact le_max_right _ _

end Purelib.Data.Rat.Fraction.Order.Basic
