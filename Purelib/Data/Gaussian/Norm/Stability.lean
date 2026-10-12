module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Rational clearances for Gaussian quadrance

A positive rational margin gives an explicit positive squared-displacement
budget. Every displacement inside that budget changes the original
quadrance by less than the margin in either direction. The calculation uses
weighted two-term bounds and retains the original Gaussian value.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Stability

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Compute a squared-displacement budget for a prescribed quadrance margin.

The rational weight allocates half the margin to the original quadrance
and half to the displacement. Positivity requires only a positive margin.
-/
@[expose] def perturbationDistanceSq (center : Basic.Canonical)
    (margin : Fraction.Rational) : Fraction.Rational :=
  let weight := (margin / 2) / (1 + Norm.Basic.normSq center)
  (margin / 2) * weight / (1 + weight)

/-- A positive quadrance margin produces a positive displacement budget. -/
theorem perturbationDistanceSq_pos (center : Basic.Canonical)
    {margin : Fraction.Rational} (positive : 0 < margin) :
    0 < perturbationDistanceSq center margin := by
  have halfPositive := Fraction.Order.Field.div_pos_direct positive
    (by decide : (0 : Fraction.Rational) < 2)
  have denominatorPositive : 0 < 1 + Norm.Basic.normSq center :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg center))
  have weightPositive := Fraction.Order.Field.div_pos_direct
    halfPositive denominatorPositive
  unfold perturbationDistanceSq
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct halfPositive weightPositive)
    ((by decide : (0 : Fraction.Rational) < 1).trans_le
      (le_add_of_nonneg_right weightPositive.le))

/-- The weighted quadrance loss is strictly below its prescribed margin. -/
private theorem weighted_loss_lt {center displacement : Basic.Canonical}
    {margin : Fraction.Rational} (positive : 0 < margin)
    (small : Norm.Basic.normSq displacement < perturbationDistanceSq center margin) :
    let weight := (margin / 2) / (1 + Norm.Basic.normSq center)
    weight * Norm.Basic.normSq center +
      ((weight + 1) / weight) * Norm.Basic.normSq displacement < margin := by
  let weight := (margin / 2) / (1 + Norm.Basic.normSq center)
  have halfPositive := Fraction.Order.Field.div_pos_direct positive
    (by decide : (0 : Fraction.Rational) < 2)
  have denominatorPositive : 0 < 1 + Norm.Basic.normSq center :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg center))
  have weightPositive : 0 < weight :=
    Fraction.Order.Field.div_pos_direct halfPositive denominatorPositive
  have onePlusPositive : 0 < 1 + weight :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      (le_add_of_nonneg_right weightPositive.le)
  have baseline : weight * Norm.Basic.normSq center ≤ margin / 2 := by
    calc
      weight * Norm.Basic.normSq center ≤
          weight * (1 + Norm.Basic.normSq center) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (le_add_of_nonneg_left (by decide)) weightPositive.le
      _ = margin / 2 :=
        Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have scaled : Norm.Basic.normSq displacement * (1 + weight) <
      (margin / 2) * weight :=
    (Fraction.Order.Field.lt_div_iff_pos onePlusPositive).mp small
  have loss : ((weight + 1) / weight) * Norm.Basic.normSq displacement <
      margin / 2 := by
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := weight) _ weightPositive
    calc
      ((weight + 1) / weight) * Norm.Basic.normSq displacement * weight =
          ((weight + 1) / weight * weight) * Norm.Basic.normSq displacement := by ring1
      _ = (weight + 1) * Norm.Basic.normSq displacement := by
        rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ weightPositive.ne']
        rfl
      _ = Norm.Basic.normSq displacement * (1 + weight) := by ring1
      _ < (margin / 2) * weight := scaled
  calc
    weight * Norm.Basic.normSq center +
        ((weight + 1) / weight) * Norm.Basic.normSq displacement ≤
      margin / 2 + ((weight + 1) / weight) * Norm.Basic.normSq displacement :=
      Fraction.Order.Arithmetic.add_le_add_direct baseline (Fraction.Order.Basic.le_refl _)
    _ < margin / 2 + margin / 2 :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct loss _
    _ = (margin / 2) * 2 := by ring1
    _ = margin := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- A displacement inside the computed budget increases quadrance by less than the margin. -/
theorem normSq_add_lt_of_distance {center displacement : Basic.Canonical}
    {margin : Fraction.Rational} (positive : 0 < margin)
    (small : Norm.Basic.normSq displacement < perturbationDistanceSq center margin) :
    Norm.Basic.normSq (center + displacement) < Norm.Basic.normSq center + margin := by
  let weight := (margin / 2) / (1 + Norm.Basic.normSq center)
  have weightPositive : 0 < weight :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct positive (by decide))
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg center)))
  calc
    Norm.Basic.normSq (center + displacement) ≤
        (weight + 1) * Norm.Basic.normSq center +
          ((weight + 1) / weight) * Norm.Basic.normSq displacement :=
      Norm.Weighted.normSq_add_le_parameter weight weightPositive center displacement
    _ = Norm.Basic.normSq center +
        (weight * Norm.Basic.normSq center +
          ((weight + 1) / weight) * Norm.Basic.normSq displacement) := by ring1
    _ < Norm.Basic.normSq center + margin :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct (weighted_loss_lt positive small) _

/-- A displacement inside the computed budget decreases quadrance by less than the margin. -/
theorem normSq_lt_add_of_distance {center displacement : Basic.Canonical}
    {margin : Fraction.Rational} (positive : 0 < margin)
    (small : Norm.Basic.normSq displacement < perturbationDistanceSq center margin) :
    Norm.Basic.normSq center < Norm.Basic.normSq (center + displacement) + margin := by
  have oppositeSmall : Norm.Basic.normSq (-displacement) <
      perturbationDistanceSq center margin := by
    rewrite [Norm.Basic.normSq_neg]
    exact small
  have opposite := normSq_add_lt_of_distance positive oppositeSmall
  have differenceBound : Norm.Basic.normSq center - Norm.Basic.normSq (center + displacement) <
      margin := by
    calc
      Norm.Basic.normSq center - Norm.Basic.normSq (center + displacement) ≤
          Norm.Basic.normSq center - Norm.Basic.normSq (center + displacement) +
            2 * Norm.Basic.normSq displacement :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Norm.Basic.normSq_nonneg displacement))
      _ = Norm.Basic.normSq (center + -displacement) - Norm.Basic.normSq center := by
        simp only [Norm.Basic.normSq, Basic.add_re, Basic.add_im, Basic.neg_re, Basic.neg_im]
        ring1
      _ < margin := by
        have translated := Fraction.Order.Arithmetic.sub_lt_sub_right_direct opposite
          (Norm.Basic.normSq center)
        calc
          Norm.Basic.normSq (center + -displacement) - Norm.Basic.normSq center <
              (Norm.Basic.normSq center + margin) - Norm.Basic.normSq center := translated
          _ = margin := by ring1
  have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct differenceBound
    (Norm.Basic.normSq (center + displacement))
  calc
    Norm.Basic.normSq center =
        (Norm.Basic.normSq center - Norm.Basic.normSq (center + displacement)) +
          Norm.Basic.normSq (center + displacement) := by ring1
    _ < margin + Norm.Basic.normSq (center + displacement) := translated
    _ = Norm.Basic.normSq (center + displacement) + margin := by ring1

/-- Compute a parameter budget preserving a strict comparison of two affine Gaussian values.

Each original value pays half the quadrance gap. Its own retained direction
converts parameter quadrance into displacement quadrance, and the finite
minimum pays both budgets.
-/
@[expose] def affineComparisonDistanceSq (reference contender
    referenceDirection contenderDirection : Basic.Canonical) : Fraction.Rational :=
  let margin := (Norm.Basic.normSq contender - Norm.Basic.normSq reference) / 2
  min
    (perturbationDistanceSq reference margin / (1 + Norm.Basic.normSq referenceDirection))
    (perturbationDistanceSq contender margin / (1 + Norm.Basic.normSq contenderDirection))

/-- A strict original quadrance comparison gives a positive affine parameter budget. -/
theorem affineComparisonDistanceSq_pos {reference contender : Basic.Canonical}
    (referenceDirection contenderDirection : Basic.Canonical)
    (strict : Norm.Basic.normSq reference < Norm.Basic.normSq contender) :
    0 < affineComparisonDistanceSq reference contender referenceDirection contenderDirection := by
  let margin := (Norm.Basic.normSq contender - Norm.Basic.normSq reference) / 2
  have marginPositive : 0 < margin :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct strict) (by decide)
  have leftPositive : 0 < perturbationDistanceSq reference margin /
      (1 + Norm.Basic.normSq referenceDirection) :=
    Fraction.Order.Field.div_pos_direct (perturbationDistanceSq_pos reference marginPositive)
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg referenceDirection)))
  have rightPositive : 0 < perturbationDistanceSq contender margin /
      (1 + Norm.Basic.normSq contenderDirection) :=
    Fraction.Order.Field.div_pos_direct (perturbationDistanceSq_pos contender marginPositive)
      ((by decide : (0 : Fraction.Rational) < 1).trans_le
        (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg contenderDirection)))
  unfold affineComparisonDistanceSq
  by_cases ordered : perturbationDistanceSq reference margin /
      (1 + Norm.Basic.normSq referenceDirection) ≤
      perturbationDistanceSq contender margin / (1 + Norm.Basic.normSq contenderDirection)
  · rewrite [Fraction.Order.Basic.min_eq_left ordered]
    exact leftPositive
  · rewrite [Fraction.Order.Basic.min_eq_right
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct ordered).le]
    exact rightPositive

/-- Dividing a displacement budget by its retained directional factor pays the actual product displacement. -/
private theorem normSq_mul_lt_budget {parameter direction : Basic.Canonical}
    {budget : Fraction.Rational}
    (small : Norm.Basic.normSq parameter < budget / (1 + Norm.Basic.normSq direction)) :
    Norm.Basic.normSq (parameter * direction) < budget := by
  have denominatorPositive : 0 < 1 + Norm.Basic.normSq direction :=
    (by decide : (0 : Fraction.Rational) < 1).trans_le
      (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg direction))
  calc
    Norm.Basic.normSq (parameter * direction) =
        Norm.Basic.normSq parameter * Norm.Basic.normSq direction :=
      Norm.Basic.normSq_mul _ _
    _ ≤ Norm.Basic.normSq parameter * (1 + Norm.Basic.normSq direction) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_left (by decide)) (Norm.Basic.normSq_nonneg parameter)
    _ < budget := (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).mp small

/-- Every parameter inside the computed budget preserves the original affine quadrance comparison. -/
theorem normSq_affine_lt_of_distance {reference contender referenceDirection
    contenderDirection parameter : Basic.Canonical}
    (strict : Norm.Basic.normSq reference < Norm.Basic.normSq contender)
    (small : Norm.Basic.normSq parameter <
      affineComparisonDistanceSq reference contender referenceDirection contenderDirection) :
    Norm.Basic.normSq (reference + parameter * referenceDirection) <
      Norm.Basic.normSq (contender + parameter * contenderDirection) := by
  let margin := (Norm.Basic.normSq contender - Norm.Basic.normSq reference) / 2
  have marginPositive : 0 < margin :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct strict) (by decide)
  have referenceSmall : Norm.Basic.normSq (parameter * referenceDirection) <
      perturbationDistanceSq reference margin :=
    normSq_mul_lt_budget
      (small.trans_le (Fraction.Order.Basic.min_le_left _ _))
  have contenderSmall : Norm.Basic.normSq (parameter * contenderDirection) <
      perturbationDistanceSq contender margin :=
    normSq_mul_lt_budget
      (small.trans_le (Fraction.Order.Basic.min_le_right _ _))
  have twiceMargin : 2 * margin = Norm.Basic.normSq contender - Norm.Basic.normSq reference := by
    calc
      2 * margin = margin * 2 := by ring1
      _ = Norm.Basic.normSq contender - Norm.Basic.normSq reference :=
        Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have contenderBound := Fraction.Order.Arithmetic.sub_lt_sub_right_direct
    (normSq_lt_add_of_distance marginPositive contenderSmall) margin
  calc
    Norm.Basic.normSq (reference + parameter * referenceDirection) <
        Norm.Basic.normSq reference + margin :=
      normSq_add_lt_of_distance marginPositive referenceSmall
    _ = Norm.Basic.normSq reference + 2 * margin - margin := by ring1
    _ = Norm.Basic.normSq reference +
        (Norm.Basic.normSq contender - Norm.Basic.normSq reference) - margin := by
      rewrite [twiceMargin]
      rfl
    _ = Norm.Basic.normSq contender - margin := by ring1
    _ < (Norm.Basic.normSq (contender + parameter * contenderDirection) + margin) - margin :=
      contenderBound
    _ = Norm.Basic.normSq (contender + parameter * contenderDirection) := by ring1

end Purelib.Data.Gaussian.Norm.Stability
