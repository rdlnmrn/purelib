module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Geometry.Gaussian.UnitCircle.Quarter
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Finite variation of the actual rational annular phase

The four original quarter formulas include their actual cardinal joins.
The retained weighted norm inequality joins their displacement estimates
with the same density 64. No additive or reflected-phase law is used.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

/-- Each original affine quarter has squared variation density 64. -/
private theorem chart_distance (quarter : UnitCircuitQuarter) (offset left right : Fraction.Rational) :
    Norm.Basic.normSq ((Waist.direction quarter (4 * left - offset)).value -
      (Waist.direction quarter (4 * right - offset)).value) ≤ 64 * (right - left) ^ 2 := by
  have difference : (Waist.direction quarter (4 * left - offset)).value -
      (Waist.direction quarter (4 * right - offset)).value =
      Quarter.unitCircuitMultiplier quarter *
        (Stereographic.unitQuarterPoint (4 * left - offset) -
          Stereographic.unitQuarterPoint (4 * right - offset)) := by
    rewrite [Waist.direction_value, Waist.direction_value]
    ring1
  rewrite [difference, Norm.Basic.normSq_mul, Quarter.unitCircuitMultiplier_unit, Fraction.Field.one_mul]
  exact (Stereographic.unitQuarterPoint_distance_le (4 * left - offset) (4 * right - offset)).trans_eq
    (by ring1)

/-- Two actual ordered phase displacements join with the same weighted density. -/
private theorem join_distance (firstValue middleValue lastValue : Canonical)
    (left middle right : Fraction.Rational)
    (first : left ≤ middle) (last : middle ≤ right)
    (before : Norm.Basic.normSq (firstValue - middleValue) ≤ 64 * (middle - left) ^ 2)
    (after : Norm.Basic.normSq (middleValue - lastValue) ≤ 64 * (right - middle) ^ 2) :
    Norm.Basic.normSq (firstValue - lastValue) ≤ 64 * (right - left) ^ 2 := by
  have result := Norm.Weighted.normSq_add_weighted
    (x := firstValue - middleValue) (y := middleValue - lastValue)
    (density := 64) (a := middle - left) (b := right - middle)
    (Fraction.Order.Arithmetic.sub_nonneg_direct first)
    (Fraction.Order.Arithmetic.sub_nonneg_direct last) before after
  have same : (firstValue - middleValue) + (middleValue - lastValue) =
      firstValue - lastValue := by ring1
  have paid := (congrArg Norm.Basic.normSq same).symm.trans_le result
  exact paid.trans_eq (by ring1)

/-- Reversing an arbitrary Gaussian displacement retains the same time-square bound. -/
private theorem reverse_distance (firstValue lastValue : Canonical)
    (left right : Fraction.Rational)
    (bound : Norm.Basic.normSq (lastValue - firstValue) ≤ 64 * (left - right) ^ 2) :
    Norm.Basic.normSq (firstValue - lastValue) ≤ 64 * (right - left) ^ 2 :=
  (Norm.Bounds.normSq_sub_symm firstValue lastValue).trans_le (bound.trans_eq (by ring1))

/-- Ordered bounds on two actual adjoining phase intervals bound their union. -/
private theorem join_interval (lower middle upper : Fraction.Rational)
    (before : ∀ left right, lower ≤ left → right ≤ middle → left ≤ right →
      Norm.Basic.normSq ((phase left).value - (phase right).value) ≤ 64 * (right - left) ^ 2)
    (after : ∀ left right, middle ≤ left → right ≤ upper → left ≤ right →
      Norm.Basic.normSq ((phase left).value - (phase right).value) ≤ 64 * (right - left) ^ 2)
    (left right : Fraction.Rational) (first : lower ≤ left) (last : right ≤ upper) (ordered : left ≤ right) :
    Norm.Basic.normSq ((phase left).value - (phase right).value) ≤ 64 * (right - left) ^ 2 := by
  by_cases rightBefore : right ≤ middle
  · exact before left right first rightBefore ordered
  · by_cases leftBefore : left ≤ middle
    · have rightAfter := (Fraction.Order.Basic.le_total middle right).resolve_right rightBefore
      exact join_distance (phase left).value (phase middle).value (phase right).value
        left middle right leftBefore rightAfter
        (before left middle first (Fraction.Order.Basic.le_refl _) leftBefore)
        (after middle right (Fraction.Order.Basic.le_refl _) last rightAfter)
    · exact after left right
        ((Fraction.Order.Basic.le_total middle left).resolve_right leftBefore) last ordered

/-- The actual four joined quarters have density 64 between ordered unit-interval times. -/
private theorem ordered_distance (left right : Fraction.Rational)
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1) (ordered : left ≤ right) :
    Norm.Basic.normSq ((phase left).value - (phase right).value) ≤ 64 * (right - left) ^ 2 := by
  have first (a b : Fraction.Rational) (_lower : 0 ≤ a) (upper : b ≤ 1 / 4) (order : a ≤ b) :
      Norm.Basic.normSq ((phase a).value - (phase b).value) ≤ 64 * (b - a) ^ 2 := by
    rewrite [phase_first_chart a (order.trans upper), phase_first_chart b upper]
    have actual := chart_distance .first 0 a b
    have noOffset (time : Fraction.Rational) : 4 * time - 0 = 4 * time := by ring1
    rewrite [noOffset a, noOffset b] at actual
    exact actual
  have second (a b : Fraction.Rational) (lower : 1 / 4 ≤ a) (upper : b ≤ 1 / 2) (order : a ≤ b) :
      Norm.Basic.normSq ((phase a).value - (phase b).value) ≤ 64 * (b - a) ^ 2 := by
    rewrite [phase_second_chart a ⟨lower, order.trans upper⟩, phase_second_chart b ⟨lower.trans order, upper⟩]
    exact chart_distance .second 1 a b
  have third (a b : Fraction.Rational) (lower : 1 / 2 ≤ a) (upper : b ≤ 3 / 4) (order : a ≤ b) :
      Norm.Basic.normSq ((phase a).value - (phase b).value) ≤ 64 * (b - a) ^ 2 := by
    rewrite [phase_third_chart a ⟨lower, order.trans upper⟩, phase_third_chart b ⟨lower.trans order, upper⟩]
    exact chart_distance .third 2 a b
  have fourth (a b : Fraction.Rational) (lower : 3 / 4 ≤ a) (upper : b ≤ 1) (order : a ≤ b) :
      Norm.Basic.normSq ((phase a).value - (phase b).value) ≤ 64 * (b - a) ^ 2 := by
    rewrite [phase_fourth_chart a ⟨lower, order.trans upper⟩, phase_fourth_chart b ⟨lower.trans order, upper⟩]
    exact chart_distance .fourth 3 a b
  have half := join_interval 0 (1 / 4) (1 / 2) first second
  have three := join_interval 0 (1 / 2) (3 / 4) half third
  exact join_interval 0 (3 / 4) 1 three fourth left right leftInside.1 rightInside.2 ordered

public section

/-- The actual joined rational unit phase has global squared variation density 64.

All four original charts and their actual cardinal seams contribute to this
bound. Reversal changes only the displayed difference orientation; neither
phase additivity nor a reflected-parameter identity is assumed.
-/
theorem phase_distance_le (left right : Fraction.Rational)
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1) :
    Norm.Basic.normSq ((phase left).value - (phase right).value) ≤ 64 * (right - left) ^ 2 := by
  rcases Fraction.Order.Basic.le_total left right with ordered | reversed
  · exact ordered_distance left right leftInside rightInside ordered
  · exact reverse_distance (phase left).value (phase right).value left right
      (ordered_distance right left rightInside leftInside reversed)

/-- The square of the actual joined phase has finite squared variation density 384. -/
theorem phase_square_distance_le (left right : Fraction.Rational)
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1) :
    Norm.Basic.normSq ((phase left).value ^ 2 - (phase right).value ^ 2) ≤ 384 * (right - left) ^ 2 := by
  have sensitivity := Norm.Power.difference_normSq_le (phase left).unit.le (phase right).unit.le 2
  rewrite [show Norm.Power.differenceFactor 1 2 = 6 by decide +kernel] at sensitivity
  exact (sensitivity.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (phase_distance_le left right leftInside rightInside) (by decide +kernel))).trans_eq (by ring1)

/-- The conjugated square uses the same actual phase variation and the same finite density. -/
theorem phase_conjugate_square_distance_le (left right : Fraction.Rational)
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1) :
    Norm.Basic.normSq (Basic.conj (phase left).value ^ 2 - Basic.conj (phase right).value ^ 2) ≤
      384 * (right - left) ^ 2 := by
  have first : Norm.Basic.normSq (Basic.conj (phase left).value) ≤ 1 := by
    rewrite [Norm.Basic.normSq_conj, (phase left).unit]
    exact Fraction.Order.Basic.le_refl _
  have last : Norm.Basic.normSq (Basic.conj (phase right).value) ≤ 1 := by
    rewrite [Norm.Basic.normSq_conj, (phase right).unit]
    exact Fraction.Order.Basic.le_refl _
  have sensitivity := Norm.Power.difference_normSq_le first last 2
  rewrite [show Norm.Power.differenceFactor 1 2 = 6 by decide +kernel] at sensitivity
  have same : Norm.Basic.normSq (Basic.conj (phase left).value - Basic.conj (phase right).value) =
      Norm.Basic.normSq ((phase left).value - (phase right).value) :=
    (congrArg Norm.Basic.normSq (Canonical.conj_sub _ _)).symm.trans (Norm.Basic.normSq_conj _)
  have original := sensitivity.trans_eq (congrArg (fun value : Fraction.Rational => 6 * value) same)
  exact (original.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (phase_distance_le left right leftInside rightInside) (by decide +kernel))).trans_eq (by ring1)

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist
