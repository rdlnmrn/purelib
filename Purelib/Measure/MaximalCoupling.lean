module
import Purelib.Measure.Content.Histogram
import Purelib.Measure.Content.SignedDifference
public import Purelib.Measure.Content.Singularity
import Purelib.Measure.Coupling.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.SignedContent.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.PositiveNegativePart
import Purelib.Data.Bool.Relation
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Coupling.Law.Product
import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Consolidation

public import Purelib.Measure.Content.Overlap
import Purelib.Data.List.Event
import Purelib.Measure.Content.Lp.L2
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Explicit maximal couplings of finite rational laws

Two finite laws have a computable common part: at each consolidated payload,
retain the smaller singleton mass.  Subtracting that common part leaves two
nonnegative residual contents of equal total mass, namely total variation.
The positive-total case couples the common part diagonally and couples the
normalised residuals independently.  The zero case reuses observational
equivalence.  No optimisation or compactness argument is involved.
-/

namespace Purelib.Measure

section
open Purelib
open Purelib.Data.Rat
/-- Subtracting the minimum from the left scalar gives the positive part of the left-minus-right difference. -/
private theorem left_sub_min_eq_positiveWeight_sub
    (left right : Fraction.Rational) :
    left - min left right = Data.Rat.positiveWeight (left - right) := by
  by_cases order : left ≤ right
  · rw [Fraction.Order.Basic.min_eq_left order,
      Data.Rat.positiveWeight_eq_zero_of_nonpos (Fraction.Order.Boundary.sub_nonpositive_iff.mpr order)]
    ring1
  · have reverse : right ≤ left :=
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
    rw [Fraction.Order.Basic.min_eq_right reverse,
      Data.Rat.positiveWeight_eq_self_of_nonneg (Fraction.Order.Boundary.sub_nonnegative_iff.mpr reverse)]

/-- Subtracting the minimum from the right scalar gives the negative part of the left-minus-right difference. -/
private theorem right_sub_min_eq_negativeWeight_sub
    (left right : Fraction.Rational) :
    right - min left right = Data.Rat.negativeWeight (left - right) := by
  by_cases order : left ≤ right
  · rw [Fraction.Order.Basic.min_eq_left order,
      Data.Rat.negativeWeight_eq_neg_of_nonpos (Fraction.Order.Boundary.sub_nonpositive_iff.mpr order)]
    ring1
  · have reverse : right ≤ left :=
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
    rw [Fraction.Order.Basic.min_eq_right reverse,
      Data.Rat.negativeWeight_eq_zero_of_nonneg (Fraction.Order.Boundary.sub_nonnegative_iff.mpr reverse)]
    ring1

end

namespace Distribution

section
open Purelib
section
open Purelib.Measure
/-- Retain the two original laws' common singleton mass on their consolidated shared key list. -/
def overlapContent {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) : Measure.Content α :=
  Content.Overlap.overlapContent left.toContent right.toContent

/-- Retain the original left singleton masses after subtracting their exact common overlap with the right law. -/
def leftResidualContent {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) : Measure.Content α :=
  Content.Overlap.leftResidualContent left.toContent right.toContent

/-- Retain the original right singleton masses after subtracting their exact common overlap with the left law. -/
def rightResidualContent {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) : Measure.Content α :=
  Content.Overlap.rightResidualContent left.toContent right.toContent

end

section
open Purelib.Data.Rat
open Purelib.Measure
/-- The common-overlap integral plus the exact left-residual integral recovers the original left expectation. -/
theorem overlap_integral_add_leftResidual_integral {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    (left.overlapContent right).integral value +
        (left.leftResidualContent right).integral value =
      left.expectation value :=
  Content.Overlap.overlap_integral_add_leftResidual_integral left.toContent right.toContent value

/-- The common-overlap integral plus the exact right-residual integral recovers the original right expectation. -/
theorem overlap_integral_add_rightResidual_integral {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α)
    (value : α → Fraction.Rational) :
    (left.overlapContent right).integral value +
        (left.rightResidualContent right).integral value =
      right.expectation value :=
  Content.Overlap.overlap_integral_add_rightResidual_integral left.toContent right.toContent value

end

/-- Common-overlap mass plus left-residual mass equals one. -/
theorem overlap_total_add_leftResidual_total {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α) :
    (left.overlapContent right).total +
        (left.leftResidualContent right).total = 1 := by
  have identity := left.overlap_integral_add_leftResidual_integral right
    (fun _ => 1)
  rw [(left.overlapContent right).integral_constant,
    (left.leftResidualContent right).integral_constant,
    left.expectation_constant] at identity
  simpa only [mul_one] using identity

/-- Common-overlap mass plus right-residual mass equals one. -/
theorem overlap_total_add_rightResidual_total {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α) :
    (left.overlapContent right).total +
        (left.rightResidualContent right).total = 1 := by
  have identity := left.overlap_integral_add_rightResidual_integral right
    (fun _ => 1)
  rw [(left.overlapContent right).integral_constant,
    (left.rightResidualContent right).integral_constant,
    right.expectation_constant] at identity
  simpa only [mul_one] using identity

section
open Purelib.Data.Rat
open Purelib.Measure
/-- On the exact key list, left residual weight equals the positive singleton-difference weight. -/
private theorem totalWeight_leftResidual_eq_positiveDifference
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ keys : List (Weighted α),
      totalWeight (keys.map (Content.Overlap.leftResidualRow left.toContent right.toContent)) =
        totalWeight
          ((keys.map fun key =>
            { item := key.item
              weight := left.probability (atomEvent key.item) -
                right.probability (atomEvent key.item) : SignedWeighted α }).map
            fun atom =>
              { item := atom.item
                weight := Data.Rat.positiveWeight atom.weight
                nonnegative := Data.Rat.positiveWeight_nonneg atom.weight })
  | [] => rfl
  | key :: remaining => by
      change
        (left.probability (atomEvent key.item) -
          min (left.probability (atomEvent key.item))
            (right.probability (atomEvent key.item))) +
          totalWeight (remaining.map (Content.Overlap.leftResidualRow left.toContent right.toContent)) =
        Data.Rat.positiveWeight
          (left.probability (atomEvent key.item) -
            right.probability (atomEvent key.item)) + _
      exact congrArg₂ (fun first second : Fraction.Rational => first + second)
        (left_sub_min_eq_positiveWeight_sub _ _)
        (totalWeight_leftResidual_eq_positiveDifference left right remaining)

/-- On the exact key list, right residual weight equals the negative singleton-difference weight. -/
private theorem totalWeight_rightResidual_eq_negativeDifference
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ keys : List (Weighted α),
      totalWeight (keys.map (Content.Overlap.rightResidualRow left.toContent right.toContent)) =
        totalWeight
          ((keys.map fun key =>
            { item := key.item
              weight := left.probability (atomEvent key.item) -
              right.probability (atomEvent key.item) : SignedWeighted α }).map
            SignedContent.negativePartAtom)
  | [] => rfl
  | key :: remaining => by
      change
        (right.probability (atomEvent key.item) -
          min (left.probability (atomEvent key.item))
            (right.probability (atomEvent key.item))) +
          totalWeight (remaining.map (Content.Overlap.rightResidualRow left.toContent right.toContent)) =
        Data.Rat.negativeWeight
          (left.probability (atomEvent key.item) -
            right.probability (atomEvent key.item)) + _
      exact congrArg₂ (fun first second : Fraction.Rational => first + second)
        (right_sub_min_eq_negativeWeight_sub _ _)
        (totalWeight_rightResidual_eq_negativeDifference left right remaining)

end

section
open Purelib.Measure
/-- The exact left residual has total mass equal to the two original laws' total variation distance. -/
theorem leftResidual_total_eq_totalVariationDistance {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α) :
    (left.leftResidualContent right).total =
      left.totalVariationDistance right := by
  unfold leftResidualContent totalVariationDistance signedDifference
  unfold Content.Overlap.leftResidualContent
  unfold Content.signedDifference SignedContent.positiveContent
    Content.total
  exact totalWeight_leftResidual_eq_positiveDifference left right
    (left.toContent.radonNikodymKeys right.toContent)

/-- The exact right residual has total mass equal to the two original laws' total variation distance. -/
theorem rightResidual_total_eq_totalVariationDistance {α : Type}
    [DecidableEq α] (left right : Measure.Distribution α) :
    (left.rightResidualContent right).total =
      left.totalVariationDistance right := by
  calc
    (left.rightResidualContent right).total =
        (left.signedDifference right).negativeContent.total := by
      unfold rightResidualContent signedDifference
      unfold Content.Overlap.rightResidualContent
      unfold Content.signedDifference SignedContent.negativeContent
        Content.total
      exact totalWeight_rightResidual_eq_negativeDifference left right
        (left.toContent.radonNikodymKeys right.toContent)
    _ = (left.signedDifference right).positiveContent.total :=
      (left.signedDifference_positiveTotal_eq_negativeTotal right).symm
    _ = left.totalVariationDistance right := rfl

end

open Purelib.Data.Rat in
open Purelib.Measure in
/-- The left residual assigns zero mass outside the event where left singleton mass dominates right singleton mass. -/
private theorem leftResidual_complement_dominance_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ keys : List (Weighted α),
      eventWeight (keys.map (Content.Overlap.leftResidualRow left.toContent right.toContent))
        (complementEvent (left.totalVariationEvent right)) = 0
  | [] => rfl
  | key :: remaining => by
      by_cases order : right.probability (atomEvent key.item) ≤
          left.probability (atomEvent key.item)
      · have selected : left.totalVariationEvent right key.item = true := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = true
          exact decide_eq_true order
        change
          (match (complementEvent (left.totalVariationEvent right)) key.item with
            | true => left.probability (atomEvent key.item) -
                min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item))
            | false => 0) +
            eventWeight (remaining.map (Content.Overlap.leftResidualRow left.toContent right.toContent))
              (complementEvent (left.totalVariationEvent right)) = 0
        rw [leftResidual_complement_dominance_measure_eq_zero left right remaining]
        change (match Bool.not (left.totalVariationEvent right key.item) with
          | true => left.probability (atomEvent key.item) -
              min (left.probability (atomEvent key.item))
                (right.probability (atomEvent key.item))
          | false => 0) + 0 = 0
        rewrite [selected]
        change (0 : Fraction.Rational) + 0 = 0
        ring1
      · have reverse : left.probability (atomEvent key.item) ≤
            right.probability (atomEvent key.item) :=
          (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
        have unselected : left.totalVariationEvent right key.item = false := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = false
          exact decide_eq_false order
        change
          (match (complementEvent (left.totalVariationEvent right)) key.item with
            | true => left.probability (atomEvent key.item) -
                min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item))
            | false => 0) +
            eventWeight (remaining.map (Content.Overlap.leftResidualRow left.toContent right.toContent))
              (complementEvent (left.totalVariationEvent right)) = 0
        rw [leftResidual_complement_dominance_measure_eq_zero left right remaining]
        change (match Bool.not (left.totalVariationEvent right key.item) with
          | true => left.probability (atomEvent key.item) -
              min (left.probability (atomEvent key.item))
                (right.probability (atomEvent key.item))
          | false => 0) + 0 = 0
        rewrite [unselected, Fraction.Order.Basic.min_eq_left reverse]
        change (left.probability (atomEvent key.item) -
          left.probability (atomEvent key.item)) + 0 = 0
        ring1

open Purelib.Measure in
open Purelib.Data.Rat in
/-- The right residual assigns zero mass inside the event where left singleton mass dominates right singleton mass. -/
private theorem rightResidual_dominance_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ∀ keys : List (Weighted α),
      eventWeight (keys.map (Content.Overlap.rightResidualRow left.toContent right.toContent))
        (left.totalVariationEvent right) = 0
  | [] => rfl
  | key :: remaining => by
      by_cases order : right.probability (atomEvent key.item) ≤
          left.probability (atomEvent key.item)
      · have selected : left.totalVariationEvent right key.item = true := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = true
          exact decide_eq_true order
        change
          (match (left.totalVariationEvent right) key.item with
            | true => right.probability (atomEvent key.item) -
                min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item))
            | false => 0) +
            eventWeight (remaining.map (Content.Overlap.rightResidualRow left.toContent right.toContent))
              (left.totalVariationEvent right) = 0
        rw [rightResidual_dominance_measure_eq_zero left right remaining]
        rewrite [selected, Fraction.Order.Basic.min_eq_right order]
        ring1
      · have unselected : left.totalVariationEvent right key.item = false := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = false
          exact decide_eq_false order
        change
          (match (left.totalVariationEvent right) key.item with
            | true => right.probability (atomEvent key.item) -
                min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item))
            | false => 0) +
            eventWeight (remaining.map (Content.Overlap.rightResidualRow left.toContent right.toContent))
              (left.totalVariationEvent right) = 0
        rw [rightResidual_dominance_measure_eq_zero left right remaining]
        rewrite [unselected]
        change (0 : Fraction.Rational) + 0 = 0
        ring1

open Purelib.Measure in
/-- Separate the exact residual contents using the original singleton-mass dominance event.

The retained left residual vanishes outside that event and the retained right residual vanishes inside it. -/
def residualContents_mutuallySingular {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) :
    Content.MutuallySingular
      (left.leftResidualContent right)
      (left.rightResidualContent right) where
  separator := left.totalVariationEvent right
  left_outside_zero := by
    unfold leftResidualContent Content.measure
    unfold Content.Overlap.leftResidualContent
    exact leftResidual_complement_dominance_measure_eq_zero left right
      (left.toContent.radonNikodymKeys right.toContent)
  right_inside_zero := by
    unfold rightResidualContent Content.measure
    unfold Content.Overlap.rightResidualContent
    exact rightResidual_dominance_measure_eq_zero left right
      (left.toContent.radonNikodymKeys right.toContent)

end

end Distribution

namespace Content.MutuallySingular

open Purelib in
open Purelib.Data.Rat in
/-- The product of two explicitly separated contents assigns zero mass to equal-coordinate pairs. -/
theorem product_equality_measure_eq_zero {α : Type} [DecidableEq α]
    {left right : Measure.Content α}
    (singular : Content.MutuallySingular left right) :
    (left.product right).measure
        (fun pair => LawCoupling.equalityRelation pair.1 pair.2) = 0 := by
  let leftBad : α × α → Bool := fun pair =>
    complementEvent singular.separator pair.1
  let rightBad : α × α → Bool := fun pair =>
    singular.separator pair.2
  have equalityImpliesBad : EventImpliesOn (left.product right).atoms
      (fun pair => LawCoupling.equalityRelation pair.1 pair.2)
      (unionEvent leftBad rightBad) := by
    intro atom member selected
    have same : atom.item.1 = atom.item.2 := by
      unfold LawCoupling.equalityRelation at selected
      exact of_decide_eq_true selected
    cases separatorSelected : singular.separator atom.item.1
    · simp only [unionEvent, leftBad, complementEvent, separatorSelected,
        Bool.not_false, Bool.true_or, -eq_self, -iff_self]
      rfl
    · have rightSelected : singular.separator atom.item.2 = true := by
        rw [← same]
        exact separatorSelected
      simp only [unionEvent, rightBad, rightSelected, Bool.or_true, -eq_self, -iff_self]
      rfl
  have leftBadMeasure : (left.product right).measure leftBad = 0 := by
    calc
      (left.product right).measure leftBad =
          (left.product right).measure (fun pair =>
            complementEvent singular.separator pair.1 &&
              (fun _ => true) pair.2) :=
        (left.product right).measure_congr _ _ (fun pair => by
          simp only [leftBad, Bool.and_true, -eq_self, -iff_self]
          rfl)
      _ =
          left.measure (complementEvent singular.separator) *
            right.measure (fun _ => true) :=
        left.product_measure_rectangle right
          (complementEvent singular.separator) (fun _ => true)
      _ = 0 := by rw [singular.left_outside_zero, zero_mul]
  have rightBadMeasure : (left.product right).measure rightBad = 0 := by
    calc
      (left.product right).measure rightBad =
          (left.product right).measure (fun pair =>
            (fun _ => true) pair.1 && singular.separator pair.2) :=
        (left.product right).measure_congr _ _ (fun pair => by
          simp only [rightBad, Bool.true_and, -eq_self, -iff_self]
          rfl)
      _ =
          left.measure (fun _ => true) *
            right.measure singular.separator :=
        left.product_measure_rectangle right (fun _ => true)
          singular.separator
      _ = 0 := by rw [singular.right_inside_zero, mul_zero]
  have equalityLeUnion := (left.product right).mono equalityImpliesBad
  have unionLe := eventWeight_union_le_add (left.product right).atoms
    leftBad rightBad
  change (left.product right).measure (unionEvent leftBad rightBad) ≤
    (left.product right).measure leftBad +
      (left.product right).measure rightBad at unionLe
  rw [leftBadMeasure, rightBadMeasure, zero_add] at unionLe
  exact Fraction.Order.Basic.Compatibility.le_antisymm _ _
    (equalityLeUnion.trans unionLe)
    ((left.product right).measure_nonneg _)

end Content.MutuallySingular

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
open Purelib.Measure
/-- Join the diagonal common overlap to the scaled product of the two exact residual contents when total variation is
positive.

The shared overlap comparison supplies all three retained contents. Dividing the residual product by the positive total
variation normalizes its contribution without changing either original law. -/
def positiveMaximalJointContent {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    Measure.Content (α × α) :=
  let comparison := Content.Overlap.Comparison.realize left.toContent right.toContent
  (comparison.common.map fun item => (item, item)).append
    ((comparison.leftResidual.product comparison.rightResidual).scale
      (1 / left.totalVariationDistance right)
      (Fraction.Order.Field.div_nonneg_direct (by decide) positive.le))

/-- Read back the retained positive-distance construction as diagonal overlap plus the scaled original residual product.
-/
theorem positiveMaximalJointContent_readback {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) (positive : 0 < left.totalVariationDistance right) :
    left.positiveMaximalJointContent right positive =
      ((left.overlapContent right).map fun item => (item, item)).append
        (((left.leftResidualContent right).product (left.rightResidualContent right)).scale
          (1 / left.totalVariationDistance right)
          (Fraction.Order.Field.div_nonneg_direct (by decide) positive.le)) := by
  let comparison := Content.Overlap.Comparison.realize left.toContent right.toContent
  change (comparison.common.map fun item => (item, item)).append
    ((comparison.leftResidual.product comparison.rightResidual).scale
      (1 / left.totalVariationDistance right)
      (Fraction.Order.Field.div_nonneg_direct (by decide) positive.le)) = _
  rw [comparison.common_eq, comparison.leftResidual_eq, comparison.rightResidual_eq]
  rfl

end

open Purelib.Data.Rat in
/-- For nonzero rational value, its reciprocal times its square equals that original value. -/
private theorem inverse_mul_self_mul_self
    (value : Fraction.Rational) (nonzero : value ≠ 0) :
    (1 / value) * (value * value) = value := by
  calc
    (1 / value) * (value * value) =
        ((1 / value) * value) * value := by ring1
    _ = 1 * value :=
      congrArg (fun factor => factor * value)
        (Fraction.Field.div_mul_cancel_of_ne 1 value nonzero)
    _ = value := Fraction.Field.one_mul value

section
open Purelib
/-- The overlap-plus-scaled-residual construction has total mass one for positive total variation. -/
theorem positiveMaximalJointContent_total {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalJointContent right positive).total = 1 := by
  rw [positiveMaximalJointContent_readback]
  rw [Content.append_total, Content.map_total,
    Content.scale_total, Content.product_total,
    left.leftResidual_total_eq_totalVariationDistance right,
    left.rightResidual_total_eq_totalVariationDistance right,
    inverse_mul_self_mul_self _ positive.ne']
  have overlap := left.overlap_total_add_leftResidual_total right
  rw [left.leftResidual_total_eq_totalVariationDistance right] at overlap
  exact overlap

/-- Package the exact positive-distance joint content as a normalized finite joint distribution. -/
def positiveMaximalJoint {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    Measure.Distribution (α × α) where
  atoms := (left.positiveMaximalJointContent right positive).atoms
  total_one := left.positiveMaximalJointContent_total right positive

section
open Purelib.Data.Rat
/-- The scaled residual product's left-coordinate integral equals the original left-residual integral. -/
private theorem scaled_residualProduct_integral_fst
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Fraction.Rational) :
    ((((left.leftResidualContent right).product
        (left.rightResidualContent right)).scale
          (1 / left.totalVariationDistance right)
          (Fraction.Order.Field.div_nonneg_direct
            (by decide) positive.le)).integral fun pair => value pair.1) =
      (left.leftResidualContent right).integral value := by
  rw [Content.scale_integral]
  have productIntegral :
      ((left.leftResidualContent right).product
          (left.rightResidualContent right)).integral
          (fun pair => value pair.1) =
        (left.leftResidualContent right).integral value *
          (left.rightResidualContent right).total := by
    calc
      ((left.leftResidualContent right).product
            (left.rightResidualContent right)).integral
            (fun pair => value pair.1) =
          ((left.leftResidualContent right).product
            (left.rightResidualContent right)).integral
            (fun pair => value pair.1 * (fun _ => 1) pair.2) :=
        ((left.leftResidualContent right).product
          (left.rightResidualContent right)).integral_congr _ _
            (fun pair => by ring1)
      _ = (left.leftResidualContent right).integral value *
          (left.rightResidualContent right).integral (fun _ => 1) :=
        (left.leftResidualContent right).product_integral_mul
          (left.rightResidualContent right) value (fun _ => 1)
      _ = (left.leftResidualContent right).integral value *
          (left.rightResidualContent right).total := by
        rw [(left.rightResidualContent right).integral_constant]
        ring1
  rw [productIntegral,
    left.rightResidual_total_eq_totalVariationDistance right]
  calc
    (1 / left.totalVariationDistance right) *
          ((left.leftResidualContent right).integral value *
            left.totalVariationDistance right) =
        (left.leftResidualContent right).integral value *
          ((1 / left.totalVariationDistance right) *
            left.totalVariationDistance right) := by ring1
    _ = (left.leftResidualContent right).integral value * 1 := by
      exact congrArg
        (fun factor =>
          (left.leftResidualContent right).integral value * factor)
        (Fraction.Field.div_mul_cancel_of_ne 1
          (left.totalVariationDistance right) positive.ne')
    _ = (left.leftResidualContent right).integral value := by ring1

/-- The scaled residual product's right-coordinate integral equals the original right-residual integral. -/
private theorem scaled_residualProduct_integral_snd
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Fraction.Rational) :
    ((((left.leftResidualContent right).product
        (left.rightResidualContent right)).scale
          (1 / left.totalVariationDistance right)
          (Fraction.Order.Field.div_nonneg_direct
            (by decide) positive.le)).integral fun pair => value pair.2) =
      (left.rightResidualContent right).integral value := by
  rw [Content.scale_integral]
  have productIntegral :
      ((left.leftResidualContent right).product
          (left.rightResidualContent right)).integral
          (fun pair => value pair.2) =
        (left.leftResidualContent right).total *
          (left.rightResidualContent right).integral value := by
    calc
      ((left.leftResidualContent right).product
            (left.rightResidualContent right)).integral
            (fun pair => value pair.2) =
          ((left.leftResidualContent right).product
            (left.rightResidualContent right)).integral
            (fun pair => (fun _ => 1) pair.1 * value pair.2) :=
        ((left.leftResidualContent right).product
          (left.rightResidualContent right)).integral_congr _ _
            (fun pair => by ring1)
      _ = (left.leftResidualContent right).integral (fun _ => 1) *
          (left.rightResidualContent right).integral value :=
        (left.leftResidualContent right).product_integral_mul
          (left.rightResidualContent right) (fun _ => 1) value
      _ = (left.leftResidualContent right).total *
          (left.rightResidualContent right).integral value := by
        rw [(left.leftResidualContent right).integral_constant]
        ring1
  rw [productIntegral,
    left.leftResidual_total_eq_totalVariationDistance right]
  calc
    (1 / left.totalVariationDistance right) *
          (left.totalVariationDistance right *
            (left.rightResidualContent right).integral value) =
        ((1 / left.totalVariationDistance right) *
          left.totalVariationDistance right) *
            (left.rightResidualContent right).integral value := by ring1
    _ = 1 * (left.rightResidualContent right).integral value := by
      exact congrArg
        (fun factor =>
          factor * (left.rightResidualContent right).integral value)
        (Fraction.Field.div_mul_cancel_of_ne 1
          (left.totalVariationDistance right) positive.ne')
    _ = (left.rightResidualContent right).integral value := by ring1

/-- The positive-distance joint distribution recovers the original left expectation on left-coordinate observables. -/
theorem positiveMaximalJoint_expectation_fst
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Fraction.Rational) :
    (left.positiveMaximalJoint right positive).expectation
        (fun pair => value pair.1) = left.expectation value := by
  change (left.positiveMaximalJointContent right positive).integral
      (fun pair => value pair.1) = left.expectation value
  rw [positiveMaximalJointContent_readback]
  rw [Content.append_integral, Content.map_integral,
    left.scaled_residualProduct_integral_fst right positive value]
  exact left.overlap_integral_add_leftResidual_integral right value

/-- The positive-distance joint distribution recovers the original right expectation on right-coordinate observables. -/
theorem positiveMaximalJoint_expectation_snd
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Fraction.Rational) :
    (left.positiveMaximalJoint right positive).expectation
        (fun pair => value pair.2) = right.expectation value := by
  change (left.positiveMaximalJointContent right positive).integral
      (fun pair => value pair.2) = right.expectation value
  rw [positiveMaximalJointContent_readback]
  rw [Content.append_integral, Content.map_integral,
    left.scaled_residualProduct_integral_snd right positive value]
  exact left.overlap_integral_add_rightResidual_integral right value

end

/-- Retain the normalized overlap-and-residual joint distribution as a coupling at positive total variation. -/
def positiveMaximalCoupling {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) : Coupling α α where
  joint := left.positiveMaximalJoint right positive

/-- Certify the positive-distance coupling's exact original left and right marginal laws.

The stored evaluation identities follow from the retained joint distribution's coordinate expectations; no replacement
marginal lists are introduced. -/
def positiveMaximalLawCoupling {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    LawCoupling left right where
  coupling := left.positiveMaximalCoupling right positive
  leftEquivalent := by
    apply EvaluationEquivalent.of_expectation_eq
    intro value
    unfold Coupling.leftMarginal positiveMaximalCoupling
    rw [Distribution.map_expectation]
    exact left.positiveMaximalJoint_expectation_fst right positive value
  rightEquivalent := by
    apply EvaluationEquivalent.of_expectation_eq
    intro value
    unfold Coupling.rightMarginal positiveMaximalCoupling
    rw [Distribution.map_expectation]
    exact left.positiveMaximalJoint_expectation_snd right positive value

/-- The diagonal copy of the exact common overlap assigns zero mass to unequal-coordinate pairs. -/
private theorem diagonalOverlap_mismatch_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ((left.overlapContent right).map fun item => (item, item)).measure
        (Coupling.mismatchEvent LawCoupling.equalityRelation) = 0 := by
  rw [Content.map_measure]
  calc
    (left.overlapContent right).measure (fun item : α =>
        Coupling.mismatchEvent LawCoupling.equalityRelation (item, item)) =
        (left.overlapContent right).measure (fun _ => false) :=
      (left.overlapContent right).measure_congr _ _ (fun item => by
        change Bool.not (decide (item = item)) = false
        rewrite [decide_eq_true (rfl : item = item)]
        rfl)
    _ = 0 := (left.overlapContent right).measure_empty

/-- All mass of the mutually singular residual product lies on unequal-coordinate pairs. -/
private theorem residualProduct_mismatch_measure_eq_total
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    ((left.leftResidualContent right).product
        (left.rightResidualContent right)).measure
        (Coupling.mismatchEvent LawCoupling.equalityRelation) =
      ((left.leftResidualContent right).product
        (left.rightResidualContent right)).total := by
  let product := (left.leftResidualContent right).product
    (left.rightResidualContent right)
  let equalityEvent : α × α → Bool := fun pair =>
    LawCoupling.equalityRelation pair.1 pair.2
  have equalityZero : product.measure equalityEvent = 0 := by
    exact Content.MutuallySingular.product_equality_measure_eq_zero
      (left.residualContents_mutuallySingular right)
  have complementMass := product.add_complement equalityEvent
  rw [equalityZero, zero_add] at complementMass
  have same : Coupling.mismatchEvent LawCoupling.equalityRelation =
      complementEvent equalityEvent := rfl
  rw [same]
  exact complementMass

/-- The positive-distance joint distribution's equality mismatch equals the original total variation distance. -/
theorem positiveMaximalJoint_mismatchProbability
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalJoint right positive).probability
        (Coupling.mismatchEvent LawCoupling.equalityRelation) =
      left.totalVariationDistance right := by
  change (left.positiveMaximalJointContent right positive).measure
      (Coupling.mismatchEvent LawCoupling.equalityRelation) =
    left.totalVariationDistance right
  rw [positiveMaximalJointContent_readback]
  rw [Content.append_measure,
    diagonalOverlap_mismatch_measure_eq_zero,
    Content.scale_measure,
    residualProduct_mismatch_measure_eq_total,
    Content.product_total,
    left.leftResidual_total_eq_totalVariationDistance right,
    left.rightResidual_total_eq_totalVariationDistance right,
    inverse_mul_self_mul_self _ positive.ne', zero_add]

/-- The certified positive-distance law coupling attains total variation as its equality-mismatch probability. -/
theorem positiveMaximalLawCoupling_mismatchProbability
    {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalLawCoupling right positive).mismatchProbability
        LawCoupling.equalityRelation =
      left.totalVariationDistance right := by
  unfold LawCoupling.mismatchProbability positiveMaximalLawCoupling
    positiveMaximalCoupling Coupling.mismatchProbability
  exact left.positiveMaximalJoint_mismatchProbability right positive

/-- Construct a coupling of the exact laws attaining their total variation as equality mismatch.

Use the left identity coupling when total variation is zero, transporting its right-law certificate. Otherwise retain
diagonal overlap and the scaled product of the two original residual contents. -/
def maximalLawCoupling {α : Type} [DecidableEq α]
    (left right : Measure.Distribution α) : LawCoupling left right := by
  by_cases zero : left.totalVariationDistance right = 0
  · let diagonal := LawCoupling.refl left
    have equivalent : EvaluationEquivalent left right :=
      (left.totalVariationDistance_eq_zero_iff_evaluationEquivalent right).mp
        zero
    exact
      { coupling := diagonal.coupling
        leftEquivalent := diagonal.leftEquivalent
        rightEquivalent := diagonal.rightEquivalent.trans equivalent }
  · have positive : 0 < left.totalVariationDistance right :=
      lt_of_le_of_ne (left.totalVariationDistance_nonnegative right)
        (Ne.symm zero)
    exact left.positiveMaximalLawCoupling right positive

/-- The constructed maximal law coupling has equality-mismatch probability exactly equal to the original total variation
distance. -/
theorem maximalLawCoupling_mismatchProbability
    {α : Type} [DecidableEq α] (left right : Measure.Distribution α) :
    (left.maximalLawCoupling right).mismatchProbability
        LawCoupling.equalityRelation =
      left.totalVariationDistance right := by
  by_cases zero : left.totalVariationDistance right = 0
  · unfold maximalLawCoupling
    rewrite [dif_pos zero, zero]
    change (LawCoupling.refl left).mismatchProbability
      LawCoupling.equalityRelation = 0
    exact LawCoupling.refl_mismatchProbability_eq_zero left
  · have positive : 0 < left.totalVariationDistance right :=
      lt_of_le_of_ne (left.totalVariationDistance_nonnegative right)
        (Ne.symm zero)
    unfold maximalLawCoupling
    rewrite [dif_neg zero]
    exact left.positiveMaximalLawCoupling_mismatchProbability right positive

end

end Distribution

end Purelib.Measure
