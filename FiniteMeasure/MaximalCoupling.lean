import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.TotalVariationDistance
import FiniteMeasure.Family
import FiniteMeasure.Singularity

/-!
# Explicit maximal couplings of finite rational laws

Two finite laws have a computable common part: at each consolidated payload,
retain the smaller singleton mass.  Subtracting that common part leaves two
nonnegative residual contents of equal total mass, namely total variation.
The positive-total case couples the common part diagonally and couples the
normalised residuals independently.  The zero case reuses observational
equivalence.  No optimisation or compactness argument is involved.
-/

namespace FiniteMeasure

private theorem left_sub_min_eq_positiveWeight_sub
    (left right : Coordinate) :
    left - min left right = positiveWeight (left - right) := by
  by_cases order : left ≤ right
  · rw [min_eq_left order,
      positiveWeight_eq_zero_of_nonpos (sub_nonpos.mpr order)]
    ring1
  · have reverse : right ≤ left :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
    rw [min_eq_right reverse,
      positiveWeight_eq_self_of_nonneg (sub_nonneg.mpr reverse)]

private theorem right_sub_min_eq_negativeWeight_sub
    (left right : Coordinate) :
    right - min left right = negativeWeight (left - right) := by
  by_cases order : left ≤ right
  · rw [min_eq_left order,
      negativeWeight_eq_neg_of_nonpos (sub_nonpos.mpr order)]
    ring1
  · have reverse : right ≤ left :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
    rw [min_eq_right reverse,
      negativeWeight_eq_zero_of_nonneg (sub_nonneg.mpr reverse)]
    ring1

namespace Distribution

private def overlapRow {α : Type} [DecidableEq α]
    (left right : Distribution α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := min
    (left.probability (atomEvent key.item))
    (right.probability (atomEvent key.item))
  nonnegative := le_min
    (left.probability_nonneg (atomEvent key.item))
    (right.probability_nonneg (atomEvent key.item))

private def leftResidualRow {α : Type} [DecidableEq α]
    (left right : Distribution α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := left.probability (atomEvent key.item) - min
    (left.probability (atomEvent key.item))
    (right.probability (atomEvent key.item))
  nonnegative := sub_nonneg.mpr (min_le_left _ _)

private def rightResidualRow {α : Type} [DecidableEq α]
    (left right : Distribution α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := right.probability (atomEvent key.item) - min
    (left.probability (atomEvent key.item))
    (right.probability (atomEvent key.item))
  nonnegative := sub_nonneg.mpr (min_le_right _ _)

/-- The singletonwise overlap of two finite laws. -/
def overlapContent {α : Type} [DecidableEq α]
    (left right : Distribution α) : FiniteContent α where
  atoms := (left.toFiniteContent.radonNikodymKeys
    right.toFiniteContent).map (overlapRow left right)

/-- The portion of the left law not contained in the singletonwise
overlap. -/
def leftResidualContent {α : Type} [DecidableEq α]
    (left right : Distribution α) : FiniteContent α where
  atoms := (left.toFiniteContent.radonNikodymKeys
    right.toFiniteContent).map (leftResidualRow left right)

/-- The portion of the right law not contained in the singletonwise
overlap. -/
def rightResidualContent {α : Type} [DecidableEq α]
    (left right : Distribution α) : FiniteContent α where
  atoms := (left.toFiniteContent.radonNikodymKeys
    right.toFiniteContent).map (rightResidualRow left right)

private theorem overlap_add_leftResidual_keys {α : Type}
    [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (keys.map (overlapRow left right)) value +
        Distribution.expectationWeight
          (keys.map (leftResidualRow left right)) value =
      left.toFiniteContent.atomMassSum keys value
  | [] => by
      change (0 : Coordinate) + 0 = 0
      ring1
  | key :: remaining => by
      simp only [List.map_cons, Distribution.expectationWeight,
        FiniteContent.atomMassSum, overlapRow, leftResidualRow]
      calc
        min (left.probability (atomEvent key.item))
                (right.probability (atomEvent key.item)) * value key.item +
              Distribution.expectationWeight
                (remaining.map (overlapRow left right)) value +
            ((left.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item +
              Distribution.expectationWeight
                (remaining.map (leftResidualRow left right)) value) =
            (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (left.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
              (Distribution.expectationWeight
                  (remaining.map (overlapRow left right)) value +
                Distribution.expectationWeight
                  (remaining.map (leftResidualRow left right)) value) := by
          ring1
        _ = (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (left.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
              left.toFiniteContent.atomMassSum remaining value := by
          rw [overlap_add_leftResidual_keys left right value remaining]
        _ = left.toFiniteContent.measure (atomEvent key.item) *
              value key.item +
            left.toFiniteContent.atomMassSum remaining value := by
          change
            (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (left.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
                left.toFiniteContent.atomMassSum remaining value =
              left.probability (atomEvent key.item) * value key.item +
                left.toFiniteContent.atomMassSum remaining value
          ring1

private theorem overlap_add_rightResidual_keys {α : Type}
    [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (keys.map (overlapRow left right)) value +
        Distribution.expectationWeight
          (keys.map (rightResidualRow left right)) value =
      right.toFiniteContent.atomMassSum keys value
  | [] => by
      change (0 : Coordinate) + 0 = 0
      ring1
  | key :: remaining => by
      simp only [List.map_cons, Distribution.expectationWeight,
        FiniteContent.atomMassSum, overlapRow, rightResidualRow]
      calc
        min (left.probability (atomEvent key.item))
                (right.probability (atomEvent key.item)) * value key.item +
              Distribution.expectationWeight
                (remaining.map (overlapRow left right)) value +
            ((right.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item +
              Distribution.expectationWeight
                (remaining.map (rightResidualRow left right)) value) =
            (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (right.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
              (Distribution.expectationWeight
                  (remaining.map (overlapRow left right)) value +
                Distribution.expectationWeight
                  (remaining.map (rightResidualRow left right)) value) := by
          ring1
        _ = (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (right.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
              right.toFiniteContent.atomMassSum remaining value := by
          rw [overlap_add_rightResidual_keys left right value remaining]
        _ = right.toFiniteContent.measure (atomEvent key.item) *
              value key.item +
            right.toFiniteContent.atomMassSum remaining value := by
          change
            (min (left.probability (atomEvent key.item))
                  (right.probability (atomEvent key.item)) * value key.item +
              (right.probability (atomEvent key.item) -
                  min (left.probability (atomEvent key.item))
                    (right.probability (atomEvent key.item))) *
                value key.item) +
                right.toFiniteContent.atomMassSum remaining value =
              right.probability (atomEvent key.item) * value key.item +
                right.toFiniteContent.atomMassSum remaining value
          ring1

/-- Overlap plus the left residual reconstructs every left expectation. -/
theorem overlap_integral_add_leftResidual_integral {α : Type}
    [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) :
    (left.overlapContent right).integral value +
        (left.leftResidualContent right).integral value =
      left.expectation value := by
  unfold overlapContent leftResidualContent FiniteContent.integral
  rw [overlap_add_leftResidual_keys]
  exact left.toFiniteContent.atomMassSum_eq_integral value
    (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)
    (left.toFiniteContent.radonNikodymKeys_noRepeated right.toFiniteContent)
    (left.toFiniteContent.payloadsCovered_radonNikodymKeys_left
      right.toFiniteContent)

/-- Overlap plus the right residual reconstructs every right expectation. -/
theorem overlap_integral_add_rightResidual_integral {α : Type}
    [DecidableEq α] (left right : Distribution α)
    (value : α → Coordinate) :
    (left.overlapContent right).integral value +
        (left.rightResidualContent right).integral value =
      right.expectation value := by
  unfold overlapContent rightResidualContent FiniteContent.integral
  rw [overlap_add_rightResidual_keys]
  exact right.toFiniteContent.atomMassSum_eq_integral value
    (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)
    (left.toFiniteContent.radonNikodymKeys_noRepeated right.toFiniteContent)
    (left.toFiniteContent.payloadsCovered_radonNikodymKeys_right
      right.toFiniteContent)

theorem overlap_total_add_leftResidual_total {α : Type}
    [DecidableEq α] (left right : Distribution α) :
    (left.overlapContent right).total +
        (left.leftResidualContent right).total = 1 := by
  have identity := left.overlap_integral_add_leftResidual_integral right
    (fun _ => 1)
  rw [(left.overlapContent right).integral_constant,
    (left.leftResidualContent right).integral_constant,
    left.expectation_constant] at identity
  simpa only [mul_one] using identity

theorem overlap_total_add_rightResidual_total {α : Type}
    [DecidableEq α] (left right : Distribution α) :
    (left.overlapContent right).total +
        (left.rightResidualContent right).total = 1 := by
  have identity := left.overlap_integral_add_rightResidual_integral right
    (fun _ => 1)
  rw [(left.overlapContent right).integral_constant,
    (left.rightResidualContent right).integral_constant,
    right.expectation_constant] at identity
  simpa only [mul_one] using identity

private theorem totalWeight_leftResidual_eq_positiveDifference
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ keys : List (Weighted α),
      totalWeight (keys.map (leftResidualRow left right)) =
        totalWeight
          ((keys.map fun key =>
            { item := key.item
              weight := left.probability (atomEvent key.item) -
                right.probability (atomEvent key.item) : SignedWeighted α }).map
            fun atom =>
              { item := atom.item
                weight := positiveWeight atom.weight
                nonnegative := positiveWeight_nonneg atom.weight })
  | [] => rfl
  | key :: remaining => by
      simp only [List.map_cons, totalWeight,
        totalWeight_leftResidual_eq_positiveDifference left right remaining,
        leftResidualRow]
      rw [left_sub_min_eq_positiveWeight_sub]

private theorem totalWeight_rightResidual_eq_negativeDifference
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ keys : List (Weighted α),
      totalWeight (keys.map (rightResidualRow left right)) =
        totalWeight
          ((keys.map fun key =>
            { item := key.item
              weight := left.probability (atomEvent key.item) -
              right.probability (atomEvent key.item) : SignedWeighted α }).map
            SignedContent.negativePartAtom)
  | [] => rfl
  | key :: remaining => by
      simp only [List.map_cons, totalWeight,
        totalWeight_rightResidual_eq_negativeDifference left right remaining,
        rightResidualRow, SignedContent.negativePartAtom]
      rw [right_sub_min_eq_negativeWeight_sub]

/-- Each residual has total mass exactly equal to total variation. -/
theorem leftResidual_total_eq_totalVariationDistance {α : Type}
    [DecidableEq α] (left right : Distribution α) :
    (left.leftResidualContent right).total =
      left.totalVariationDistance right := by
  unfold leftResidualContent totalVariationDistance signedDifference
  unfold FiniteContent.signedDifference SignedContent.positiveContent
    FiniteContent.total
  exact totalWeight_leftResidual_eq_positiveDifference left right
    (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)

theorem rightResidual_total_eq_totalVariationDistance {α : Type}
    [DecidableEq α] (left right : Distribution α) :
    (left.rightResidualContent right).total =
      left.totalVariationDistance right := by
  calc
    (left.rightResidualContent right).total =
        (left.signedDifference right).negativeContent.total := by
      unfold rightResidualContent signedDifference
      unfold FiniteContent.signedDifference SignedContent.negativeContent
        FiniteContent.total
      exact totalWeight_rightResidual_eq_negativeDifference left right
        (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)
    _ = (left.signedDifference right).positiveContent.total :=
      (left.signedDifference_positiveTotal_eq_negativeTotal right).symm
    _ = left.totalVariationDistance right := rfl

private theorem leftResidual_complement_dominance_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ keys : List (Weighted α),
      eventWeight (keys.map (leftResidualRow left right))
        (complementEvent (left.totalVariationEvent right)) = 0
  | [] => rfl
  | key :: remaining => by
      by_cases order : right.probability (atomEvent key.item) ≤
          left.probability (atomEvent key.item)
      · have selected : left.totalVariationEvent right key.item = true := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = true
          exact decide_eq_true_eq.mpr order
        simp only [List.map_cons, eventWeight, complementEvent, selected,
          leftResidualRow, Bool.not_true, zero_add,
          leftResidual_complement_dominance_measure_eq_zero left right
            remaining]
      · have reverse : left.probability (atomEvent key.item) ≤
            right.probability (atomEvent key.item) :=
          (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
        have unselected : left.totalVariationEvent right key.item = false := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = false
          exact decide_eq_false_iff_not.mpr order
        simp only [List.map_cons, eventWeight, complementEvent, unselected,
          Bool.not_false, leftResidualRow, min_eq_left reverse,
          leftResidual_complement_dominance_measure_eq_zero
            left right remaining]
        ring1

private theorem rightResidual_dominance_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ∀ keys : List (Weighted α),
      eventWeight (keys.map (rightResidualRow left right))
        (left.totalVariationEvent right) = 0
  | [] => rfl
  | key :: remaining => by
      by_cases order : right.probability (atomEvent key.item) ≤
          left.probability (atomEvent key.item)
      · have selected : left.totalVariationEvent right key.item = true := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = true
          exact decide_eq_true_eq.mpr order
        simp only [List.map_cons, eventWeight, selected, rightResidualRow,
          min_eq_right order,
          rightResidual_dominance_measure_eq_zero left right remaining]
        ring1
      · have unselected : left.totalVariationEvent right key.item = false := by
          change decide (right.probability (atomEvent key.item) ≤
            left.probability (atomEvent key.item)) = false
          exact decide_eq_false_iff_not.mpr order
        simp only [List.map_cons, eventWeight, unselected,
          rightResidualRow, zero_add,
          rightResidual_dominance_measure_eq_zero left right remaining]

/-- The two residual contents live on opposite sides of the executable Hahn
event. -/
def residualContents_mutuallySingular {α : Type} [DecidableEq α]
    (left right : Distribution α) :
    FiniteContent.MutuallySingular
      (left.leftResidualContent right)
      (left.rightResidualContent right) where
  separator := left.totalVariationEvent right
  left_outside_zero := by
    unfold leftResidualContent FiniteContent.measure
    exact leftResidual_complement_dominance_measure_eq_zero left right
      (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)
  right_inside_zero := by
    unfold rightResidualContent FiniteContent.measure
    exact rightResidual_dominance_measure_eq_zero left right
      (left.toFiniteContent.radonNikodymKeys right.toFiniteContent)

end Distribution

namespace FiniteContent.MutuallySingular

/-- The product of mutually singular contents gives zero mass to the
diagonal equality event. -/
theorem product_equality_measure_eq_zero {α : Type} [DecidableEq α]
    {left right : FiniteContent α}
    (singular : FiniteContent.MutuallySingular left right) :
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
        Bool.not_false, Bool.true_or]
    · have rightSelected : singular.separator atom.item.2 = true := by
        rw [← same]
        exact separatorSelected
      simp only [unionEvent, rightBad, rightSelected, Bool.or_true]
  have leftBadMeasure : (left.product right).measure leftBad = 0 := by
    calc
      (left.product right).measure leftBad =
          (left.product right).measure (fun pair =>
            complementEvent singular.separator pair.1 &&
              (fun _ => true) pair.2) :=
        (left.product right).measure_congr _ _ (fun pair => by
          simp only [leftBad, Bool.and_true])
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
          simp only [rightBad, Bool.true_and])
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
  exact RFAP.ConstructiveFraction.le_antisymm _ _
    (equalityLeUnion.trans unionLe)
    ((left.product right).measure_nonneg _)

end FiniteContent.MutuallySingular

namespace Distribution

/-- In the positive-distance case, combine the diagonal overlap with the
residual product scaled by the reciprocal of total variation. -/
def positiveMaximalJointContent {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    FiniteContent (α × α) :=
  ((left.overlapContent right).map fun item => (item, item)).append
    (((left.leftResidualContent right).product
      (left.rightResidualContent right)).scale
        (1 / left.totalVariationDistance right)
        (RFAP.ConstructiveFraction.div_nonneg_direct
          (by decide) positive.le))

private theorem inverse_mul_self_mul_self
    (value : Coordinate) (nonzero : value ≠ 0) :
    (1 / value) * (value * value) = value := by
  calc
    (1 / value) * (value * value) =
        ((1 / value) * value) * value := by ring1
    _ = 1 * value :=
      congrArg (fun factor => factor * value)
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 value nonzero)
    _ = value := RFAP.ConstructiveFraction.one_mul value

theorem positiveMaximalJointContent_total {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalJointContent right positive).total = 1 := by
  unfold positiveMaximalJointContent
  rw [FiniteContent.append_total, FiniteContent.map_total,
    FiniteContent.scale_total, FiniteContent.product_total,
    left.leftResidual_total_eq_totalVariationDistance right,
    left.rightResidual_total_eq_totalVariationDistance right,
    inverse_mul_self_mul_self _ positive.ne']
  have overlap := left.overlap_total_add_leftResidual_total right
  rw [left.leftResidual_total_eq_totalVariationDistance right] at overlap
  exact overlap

/-- The positive-distance joint content, certified as a probability
distribution. -/
def positiveMaximalJoint {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    Distribution (α × α) where
  atoms := (left.positiveMaximalJointContent right positive).atoms
  total_one := left.positiveMaximalJointContent_total right positive

private theorem scaled_residualProduct_integral_fst
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Coordinate) :
    ((((left.leftResidualContent right).product
        (left.rightResidualContent right)).scale
          (1 / left.totalVariationDistance right)
          (RFAP.ConstructiveFraction.div_nonneg_direct
            (by decide) positive.le)).integral fun pair => value pair.1) =
      (left.leftResidualContent right).integral value := by
  rw [FiniteContent.scale_integral]
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
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
          (left.totalVariationDistance right) positive.ne')
    _ = (left.leftResidualContent right).integral value := by ring1

private theorem scaled_residualProduct_integral_snd
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Coordinate) :
    ((((left.leftResidualContent right).product
        (left.rightResidualContent right)).scale
          (1 / left.totalVariationDistance right)
          (RFAP.ConstructiveFraction.div_nonneg_direct
            (by decide) positive.le)).integral fun pair => value pair.2) =
      (left.rightResidualContent right).integral value := by
  rw [FiniteContent.scale_integral]
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
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1
          (left.totalVariationDistance right) positive.ne')
    _ = (left.rightResidualContent right).integral value := by ring1

theorem positiveMaximalJoint_expectation_fst
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Coordinate) :
    (left.positiveMaximalJoint right positive).expectation
        (fun pair => value pair.1) = left.expectation value := by
  change (left.positiveMaximalJointContent right positive).integral
      (fun pair => value pair.1) = left.expectation value
  unfold positiveMaximalJointContent
  rw [FiniteContent.append_integral, FiniteContent.map_integral,
    left.scaled_residualProduct_integral_fst right positive value]
  exact left.overlap_integral_add_leftResidual_integral right value

theorem positiveMaximalJoint_expectation_snd
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right)
    (value : α → Coordinate) :
    (left.positiveMaximalJoint right positive).expectation
        (fun pair => value pair.2) = right.expectation value := by
  change (left.positiveMaximalJointContent right positive).integral
      (fun pair => value pair.2) = right.expectation value
  unfold positiveMaximalJointContent
  rw [FiniteContent.append_integral, FiniteContent.map_integral,
    left.scaled_residualProduct_integral_snd right positive value]
  exact left.overlap_integral_add_rightResidual_integral right value

/-- Coupling carried by the explicit positive-distance joint law. -/
def positiveMaximalCoupling {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) : Coupling α α where
  joint := left.positiveMaximalJoint right positive

/-- The positive-distance construction has the requested named marginals. -/
def positiveMaximalLawCoupling {α : Type} [DecidableEq α]
    (left right : Distribution α)
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

private theorem diagonalOverlap_mismatch_measure_eq_zero
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    ((left.overlapContent right).map fun item => (item, item)).measure
        (Coupling.mismatchEvent LawCoupling.equalityRelation) = 0 := by
  rw [FiniteContent.map_measure]
  calc
    (left.overlapContent right).measure (fun item : α =>
        Coupling.mismatchEvent LawCoupling.equalityRelation (item, item)) =
        (left.overlapContent right).measure (fun _ => false) :=
      (left.overlapContent right).measure_congr _ _ (fun item => by
        unfold Coupling.mismatchEvent LawCoupling.equalityRelation
        simp only [decide_true, Bool.not_true])
    _ = 0 := (left.overlapContent right).measure_empty

private theorem residualProduct_mismatch_measure_eq_total
    {α : Type} [DecidableEq α] (left right : Distribution α) :
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
    exact FiniteContent.MutuallySingular.product_equality_measure_eq_zero
      (left.residualContents_mutuallySingular right)
  have complementMass := product.add_complement equalityEvent
  rw [equalityZero, zero_add] at complementMass
  have same : Coupling.mismatchEvent LawCoupling.equalityRelation =
      complementEvent equalityEvent := rfl
  rw [same]
  exact complementMass

/-- In the positive-distance construction, mismatch probability is exactly
total variation. -/
theorem positiveMaximalJoint_mismatchProbability
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalJoint right positive).probability
        (Coupling.mismatchEvent LawCoupling.equalityRelation) =
      left.totalVariationDistance right := by
  change (left.positiveMaximalJointContent right positive).measure
      (Coupling.mismatchEvent LawCoupling.equalityRelation) =
    left.totalVariationDistance right
  unfold positiveMaximalJointContent
  rw [FiniteContent.append_measure,
    diagonalOverlap_mismatch_measure_eq_zero,
    FiniteContent.scale_measure,
    residualProduct_mismatch_measure_eq_total,
    FiniteContent.product_total,
    left.leftResidual_total_eq_totalVariationDistance right,
    left.rightResidual_total_eq_totalVariationDistance right,
    inverse_mul_self_mul_self _ positive.ne', zero_add]

theorem positiveMaximalLawCoupling_mismatchProbability
    {α : Type} [DecidableEq α]
    (left right : Distribution α)
    (positive : 0 < left.totalVariationDistance right) :
    (left.positiveMaximalLawCoupling right positive).mismatchProbability
        LawCoupling.equalityRelation =
      left.totalVariationDistance right := by
  unfold LawCoupling.mismatchProbability positiveMaximalLawCoupling
    positiveMaximalCoupling Coupling.mismatchProbability
  exact left.positiveMaximalJoint_mismatchProbability right positive

/-- An explicit maximal coupling for every pair of finite rational laws. -/
def maximalLawCoupling {α : Type} [DecidableEq α]
    (left right : Distribution α) : LawCoupling left right := by
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

/-- The constructive maximal-coupling theorem: the computed witness attains
the universal total-variation lower bound exactly. -/
theorem maximalLawCoupling_mismatchProbability
    {α : Type} [DecidableEq α] (left right : Distribution α) :
    (left.maximalLawCoupling right).mismatchProbability
        LawCoupling.equalityRelation =
      left.totalVariationDistance right := by
  by_cases zero : left.totalVariationDistance right = 0
  · unfold maximalLawCoupling
    simp only [zero, ↓reduceDIte]
    change (LawCoupling.refl left).mismatchProbability
      LawCoupling.equalityRelation = 0
    exact LawCoupling.refl_mismatchProbability_eq_zero left
  · have positive : 0 < left.totalVariationDistance right :=
      lt_of_le_of_ne (left.totalVariationDistance_nonnegative right)
        (Ne.symm zero)
    unfold maximalLawCoupling
    simp only [zero, ↓reduceDIte]
    exact left.positiveMaximalLawCoupling_mismatchProbability right positive

end Distribution

end FiniteMeasure
