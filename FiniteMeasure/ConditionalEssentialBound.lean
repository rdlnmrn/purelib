import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalJensen
import FiniteMeasure.EssentialMaximum

/-!
# Essential bounds under finite conditional expectation

Conditional averaging ignores displayed zero-weight rows and preserves every
explicit essential magnitude ceiling.  Consequently the computed finite
essential maximum cannot increase.  This is the constructive finite
`L∞`-contraction theorem; no supremum or completed function space is used.
-/

namespace FiniteMeasure

namespace Distribution

/-- Restricted integration preserves an order which may fail only on
displayed zero-weight rows. -/
theorem eventIntegral_mono_off_zero {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    distribution.eventIntegral event lower ≤
      distribution.eventIntegral event upper := by
  unfold eventIntegral
  apply distribution.toFiniteContent.integral_mono_off_zero
  intro atom member
  rcases pointwise atom member with zero | bounded
  · exact Or.inl zero
  · apply Or.inr
    cases selected : event atom.item
    · simp only [indicator, selected, zero_mul]
      exact le_rfl
    · simpa only [indicator, selected, one_mul] using bounded

/-- Conditional averaging preserves an order away from displayed zero-weight
rows. -/
theorem conditionalMean_mono_off_zero {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ distribution.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    distribution.conditionalMean event lower ≤
      distribution.conditionalMean event upper := by
  have numeratorOrder :=
    distribution.eventIntegral_mono_off_zero event lower upper pointwise
  unfold conditionalMean
  change distribution.eventIntegral event lower *
      (distribution.probability event)⁻¹ ≤
    distribution.eventIntegral event upper *
      (distribution.probability event)⁻¹
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    numeratorOrder
    (RFAP.ConstructiveFraction.inv_pos_direct positive).le

/-- An essential upper ceiling controls the conditional mean on every
positive displayed event. -/
theorem conditionalMean_le_of_boundedAboveOffZeroWeightOn {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : BoundedAboveOffZeroWeightOn distribution.atoms value ceiling) :
    distribution.conditionalMean event value ≤ ceiling := by
  calc
    distribution.conditionalMean event value ≤
        distribution.conditionalMean event (fun _ => ceiling) :=
      distribution.conditionalMean_mono_off_zero event positive value
        (fun _ => ceiling) bounded
    _ = ceiling :=
      distribution.conditionalMean_constant event positive ceiling

/-- Restricting two observables to one displayed event makes the exact
integral functional Lipschitz with factor equal to that event's rational
probability. -/
theorem eventIntegral_separation_le_probability_mul_essentialMaximumDistance
    {α : Type} (distribution : Distribution α) (event : α → Bool)
    (left right : α → Coordinate) :
    rationalSeparation (distribution.eventIntegral event left)
        (distribution.eventIntegral event right) ≤
      distribution.probability event *
        distribution.essentialMaximumDistance left right := by
  have expectationBound := distribution.expectation_separation_le_l1Distance
    (fun item => indicator event item * left item)
    (fun item => indicator event item * right item)
  change rationalSeparation (distribution.eventIntegral event left)
      (distribution.eventIntegral event right) ≤
    distribution.l1Distance
      (fun item => indicator event item * left item)
      (fun item => indicator event item * right item) at expectationBound
  have l1Identity :
      distribution.l1Distance
          (fun item => indicator event item * left item)
          (fun item => indicator event item * right item) =
        distribution.poweredL1
          (fun item => indicator event item * (left item - right item)) := by
    rw [← distribution.poweredL1_sub_eq_l1Distance]
    exact distribution.toFiniteContent.poweredL1_congr _ _
      (fun item => by ring1)
  have restrictedBound :=
    FiniteContent.poweredL1_indicator_mul_le_essentialMaximum_mul_measure
      distribution.toFiniteContent event
        (fun item => left item - right item)
  calc
    rationalSeparation (distribution.eventIntegral event left)
          (distribution.eventIntegral event right) ≤
        distribution.l1Distance
          (fun item => indicator event item * left item)
          (fun item => indicator event item * right item) := expectationBound
    _ = distribution.poweredL1
          (fun item => indicator event item * (left item - right item)) :=
      l1Identity
    _ ≤ distribution.essentialMaximumDistance left right *
          distribution.probability event := restrictedBound
    _ = distribution.probability event *
          distribution.essentialMaximumDistance left right := by
      ring1

/-- Conditional averaging on one explicitly positive event is itself
one-Lipschitz for finite essential-maximum distance. -/
theorem conditionalMean_separation_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    rationalSeparation (distribution.conditionalMean event left)
        (distribution.conditionalMean event right) ≤
      distribution.essentialMaximumDistance left right := by
  let probability := distribution.probability event
  let leftIntegral := distribution.eventIntegral event left
  let rightIntegral := distribution.eventIntegral event right
  let distance := distribution.essentialMaximumDistance left right
  have eventBound :
      rationalSeparation leftIntegral rightIntegral ≤
        probability * distance := by
    exact
      Distribution.eventIntegral_separation_le_probability_mul_essentialMaximumDistance
        distribution event left right
  have inversePositive : 0 < probability⁻¹ :=
    RFAP.ConstructiveFraction.inv_pos_direct positive
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    eventBound (rationalSeparation_nonneg probability⁻¹ 0)
  have inverseMagnitude :
      rationalSeparation probability⁻¹ 0 = probability⁻¹ :=
    rationalSeparation_zero_of_nonneg inversePositive.le
  unfold conditionalMean
  change rationalSeparation (leftIntegral / probability)
      (rightIntegral / probability) ≤ distance
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    rationalSeparation (leftIntegral * probability⁻¹)
          (rightIntegral * probability⁻¹) =
        rationalSeparation (probability⁻¹ * leftIntegral)
          (probability⁻¹ * rightIntegral) := by
      rw [mul_comm leftIntegral probability⁻¹,
        mul_comm rightIntegral probability⁻¹]
    _ = rationalSeparation probability⁻¹ 0 *
          rationalSeparation leftIntegral rightIntegral :=
      rationalSeparation_scale probability⁻¹ leftIntegral rightIntegral
    _ ≤ rationalSeparation probability⁻¹ 0 *
          (probability * distance) := scaled
    _ = distance := by
      rw [inverseMagnitude]
      calc
        probability⁻¹ * (probability * distance) =
            (probability⁻¹ * probability) * distance := by
          rw [mul_assoc]
        _ = distance := by
          rw [RFAP.ConstructiveFraction.inv_mul_cancel probability
            positive.ne', one_mul]

end Distribution

namespace PositiveEventPartition

/-- Every displayed conditional-expectation value satisfies any essential
magnitude ceiling for the original observable, including on zero-weight
rows of the output table. -/
theorem rationalSeparation_conditionalExpectation_le_of_essentialBound
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : distribution.EssentiallyBoundedBy value ceiling)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    rationalSeparation
        (partition.conditionalExpectation value atom.item) 0 ≤ ceiling := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
    value event eventMember atom member selected]
  exact (distribution.conditionalMean_rationalSeparation_zero_le event
      (partition.positive event eventMember) value).trans
    (distribution.conditionalMean_le_of_boundedAboveOffZeroWeightOn event
      (partition.positive event eventMember)
      (fun item => rationalSeparation (value item) 0) ceiling bounded)

/-- Finite conditional expectation preserves every displayed essential
magnitude ceiling. -/
theorem essentiallyBoundedBy_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.EssentiallyBoundedBy
      (partition.conditionalExpectation value) ceiling := by
  intro atom member
  exact Or.inr
    (partition.rationalSeparation_conditionalExpectation_le_of_essentialBound
      value ceiling bounded atom member)

/-- The executable least essential magnitude bound is contractive under
finite conditional expectation. -/
theorem essentialMaximumMagnitude_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (partition.conditionalExpectation value) ≤
      distribution.essentialMaximumMagnitude value := by
  apply distribution.toFiniteContent.essentialMaximumMagnitude_le
  · exact distribution.essentialMaximumMagnitude_nonnegative value
  · exact partition.essentiallyBoundedBy_conditionalExpectation value
      (distribution.essentialMaximumMagnitude value)
      (distribution.toFiniteContent
        |>.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Finite conditional expectation contracts the executable
essential-maximum distance between two observables. -/
theorem essentialMaximumDistance_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Coordinate) :
    distribution.essentialMaximumDistance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) ≤
      distribution.essentialMaximumDistance left right := by
  unfold Distribution.essentialMaximumDistance
    FiniteContent.essentialMaximumDistance
  calc
    distribution.essentialMaximumMagnitude (fun item =>
          partition.conditionalExpectation left item -
            partition.conditionalExpectation right item) =
        distribution.essentialMaximumMagnitude
          (partition.conditionalExpectation (fun item =>
            left item - right item)) :=
      distribution.essentialMaximumMagnitude_congr _ _ (fun item =>
        (partition.conditionalExpectation_sub left right item).symm)
    _ ≤ distribution.essentialMaximumMagnitude (fun item =>
          left item - right item) :=
      partition.essentialMaximumMagnitude_conditionalExpectation_le
        (fun item => left item - right item)

end PositiveEventPartition

end FiniteMeasure
