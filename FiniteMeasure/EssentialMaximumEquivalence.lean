import FiniteMeasure.LpEquivalence
import FiniteMeasure.EssentialMaximum

/-!
# Essential maxima under finite evaluation equivalence

Evaluation-equivalent finite distributions have the same null discrepancies.
Consequently they have the same essential bounds and the same executable
essential maxima, even when their displayed atom tables use different row
orders or consolidate repeated payloads.
-/

namespace FiniteMeasure

namespace Distribution.EvaluationEquivalent

private theorem essentiallyBoundedBy_of_equivalent {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Coordinate) (ceiling : Coordinate)
    (bounded : right.EssentiallyBoundedBy value ceiling) :
    left.EssentiallyBoundedBy value ceiling := by
  let magnitude : α → Coordinate := fun item =>
    rationalSeparation (value item) 0
  let capped : α → Coordinate := fun item =>
    min (magnitude item) ceiling
  have rightEqual : right.EqualAlmostEverywhere magnitude capped := by
    intro atom member
    rcases bounded atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      change magnitude atom.item = min (magnitude atom.item) ceiling
      exact (min_eq_left bound).symm
  have leftEqual : left.EqualAlmostEverywhere magnitude capped :=
    (equivalent.equalAlmostEverywhere_iff magnitude capped).mpr rightEqual
  intro atom member
  rcases leftEqual atom member with zero | same
  · exact Or.inl zero
  · apply Or.inr
    change magnitude atom.item ≤ ceiling
    calc
      magnitude atom.item = capped atom.item := same
      _ = min (magnitude atom.item) ceiling := rfl
      _ ≤ ceiling := min_le_right _ _

/-- Essential boundedness is an observational property of a displayed
finite distribution, independent of its atom-table representation. -/
theorem essentiallyBoundedBy_iff {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Coordinate) (ceiling : Coordinate) :
    left.EssentiallyBoundedBy value ceiling ↔
      right.EssentiallyBoundedBy value ceiling := by
  constructor
  · exact essentiallyBoundedBy_of_equivalent equivalent.symm value ceiling
  · exact essentiallyBoundedBy_of_equivalent equivalent value ceiling

/-- Evaluation-equivalent finite distributions have identical executable
essential maxima. -/
theorem essentialMaximumMagnitude_eq {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.essentialMaximumMagnitude value =
      right.essentialMaximumMagnitude value := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · change left.toFiniteContent.essentialMaximumMagnitude value ≤
      right.toFiniteContent.essentialMaximumMagnitude value
    apply left.toFiniteContent.essentialMaximumMagnitude_le value
      (right.essentialMaximumMagnitude value)
      (right.essentialMaximumMagnitude_nonnegative value)
    exact (equivalent.essentiallyBoundedBy_iff value
      (right.essentialMaximumMagnitude value)).mpr
        (FiniteContent.essentiallyBoundedBy_essentialMaximumMagnitude
          right.toFiniteContent value)
  · change right.toFiniteContent.essentialMaximumMagnitude value ≤
      left.toFiniteContent.essentialMaximumMagnitude value
    apply right.toFiniteContent.essentialMaximumMagnitude_le value
      (left.essentialMaximumMagnitude value)
      (left.essentialMaximumMagnitude_nonnegative value)
    exact (equivalent.essentiallyBoundedBy_iff value
      (left.essentialMaximumMagnitude value)).mp
        (FiniteContent.essentiallyBoundedBy_essentialMaximumMagnitude
          left.toFiniteContent value)

theorem essentialMaximumDistance_eq {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
    left.essentialMaximumDistance first second =
      right.essentialMaximumDistance first second := by
  unfold Distribution.essentialMaximumDistance
    FiniteContent.essentialMaximumDistance
  exact equivalent.essentialMaximumMagnitude_eq
    (fun item => first item - second item)

end Distribution.EvaluationEquivalent

end FiniteMeasure
