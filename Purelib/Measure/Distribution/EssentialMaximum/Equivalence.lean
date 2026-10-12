module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.Equivalence
import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
public import Purelib.Measure.Distribution.EssentialBound.Basic
public import Purelib.Measure.Distribution.Equivalence

/-!
# Essential maxima under finite evaluation equivalence

Evaluation-equivalent finite distributions have the same null discrepancies.
Consequently they have the same essential bounds and the same executable
essential maxima, even when their displayed atom tables use different row
orders or consolidate repeated payloads.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution.EvaluationEquivalent

open Purelib
open Purelib.Data.Rat
/-- Transfer an essential magnitude ceiling from the right law to an evaluation-equivalent left law. -/
private theorem essentiallyBoundedBy_of_equivalent {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : right.EssentiallyBoundedBy value ceiling) :
    left.EssentiallyBoundedBy value ceiling := by
  let magnitude : α → Fraction.Rational := fun item =>
    Distance.rationalSeparation (value item) 0
  let capped : α → Fraction.Rational := fun item =>
    min (magnitude item) ceiling
  have rightEqual : right.EqualAlmostEverywhere magnitude capped := by
    intro atom member
    rcases bounded atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      change magnitude atom.item = min (magnitude atom.item) ceiling
      exact (Fraction.Order.Basic.min_eq_left bound).symm
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
      _ ≤ ceiling := Fraction.Order.Basic.min_le_right _ _

/-- Evaluation-equivalent laws admit exactly the same essential magnitude ceilings. -/
theorem essentiallyBoundedBy_iff {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) :
    left.EssentiallyBoundedBy value ceiling ↔
      right.EssentiallyBoundedBy value ceiling := by
  constructor
  · exact essentiallyBoundedBy_of_equivalent equivalent.symm value ceiling
  · exact essentiallyBoundedBy_of_equivalent equivalent value ceiling

/-- Evaluation-equivalent laws give each observable the same essential maximum magnitude. -/
theorem essentialMaximumMagnitude_eq {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) :
    left.essentialMaximumMagnitude value =
      right.essentialMaximumMagnitude value := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · change left.toContent.essentialMaximumMagnitude value ≤
      right.toContent.essentialMaximumMagnitude value
    apply left.toContent.essentialMaximumMagnitude_le value
      (right.essentialMaximumMagnitude value)
      (right.essentialMaximumMagnitude_nonnegative value)
    exact (equivalent.essentiallyBoundedBy_iff value
      (right.essentialMaximumMagnitude value)).mpr
        (Content.essentiallyBoundedBy_essentialMaximumMagnitude
          right.toContent value)
  · change right.toContent.essentialMaximumMagnitude value ≤
      left.toContent.essentialMaximumMagnitude value
    apply right.toContent.essentialMaximumMagnitude_le value
      (left.essentialMaximumMagnitude value)
      (left.essentialMaximumMagnitude_nonnegative value)
    exact (equivalent.essentiallyBoundedBy_iff value
      (left.essentialMaximumMagnitude value)).mp
        (Content.essentiallyBoundedBy_essentialMaximumMagnitude
          left.toContent value)

/-- Evaluation-equivalent laws give each observable pair the same essential maximum distance. -/
theorem essentialMaximumDistance_eq {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.essentialMaximumDistance first second =
      right.essentialMaximumDistance first second := by
  unfold Distribution.essentialMaximumDistance
    Content.essentialMaximumDistance
  exact equivalent.essentialMaximumMagnitude_eq
    (fun item => first item - second item)

end Distribution.EvaluationEquivalent

end Purelib.Measure
