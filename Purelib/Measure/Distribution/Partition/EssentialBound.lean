module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Conditioning.EssentialBound
import Purelib.Measure.Distribution.Conditioning.Jensen
import Purelib.Measure.Distribution.Content
public import Purelib.Measure.Distribution.EssentialBound.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Measure.Distribution.Partition.Expectation

section
@[expose] public section

/-!
# Essential bounds under finite conditional expectation

Conditional averaging ignores displayed zero-weight rows and preserves every
explicit essential magnitude ceiling.  Consequently the computed finite
essential maximum cannot increase.  This is the constructive finite
`L∞`-contraction theorem; no supremum or completed function space is used.
-/

namespace Purelib.Measure

namespace Distribution
end Distribution

namespace PositiveEventPartition

open Purelib.Data.Rat
/-- An original essential magnitude ceiling bounds partition conditional expectation at every retained atom. -/
theorem rationalSeparation_conditionalExpectation_le_of_essentialBound
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : distribution.EssentiallyBoundedBy value ceiling)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    Distance.rationalSeparation
        (partition.conditionalExpectation value atom.item) 0 ≤ ceiling := by
  rcases partition.toEventPartition.exists_selected_event atom member with
    ⟨event, eventMember, selected⟩
  rw [partition.conditionalExpectation_eq_conditionalMean_on_cell
    value event eventMember atom member selected]
  exact (distribution.conditionalMean_rationalSeparation_zero_le event
      (partition.positive event eventMember) value).trans
    (distribution.conditionalMean_le_of_boundedAboveOffZeroWeightOn event
      (partition.positive event eventMember)
      (fun item => Distance.rationalSeparation (value item) 0) ceiling bounded)

/-- Partition conditional expectation preserves every essential magnitude ceiling of the original observable. -/
theorem essentiallyBoundedBy_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : distribution.EssentiallyBoundedBy value ceiling) :
    distribution.EssentiallyBoundedBy
      (partition.conditionalExpectation value) ceiling := by
  intro atom member
  exact Or.inr
    (partition.rationalSeparation_conditionalExpectation_le_of_essentialBound
      value ceiling bounded atom member)

/-- Partition conditional expectation cannot increase essential maximum magnitude. -/
theorem essentialMaximumMagnitude_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (partition.conditionalExpectation value) ≤
      distribution.essentialMaximumMagnitude value := by
  apply distribution.toContent.essentialMaximumMagnitude_le
  · exact distribution.essentialMaximumMagnitude_nonnegative value
  · exact partition.essentiallyBoundedBy_conditionalExpectation value
      (distribution.essentialMaximumMagnitude value)
      (distribution.toContent
        |>.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Applying the same partition conditional expectation to both observables cannot increase essential maximum distance.
-/
theorem essentialMaximumDistance_conditionalExpectation_le {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (left right : α → Fraction.Rational) :
    distribution.essentialMaximumDistance
        (partition.conditionalExpectation left)
        (partition.conditionalExpectation right) ≤
      distribution.essentialMaximumDistance left right := by
  unfold Distribution.essentialMaximumDistance
    Content.essentialMaximumDistance
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

end Purelib.Measure

end
