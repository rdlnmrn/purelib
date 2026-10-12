module

import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Content.NullEvent
import Purelib.Measure.Content.Singularity
import Purelib.Measure.SignedContent.Basic
import Purelib.Measure.SignedContent.Hahn.Basic
public import Purelib.Measure.SignedContent.Hahn.Singularity
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite Hahn--Jordan decomposition and uniqueness

A displayed Jordan decomposition reconstructs a signed content from two
nonnegative finite contents separated by an executable event.  Any two such
decompositions agree on every executable event.  A Hahn certificate turns
the atomwise positive and negative parts into the canonical decomposition.

The Hahn certificate is essential when a signed table repeats one payload
with conflicting signs: in that case no item-level Boolean separator need
exist even though atomwise positive and negative weights are computable.
-/

public section

namespace Purelib.Measure

namespace SignedContent

set_option genInjectivity false in
/-- Retain mutually singular positive contents whose measurement difference is the exact signed content.

The eventwise decomposition identity and an explicit separating event refer to the same original signed content and the
two retained parts. -/
structure JordanDecomposition {α : Type} (content : SignedContent α) where
  /-- The exact retained nonnegative content forming the positive part. -/ positive : Content α
  /-- The exact retained nonnegative content forming the negative part. -/ negative : Content α
  /-- Every original signed event measurement equals the positive measurement minus the negative measurement. -/
    measure_eq : ∀ event : α → Bool,
    content.measure event = positive.measure event - negative.measure event
  /-- An explicit separator certifies mutual singularity of the two retained parts. -/
    positive_mutuallySingular_negative :
    Content.MutuallySingular positive negative

constructive_injectivity JordanDecomposition

/-- Construct the signed content's positive and negative parts as a Jordan decomposition using its retained Hahn
separator. -/
@[expose] def HahnCertificate.jordanDecomposition {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    JordanDecomposition content where
  positive := content.positiveContent
  negative := content.negativeContent
  measure_eq := content.measure_eq_positive_sub_negative
  positive_mutuallySingular_negative :=
    certificate.positiveContent_mutuallySingular_negativeContent

namespace JordanDecomposition

/-- Selection by an event intersection implies selection by its left event on every retained atom. -/
private theorem intersection_implies_left {α : Type}
    (atoms : List (Weighted α)) (event separator : α → Bool) :
    EventImpliesOn atoms (intersectionEvent event separator) event := by
  intro atom member selected
  cases eventSelected : event atom.item
  · simp only [-eq_self, -iff_self, intersectionEvent, eventSelected, Bool.false_and] at selected
    exact Bool.noConfusion selected
  · exact rfl

open Purelib.Data.Rat in
/-- Any two Jordan decompositions of the same signed content have equal positive measurements for every event. -/
theorem positive_measure_eq {α : Type} {content : SignedContent α}
    (first second : JordanDecomposition content) (event : α → Bool) :
    first.positive.measure event = second.positive.measure event := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · let separator := first.positive_mutuallySingular_negative.separator
    let selectedEvent := intersectionEvent event separator
    have positiveFull : first.positive.measure event =
        first.positive.measure selectedEvent :=
      first.positive.measure_eq_intersection_of_complement_eq_zero
        event separator
        first.positive_mutuallySingular_negative.left_outside_zero
    have negativeSelectedZero : first.negative.measure selectedEvent = 0 :=
      first.negative.measure_intersection_eq_zero_of_right event separator
        first.positive_mutuallySingular_negative.right_inside_zero
    have firstPositiveSigned : first.positive.measure event =
        content.measure selectedEvent := by
      rw [positiveFull, first.measure_eq selectedEvent, negativeSelectedZero]
      ring1
    have signedLeSecondSelected : content.measure selectedEvent ≤
        second.positive.measure selectedEvent := by
      rw [second.measure_eq selectedEvent]
      exact Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
      have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
        (second.negative.measure_nonneg selectedEvent) (second.positive.measure selectedEvent)
      calc
        (second.positive.measure selectedEvent) = 0 + (second.positive.measure selectedEvent) := (Fraction.zero_add
          _).symm
        _ ≤ _ + (second.positive.measure selectedEvent) := translated
        _ = (second.positive.measure selectedEvent) + _ := Fraction.add_comm _ _)
    have secondSelectedLe : second.positive.measure selectedEvent ≤
        second.positive.measure event :=
      eventWeight_mono
        (intersection_implies_left second.positive.atoms event separator)
    rw [firstPositiveSigned]
    exact signedLeSecondSelected.trans secondSelectedLe
  · let separator := second.positive_mutuallySingular_negative.separator
    let selectedEvent := intersectionEvent event separator
    have positiveFull : second.positive.measure event =
        second.positive.measure selectedEvent :=
      second.positive.measure_eq_intersection_of_complement_eq_zero
        event separator
        second.positive_mutuallySingular_negative.left_outside_zero
    have negativeSelectedZero : second.negative.measure selectedEvent = 0 :=
      second.negative.measure_intersection_eq_zero_of_right event separator
        second.positive_mutuallySingular_negative.right_inside_zero
    have secondPositiveSigned : second.positive.measure event =
        content.measure selectedEvent := by
      rw [positiveFull, second.measure_eq selectedEvent, negativeSelectedZero]
      ring1
    have signedLeFirstSelected : content.measure selectedEvent ≤
        first.positive.measure selectedEvent := by
      rw [first.measure_eq selectedEvent]
      exact Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr (by
      have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
        (first.negative.measure_nonneg selectedEvent) (first.positive.measure selectedEvent)
      calc
        (first.positive.measure selectedEvent) = 0 + (first.positive.measure selectedEvent) := (Fraction.zero_add
          _).symm
        _ ≤ _ + (first.positive.measure selectedEvent) := translated
        _ = (first.positive.measure selectedEvent) + _ := Fraction.add_comm _ _)
    have firstSelectedLe : first.positive.measure selectedEvent ≤
        first.positive.measure event :=
      eventWeight_mono
        (intersection_implies_left first.positive.atoms event separator)
    rw [secondPositiveSigned]
    exact signedLeFirstSelected.trans firstSelectedLe

/-- Any two Jordan decompositions of the same signed content have equal negative measurements for every event. -/
theorem negative_measure_eq {α : Type} {content : SignedContent α}
    (first second : JordanDecomposition content) (event : α → Bool) :
    first.negative.measure event = second.negative.measure event := by
  have positiveEqual := first.positive_measure_eq second event
  calc
    first.negative.measure event =
        first.positive.measure event - content.measure event := by
      rw [first.measure_eq event]
      ring1
    _ = second.positive.measure event - content.measure event := by
      rw [positiveEqual]
    _ = second.negative.measure event := by
      rw [second.measure_eq event]
      ring1

/-- Every Jordan positive part agrees eventwise with the original signed content's positive part when a Hahn certificate
is supplied. -/
theorem positive_measure_eq_canonical {α : Type}
    {content : SignedContent α} (decomposition : JordanDecomposition content)
    (certificate : HahnCertificate content) (event : α → Bool) :
    decomposition.positive.measure event =
      content.positiveContent.measure event :=
  decomposition.positive_measure_eq certificate.jordanDecomposition event

/-- Every Jordan negative part agrees eventwise with the original signed content's negative part when a Hahn certificate
is supplied. -/
theorem negative_measure_eq_canonical {α : Type}
    {content : SignedContent α} (decomposition : JordanDecomposition content)
    (certificate : HahnCertificate content) (event : α → Bool) :
    decomposition.negative.measure event =
      content.negativeContent.measure event :=
  decomposition.negative_measure_eq certificate.jordanDecomposition event

end JordanDecomposition

end SignedContent

end Purelib.Measure
