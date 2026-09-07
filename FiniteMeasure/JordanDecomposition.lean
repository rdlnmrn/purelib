import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.LebesgueDecompositionUniqueness
import FiniteMeasure.Singularity

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

namespace FiniteMeasure

namespace SignedContent

/-- Displayed finite Jordan decomposition of a signed content. -/
structure JordanDecomposition {α : Type} (content : SignedContent α) where
  positive : FiniteContent α
  negative : FiniteContent α
  measure_eq : ∀ event : α → Bool,
    content.measure event = positive.measure event - negative.measure event
  positive_mutuallySingular_negative :
    FiniteContent.MutuallySingular positive negative

/-- The atomwise positive and negative parts form a genuine Jordan
decomposition whenever an item-level Hahn sign certificate is supplied. -/
def HahnCertificate.jordanDecomposition {α : Type}
    {content : SignedContent α} (certificate : HahnCertificate content) :
    JordanDecomposition content where
  positive := content.positiveContent
  negative := content.negativeContent
  measure_eq := content.measure_eq_positive_sub_negative
  positive_mutuallySingular_negative :=
    certificate.positiveContent_mutuallySingular_negativeContent

namespace JordanDecomposition

private theorem intersection_implies_left {α : Type}
    (atoms : List (Weighted α)) (event separator : α → Bool) :
    EventImpliesOn atoms (intersectionEvent event separator) event := by
  intro atom member selected
  cases eventSelected : event atom.item
  · simp only [intersectionEvent, eventSelected, Bool.false_and] at selected
    exact Bool.noConfusion selected
  · exact rfl

/-- The positive parts of any two Jordan decompositions agree on every
executable event. -/
theorem positive_measure_eq {α : Type} {content : SignedContent α}
    (first second : JordanDecomposition content) (event : α → Bool) :
    first.positive.measure event = second.positive.measure event := by
  apply RFAP.ConstructiveFraction.le_antisymm
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
      rw [positiveFull, first.measure_eq selectedEvent, negativeSelectedZero,
        sub_zero]
    have signedLeSecondSelected : content.measure selectedEvent ≤
        second.positive.measure selectedEvent := by
      rw [second.measure_eq selectedEvent]
      exact sub_le_self _ (second.negative.measure_nonneg selectedEvent)
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
      rw [positiveFull, second.measure_eq selectedEvent, negativeSelectedZero,
        sub_zero]
    have signedLeFirstSelected : content.measure selectedEvent ≤
        first.positive.measure selectedEvent := by
      rw [first.measure_eq selectedEvent]
      exact sub_le_self _ (first.negative.measure_nonneg selectedEvent)
    have firstSelectedLe : first.positive.measure selectedEvent ≤
        first.positive.measure event :=
      eventWeight_mono
        (intersection_implies_left first.positive.atoms event separator)
    rw [secondPositiveSigned]
    exact signedLeFirstSelected.trans firstSelectedLe

/-- The negative parts of any two Jordan decompositions agree on every
executable event. -/
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

/-- Every displayed positive Jordan part agrees eventwise with the canonical
atomwise positive content selected by a Hahn certificate. -/
theorem positive_measure_eq_canonical {α : Type}
    {content : SignedContent α} (decomposition : JordanDecomposition content)
    (certificate : HahnCertificate content) (event : α → Bool) :
    decomposition.positive.measure event =
      content.positiveContent.measure event :=
  decomposition.positive_measure_eq certificate.jordanDecomposition event

/-- Every displayed negative Jordan part agrees eventwise with the canonical
atomwise negative content selected by a Hahn certificate. -/
theorem negative_measure_eq_canonical {α : Type}
    {content : SignedContent α} (decomposition : JordanDecomposition content)
    (certificate : HahnCertificate content) (event : α → Bool) :
    decomposition.negative.measure event =
      content.negativeContent.measure event :=
  decomposition.negative_measure_eq certificate.jordanDecomposition event

end JordanDecomposition

end SignedContent

end FiniteMeasure
