module
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Density.Witness
public import Purelib.Measure.Content.Lebesgue.Basic
import Purelib.Measure.Content.NullEvent
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

section
/-!
# Uniqueness of finite Lebesgue decomposition

Any two displayed decompositions of one finite content into a part absolutely
continuous with respect to a source and a source-singular remainder agree on
every executable event.  The proof intersects the two explicit singularity
separators and uses only finite additivity and nonnegative event weights.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content
namespace LebesgueDecomposition

/-- The regular part vanishes outside any separator whose complement has zero original source mass. -/
private theorem regular_complement_separator_eq_zero {α : Type}
    {target source : Content α}
    (decomposition : LebesgueDecomposition target source)
    (separator : α → Bool)
    (sourceOutsideZero :
      source.measure (complementEvent separator) = 0) :
    decomposition.regular.measure (complementEvent separator) = 0 :=
  decomposition.regular_absolutelyContinuous
    (complementEvent separator) sourceOutsideZero

/-- Any two decompositions of the same target relative to the same source have equal regular-part event measurements.

Intersect the two retained separators to compare both regular parts on a common event. Their singular parts vanish there
and both reconstruct the same original target reading. -/
theorem regular_measure_eq {α : Type}
    {target source : Content α}
    (first second : LebesgueDecomposition target source)
    (event : α → Bool) :
    first.regular.measure event = second.regular.measure event := by
  let firstSeparator := first.source_mutuallySingular_singular.separator
  let secondSeparator := second.source_mutuallySingular_singular.separator
  let eventFirst := intersectionEvent event firstSeparator
  let common := intersectionEvent eventFirst secondSeparator
  have firstOutsideFirst :
      first.regular.measure (complementEvent firstSeparator) = 0 :=
    first.regular_complement_separator_eq_zero firstSeparator
      first.source_mutuallySingular_singular.left_outside_zero
  have firstOutsideSecond :
      first.regular.measure (complementEvent secondSeparator) = 0 :=
    first.regular_complement_separator_eq_zero secondSeparator
      second.source_mutuallySingular_singular.left_outside_zero
  have secondOutsideFirst :
      second.regular.measure (complementEvent firstSeparator) = 0 :=
    second.regular_complement_separator_eq_zero firstSeparator
      first.source_mutuallySingular_singular.left_outside_zero
  have secondOutsideSecond :
      second.regular.measure (complementEvent secondSeparator) = 0 :=
    second.regular_complement_separator_eq_zero secondSeparator
      second.source_mutuallySingular_singular.left_outside_zero
  have firstEventCommon : first.regular.measure event =
      first.regular.measure common := by
    calc
      first.regular.measure event = first.regular.measure eventFirst :=
        first.regular.measure_eq_intersection_of_complement_eq_zero
          event firstSeparator firstOutsideFirst
      _ = first.regular.measure common :=
        first.regular.measure_eq_intersection_of_complement_eq_zero
          eventFirst secondSeparator firstOutsideSecond
  have secondEventCommon : second.regular.measure event =
      second.regular.measure common := by
    calc
      second.regular.measure event = second.regular.measure eventFirst :=
        second.regular.measure_eq_intersection_of_complement_eq_zero
          event firstSeparator secondOutsideFirst
      _ = second.regular.measure common :=
        second.regular.measure_eq_intersection_of_complement_eq_zero
          eventFirst secondSeparator secondOutsideSecond
  have commonImpliesFirst : EventImpliesOn first.singular.atoms common
      firstSeparator := by
    intro atom member selected
    cases eventSelected : event atom.item
    · simp only [common, eventFirst, intersectionEvent, eventSelected,
        Bool.false_and] at selected
      exact Bool.noConfusion selected
    · cases firstSelected : firstSeparator atom.item
      · simp only [common, eventFirst, intersectionEvent, eventSelected,
          firstSelected, Bool.true_and, Bool.false_and] at selected
        exact Bool.noConfusion selected
      · exact rfl
  have commonImpliesSecond : EventImpliesOn second.singular.atoms common
      secondSeparator := by
    intro atom member selected
    cases eventSelected : event atom.item
    · simp only [common, eventFirst, intersectionEvent, eventSelected,
        Bool.false_and] at selected
      exact Bool.noConfusion selected
    · cases firstSelected : firstSeparator atom.item
      · simp only [common, eventFirst, intersectionEvent, eventSelected,
          firstSelected, Bool.true_and, Bool.false_and] at selected
        exact Bool.noConfusion selected
      · simpa only [common, eventFirst, intersectionEvent, eventSelected,
          firstSelected, Bool.true_and] using selected
  have firstSingularCommonZero : first.singular.measure common = 0 :=
    first.singular.measure_eq_zero_of_eventImplies commonImpliesFirst
      first.source_mutuallySingular_singular.right_inside_zero
  have secondSingularCommonZero : second.singular.measure common = 0 :=
    second.singular.measure_eq_zero_of_eventImplies commonImpliesSecond
      second.source_mutuallySingular_singular.right_inside_zero
  have firstCommon : target.measure common = first.regular.measure common := by
    rw [first.measure_eq common, firstSingularCommonZero, add_zero]
  have secondCommon : target.measure common = second.regular.measure common := by
    rw [second.measure_eq common, secondSingularCommonZero, add_zero]
  calc
    first.regular.measure event = first.regular.measure common :=
      firstEventCommon
    _ = target.measure common := firstCommon.symm
    _ = second.regular.measure common := secondCommon
    _ = second.regular.measure event := secondEventCommon.symm

/-- Any two decompositions of the same target relative to the same source have equal singular-part event measurements.
-/
theorem singular_measure_eq {α : Type}
    {target source : Content α}
    (first second : LebesgueDecomposition target source)
    (event : α → Bool) :
    first.singular.measure event = second.singular.measure event := by
  have regularEqual := first.regular_measure_eq second event
  calc
    first.singular.measure event =
        target.measure event - first.regular.measure event := by
      rw [first.measure_eq event]
      ring1
    _ = target.measure event - second.regular.measure event := by
      rw [regularEqual]
    _ = second.singular.measure event := by
      rw [second.measure_eq event]
      ring1

/-- Every retained regular-part measurement equals that of the exact canonical source-support restriction. -/
theorem regular_measure_eq_canonical {α : Type} [DecidableEq α]
    {target source : Content α}
    (decomposition : LebesgueDecomposition target source)
    (event : α → Bool) :
    decomposition.regular.measure event =
      (target.lebesgueRegularPart source).measure event := by
  exact decomposition.regular_measure_eq
    (target.lebesgueDecomposition source) event

/-- Every retained singular-part measurement equals that of the exact canonical source-null restriction. -/
theorem singular_measure_eq_canonical {α : Type} [DecidableEq α]
    {target source : Content α}
    (decomposition : LebesgueDecomposition target source)
    (event : α → Bool) :
    decomposition.singular.measure event =
      (target.lebesgueSingularPart source).measure event := by
  exact decomposition.singular_measure_eq
    (target.lebesgueDecomposition source) event

end LebesgueDecomposition

end Content

end Purelib.Measure

end
