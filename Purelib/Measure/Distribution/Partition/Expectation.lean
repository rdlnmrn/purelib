module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Event.Family
import Purelib.Measure.Event.IndicatorFamily
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

public section

namespace Purelib.Measure

namespace EventPartition

/-- The exact partition's indicator sum equals one at each original distribution occurrence. -/
theorem sumIndicators_eq_one {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    sumIndicators partition.events atom.item = 1 := by
  rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
    distribution.atoms partition.disjoint atom member]
  simp only [-eq_self, -iff_self, Distribution.indicator, partition.covers atom member]
  rfl

/-- Every original distribution occurrence is selected by some event in the retained partition list. -/
theorem exists_selected_event {α : Type}
    {distribution : Distribution α}
    (partition : EventPartition distribution)
    (atom : Weighted α) (member : atom ∈ distribution.atoms) :
    ∃ event, event ∈ partition.events ∧ event atom.item = true := by
  have covered := partition.covers atom member
  let item := atom.item
  have findSelected : ∀ (events : List (α → Bool)),
      unionEvents events item = true →
        ∃ event, event ∈ events ∧ event item = true := by
    intro events
    induction events with
    | nil =>
        intro impossible
        simp only [-eq_self, -iff_self, unionEvents] at impossible
        exact Bool.noConfusion impossible
    | cons event remaining inductionHypothesis =>
        intro unionTrue
        cases selected : event item
        · have remainingTrue : unionEvents remaining item = true := by
            simpa only [-eq_self, -iff_self, unionEvents, unionEvent, selected, Bool.false_or]
              using unionTrue
          rcases inductionHypothesis remainingTrue with
            ⟨target, targetMember, targetSelected⟩
          exact ⟨target, List.mem_cons_of_mem event targetMember,
            targetSelected⟩
        · exact ⟨event, List.mem_cons_self, selected⟩
  exact findSelected partition.events covered

open Purelib.Data.Rat in
/-- The sum of event integrals over the exact finite partition recovers the original observable expectation. -/
theorem total_expectation {α : Type} {distribution : Distribution α}
    (partition : EventPartition distribution)
    (value : α → Fraction.Rational) :
    (partition.events.map fun event =>
        distribution.eventIntegral event value).sum =
      distribution.expectation value := by
  rw [distribution.eventIntegrals_sum]
  apply distribution.expectation_congr_off_zero
  intro atom member
  apply Or.inr
  change sumIndicators partition.events atom.item * value atom.item =
    value atom.item
  rw [partition.sumIndicators_eq_one atom member]
  ring1

end EventPartition

end Purelib.Measure

end
