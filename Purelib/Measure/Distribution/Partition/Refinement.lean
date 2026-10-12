module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Moments.Basic
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Moments
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Explicit finite partition refinement

A refinement here is finite data.  For every displayed coarse cell it gives
a displayed list of finer cells, proves those cells belong to the finer
partition and are disjoint, and certifies on every displayed atom that their
Boolean union is the coarse cell.  This suffices for an exact finite tower
law for conditional expectation.

There is no filtration over an infinite index and no limiting martingale.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

set_option genInjectivity false in
/-- Retain exact fine-cell lists decomposing every coarse cell of two positive partitions of the same distribution.

Each supplied list contains only cells of the original fine partition, is disjoint on the original atoms and has union
equal to the exact coarse event on those atoms. -/
structure PositivePartitionRefinement {α : Type}
    {distribution : Distribution α}
    (fine coarse : PositiveEventPartition distribution) where
  /-- The exact retained fine-event list assigned to each coarse event. -/ cellsFor : (α → Bool) → List (α → Bool)
  /-- Each event in an assigned list belongs to the original fine partition. -/ cells_mem : ∀ coarseEvent, coarseEvent ∈
    coarse.events →
    ∀ fineEvent, fineEvent ∈ cellsFor coarseEvent →
      fineEvent ∈ fine.events
  /-- Each assigned list is disjoint on the original distribution occurrences. -/ cells_disjoint : ∀ coarseEvent,
    coarseEvent ∈ coarse.events →
    MutuallyDisjointOn distribution.atoms (cellsFor coarseEvent)
  /-- The assigned fine-cell union equals its original coarse event at every retained occurrence. -/ agrees_on_atoms : ∀
    coarseEvent, coarseEvent ∈ coarse.events →
    ∀ atom, atom ∈ distribution.atoms →
      unionEvents (cellsFor coarseEvent) atom.item = coarseEvent atom.item

constructive_injectivity PositivePartitionRefinement

namespace PositivePartitionRefinement

/-- Fine partition conditional expectation preserves the summed event integrals over any list of its exact cells. -/
private theorem sum_eventIntegrals_conditionalExpectation
    {α : Type} {distribution : Distribution α}
    (fine : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ fine.events) →
      (events.map fun event => distribution.eventIntegral event
        (fine.conditionalExpectation value)).sum =
      (events.map fun event =>
        distribution.eventIntegral event value).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [fine.eventIntegral_conditionalExpectation value event
        (subset event List.mem_cons_self)]
      rw [sum_eventIntegrals_conditionalExpectation fine value remaining
        (fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member))]

/-- Fine partition conditional expectation preserves every retained coarse-cell integral under the supplied refinement.
-/
theorem eventIntegral_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) (coarseEvent : α → Bool)
    (coarseMember : coarseEvent ∈ coarse.events) :
    distribution.eventIntegral coarseEvent
        (fine.conditionalExpectation value) =
      distribution.eventIntegral coarseEvent value := by
  let cells := refinement.cellsFor coarseEvent
  have coarseToCells : EqualOffZeroWeightOn distribution.atoms coarseEvent
      (unionEvents cells) := by
    intro atom atomMember
    exact Or.inr
      (refinement.agrees_on_atoms coarseEvent coarseMember atom
        atomMember).symm
  have cellsToCoarse : EqualOffZeroWeightOn distribution.atoms
      (unionEvents cells) coarseEvent :=
    coarseToCells.symm
  calc
    distribution.eventIntegral coarseEvent
          (fine.conditionalExpectation value) =
        distribution.eventIntegral (unionEvents cells)
          (fine.conditionalExpectation value) :=
      distribution.eventIntegral_congr_off_zero coarseEvent
        (unionEvents cells) (fine.conditionalExpectation value) coarseToCells
    _ = (cells.map fun event => distribution.eventIntegral event
          (fine.conditionalExpectation value)).sum :=
      distribution.eventIntegral_unionEvents_of_disjoint cells
        (fine.conditionalExpectation value)
        (refinement.cells_disjoint coarseEvent coarseMember)
    _ = (cells.map fun event =>
          distribution.eventIntegral event value).sum :=
      sum_eventIntegrals_conditionalExpectation fine value cells
        (refinement.cells_mem coarseEvent coarseMember)
    _ = distribution.eventIntegral (unionEvents cells) value :=
      (distribution.eventIntegral_unionEvents_of_disjoint cells value
        (refinement.cells_disjoint coarseEvent coarseMember)).symm
    _ = distribution.eventIntegral coarseEvent value :=
      distribution.eventIntegral_congr_off_zero (unionEvents cells)
        coarseEvent value cellsToCoarse

/-- Fine partition conditional expectation preserves every retained coarse-cell conditional mean. -/
theorem conditionalMean_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) (coarseEvent : α → Bool)
    (coarseMember : coarseEvent ∈ coarse.events) :
    distribution.conditionalMean coarseEvent
        (fine.conditionalExpectation value) =
      distribution.conditionalMean coarseEvent value := by
  unfold Distribution.conditionalMean
  rw [refinement.eventIntegral_conditionalExpectation value coarseEvent
    coarseMember]

/-- Replacing an observable by its fine conditional expectation leaves the indicator-weighted mean sum over retained
coarse cells unchanged. -/
private theorem conditionalExpectationSum_tower
    {α : Type} {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) (item : α) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ coarse.events) →
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event
          (fine.conditionalExpectation value)).sum =
      (events.map fun event => Distribution.indicator event item *
        distribution.conditionalMean event value).sum
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [refinement.conditionalMean_conditionalExpectation value event
        (subset event List.mem_cons_self)]
      rw [conditionalExpectationSum_tower refinement value item remaining
        (fun candidate member =>
          subset candidate (List.mem_cons_of_mem event member))]

/-- Conditioning a fine conditional expectation on the retained coarse partition equals coarse conditional expectation
of the original observable. -/
theorem conditionalExpectation_tower {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) (item : α) :
    coarse.conditionalExpectation (fine.conditionalExpectation value) item =
      coarse.conditionalExpectation value item := by
  unfold PositiveEventPartition.conditionalExpectation
  exact conditionalExpectationSum_tower refinement value item coarse.events
    (fun event member => member)

/-- Under the retained refinement, the coarse conditional expectation's variance is at most the fine conditional
expectation's variance. -/
theorem variance_conditionalExpectation_mono {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Fraction.Rational) :
    distribution.variance (coarse.conditionalExpectation value) ≤
      distribution.variance (fine.conditionalExpectation value) := by
  calc
    distribution.variance (coarse.conditionalExpectation value) =
        distribution.variance
          (coarse.conditionalExpectation
            (fine.conditionalExpectation value)) :=
      distribution.variance_congr _ _ (fun item =>
        (refinement.conditionalExpectation_tower value item).symm)
    _ ≤ distribution.variance (fine.conditionalExpectation value) :=
      coarse.variance_conditionalExpectation_le
        (fine.conditionalExpectation value)

end PositivePartitionRefinement

end Purelib.Measure

end
