import FiniteMeasure.PartitionExpectation

/-!
# Explicit finite partition refinement

A refinement here is finite data.  For every displayed coarse cell it gives
a displayed list of finer cells, proves those cells belong to the finer
partition and are disjoint, and certifies on every displayed atom that their
Boolean union is the coarse cell.  This suffices for an exact finite tower
law for conditional expectation.

There is no filtration over an infinite index and no limiting martingale.
-/

namespace FiniteMeasure

namespace Distribution

/-- Restricted integrals respect event equality away from displayed
zero-weight atoms. -/
theorem eventIntegral_congr_off_zero {α : Type}
    (distribution : Distribution α) (left right : α → Bool)
    (value : α → Coordinate)
    (equal : EqualOffZeroWeightOn distribution.atoms left right) :
    distribution.eventIntegral left value =
      distribution.eventIntegral right value := by
  unfold eventIntegral
  apply distribution.expectation_congr_off_zero
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  · apply Or.inr
    change indicator left atom.item * value atom.item =
      indicator right atom.item * value atom.item
    unfold indicator
    rw [same]

/-- Exact finite additivity of restricted integrals over an explicitly
disjoint displayed event family. -/
theorem eventIntegral_unionEvents_of_disjoint {α : Type}
    (distribution : Distribution α) (events : List (α → Bool))
    (value : α → Coordinate)
    (disjoint : MutuallyDisjointOn distribution.atoms events) :
    distribution.eventIntegral (unionEvents events) value =
      (events.map fun event =>
        distribution.eventIntegral event value).sum := by
  rw [distribution.eventIntegrals_sum]
  unfold eventIntegral
  apply distribution.expectation_congr_off_zero
  intro atom member
  apply Or.inr
  change Distribution.indicator (unionEvents events) atom.item *
      value atom.item = sumIndicators events atom.item * value atom.item
  rw [sumIndicators_eq_indicator_unionEvents_of_disjoint
    distribution.atoms disjoint atom member]

end Distribution

/-- Explicit finite certificate that `fine` refines `coarse`.  Each coarse
cell is represented by a displayed union of cells from the fine partition. -/
structure PositivePartitionRefinement {α : Type}
    {distribution : Distribution α}
    (fine coarse : PositiveEventPartition distribution) where
  cellsFor : (α → Bool) → List (α → Bool)
  cells_mem : ∀ coarseEvent, coarseEvent ∈ coarse.events →
    ∀ fineEvent, fineEvent ∈ cellsFor coarseEvent →
      fineEvent ∈ fine.events
  cells_disjoint : ∀ coarseEvent, coarseEvent ∈ coarse.events →
    MutuallyDisjointOn distribution.atoms (cellsFor coarseEvent)
  agrees_on_atoms : ∀ coarseEvent, coarseEvent ∈ coarse.events →
    ∀ atom, atom ∈ distribution.atoms →
      unionEvents (cellsFor coarseEvent) atom.item = coarseEvent atom.item

namespace PositivePartitionRefinement

private theorem sum_eventIntegrals_conditionalExpectation
    {α : Type} {distribution : Distribution α}
    (fine : PositiveEventPartition distribution)
    (value : α → Coordinate) :
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

/-- Fine conditional expectation preserves the restricted integral over a
coarse cell represented by its explicit finite group of fine cells. -/
theorem eventIntegral_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) (coarseEvent : α → Bool)
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

/-- Conditional means on every coarse cell are unchanged after first taking
the finer conditional expectation. -/
theorem conditionalMean_conditionalExpectation {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) (coarseEvent : α → Bool)
    (coarseMember : coarseEvent ∈ coarse.events) :
    distribution.conditionalMean coarseEvent
        (fine.conditionalExpectation value) =
      distribution.conditionalMean coarseEvent value := by
  unfold Distribution.conditionalMean
  rw [refinement.eventIntegral_conditionalExpectation value coarseEvent
    coarseMember]

private theorem conditionalExpectationSum_tower
    {α : Type} {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) (item : α) :
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

/-- Exact finite tower law for one explicitly certified partition
refinement. -/
theorem conditionalExpectation_tower {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) (item : α) :
    coarse.conditionalExpectation (fine.conditionalExpectation value) item =
      coarse.conditionalExpectation value item := by
  unfold PositiveEventPartition.conditionalExpectation
  exact conditionalExpectationSum_tower refinement value item coarse.events
    (fun event member => member)

/-- Along one explicit finite refinement step, finer conditional
information carries at least as much between-cell variance as coarser
information. -/
theorem variance_conditionalExpectation_mono {α : Type}
    {distribution : Distribution α}
    {fine coarse : PositiveEventPartition distribution}
    (refinement : PositivePartitionRefinement fine coarse)
    (value : α → Coordinate) :
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

end FiniteMeasure
