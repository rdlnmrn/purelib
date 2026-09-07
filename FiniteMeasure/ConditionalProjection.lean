import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.PartitionExpectation
import FiniteMeasure.PoweredLp

/-!
# Conditional expectation as a finite L2 projection

A cellwise observable carries explicit rational values for the cells of a
positive finite event partition.  The conditional-expectation residual has
zero integral on each cell, hence is orthogonal to every such observable.
Expanding one rational square yields the exact Pythagorean identity and the
best powered-L2 approximation theorem.
-/

namespace FiniteMeasure

namespace PositiveEventPartition

/-- Explicit evidence that an observable is constant on every displayed
partition cell, up to rows carrying no special quotient construction. -/
structure CellwiseObservable {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) where
  cellValue : (α → Bool) → Coordinate
  agrees : ∀ event, event ∈ partition.events →
    ∀ atom, atom ∈ distribution.atoms → event atom.item = true →
      value atom.item = cellValue event

namespace CellwiseObservable

/-! Postcomposition preserves the explicit value attached to every cell. -/
def map {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {value : α → Coordinate}
    (represented : CellwiseObservable partition value)
    (transform : Coordinate → Coordinate) :
    CellwiseObservable partition (fun item => transform (value item)) where
  cellValue event := transform (represented.cellValue event)
  agrees event eventMember atom atomMember selected := by
    rw [represented.agrees event eventMember atom atomMember selected]

def sub {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {left right : α → Coordinate}
    (leftCellwise : CellwiseObservable partition left)
    (rightCellwise : CellwiseObservable partition right) :
    CellwiseObservable partition (fun item => left item - right item) where
  cellValue event := leftCellwise.cellValue event -
    rightCellwise.cellValue event
  agrees event eventMember atom atomMember selected := by
    rw [leftCellwise.agrees event eventMember atom atomMember selected,
      rightCellwise.agrees event eventMember atom atomMember selected]

end CellwiseObservable

/-- Conditional expectation has the displayed conditional mean as its value
on each cell. -/
def conditionalExpectation_cellwise {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) :
    CellwiseObservable partition (partition.conditionalExpectation value) where
  cellValue event := distribution.conditionalMean event value
  agrees event eventMember atom atomMember selected :=
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom atomMember selected

private theorem eventIntegral_residual_eq_zero {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Coordinate) (event : α → Bool)
    (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event (fun item =>
      value item - partition.conditionalExpectation value item) = 0 := by
  have preserved :=
    partition.eventIntegral_conditionalExpectation value event eventMember
  unfold Distribution.eventIntegral at preserved
  unfold Distribution.eventIntegral
  calc
    distribution.expectation (fun item => Distribution.indicator event item *
          (value item - partition.conditionalExpectation value item)) =
        distribution.expectation (fun item =>
          Distribution.indicator event item * value item -
            Distribution.indicator event item *
              partition.conditionalExpectation value item) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          Distribution.indicator event item * value item) -
        distribution.expectation (fun item =>
          Distribution.indicator event item *
            partition.conditionalExpectation value item) :=
      distribution.expectation_sub _ _
    _ = 0 := by
      rw [preserved]
      ring1

/-- Cellwise orthogonality on one displayed cell. -/
private theorem eventIntegral_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Coordinate)
    (represented : CellwiseObservable partition cellwise)
    (event : α → Bool) (eventMember : event ∈ partition.events) :
    distribution.eventIntegral event (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item) = 0 := by
  unfold Distribution.eventIntegral
  calc
    distribution.expectation (fun item =>
          Distribution.indicator event item *
            ((value item - partition.conditionalExpectation value item) *
              cellwise item)) =
        distribution.expectation (fun item =>
          represented.cellValue event *
            (Distribution.indicator event item *
              (value item - partition.conditionalExpectation value item))) := by
      apply distribution.expectation_congr_off_zero
      intro atom atomMember
      apply Or.inr
      change Distribution.indicator event atom.item *
          ((value atom.item -
              partition.conditionalExpectation value atom.item) *
            cellwise atom.item) =
        represented.cellValue event *
          (Distribution.indicator event atom.item *
            (value atom.item -
              partition.conditionalExpectation value atom.item))
      cases selected : event atom.item
      · simp only [Distribution.indicator, selected, zero_mul]
        ring1
      · rw [represented.agrees event eventMember atom atomMember selected]
        simp only [Distribution.indicator, selected, one_mul]
        ring1
    _ = represented.cellValue event *
        distribution.expectation (fun item =>
          Distribution.indicator event item *
            (value item - partition.conditionalExpectation value item)) :=
      distribution.expectation_scale _ _
    _ = represented.cellValue event *
        distribution.eventIntegral event (fun item =>
          value item - partition.conditionalExpectation value item) := rfl
    _ = 0 := by
      rw [partition.eventIntegral_residual_eq_zero value event eventMember,
        mul_zero]

private theorem sum_eventIntegral_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Coordinate)
    (represented : CellwiseObservable partition cellwise) :
    ∀ events : List (α → Bool),
      (∀ event, event ∈ events → event ∈ partition.events) →
      (events.map fun event => distribution.eventIntegral event (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item)).sum = 0
  | [], subset => rfl
  | event :: remaining, subset => by
      simp only [List.map_cons, List.sum_cons]
      rw [partition.eventIntegral_residual_mul_cellwise_eq_zero
          value cellwise represented event
          (subset event List.mem_cons_self),
        partition.sum_eventIntegral_residual_mul_cellwise_eq_zero
          value cellwise represented remaining
          (fun candidate member =>
            subset candidate (List.mem_cons_of_mem event member)),
        zero_add]

/-- The conditional-expectation residual is orthogonal to every explicitly
cellwise observable. -/
theorem expectation_residual_mul_cellwise_eq_zero
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value cellwise : α → Coordinate)
    (represented : CellwiseObservable partition cellwise) :
    distribution.expectation (fun item =>
        (value item - partition.conditionalExpectation value item) *
          cellwise item) = 0 := by
  calc
    distribution.expectation (fun item =>
          (value item - partition.conditionalExpectation value item) *
            cellwise item) =
        (partition.events.map fun event =>
          distribution.eventIntegral event (fun item =>
            (value item - partition.conditionalExpectation value item) *
              cellwise item)).sum :=
      (partition.toEventPartition.total_expectation _).symm
    _ = 0 :=
      partition.sum_eventIntegral_residual_mul_cellwise_eq_zero
        value cellwise represented partition.events
        (fun event member => member)

/-- Exact finite Pythagorean identity for conditional expectation and an
arbitrary explicitly cellwise competitor. -/
theorem expectation_sq_sub_pythagorean
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Coordinate)
    (represented : CellwiseObservable partition competitor) :
    distribution.expectation (fun item =>
        (value item - competitor item) ^ 2) =
      distribution.expectation (fun item =>
        (value item - partition.conditionalExpectation value item) ^ 2) +
      distribution.expectation (fun item =>
        (partition.conditionalExpectation value item - competitor item) ^ 2) := by
  let projected := partition.conditionalExpectation value
  let projectedCellwise := partition.conditionalExpectation_cellwise value
  let differenceCellwise := projectedCellwise.sub represented
  have orthogonal : distribution.expectation (fun item =>
      (value item - projected item) *
        (projected item - competitor item)) = 0 :=
    partition.expectation_residual_mul_cellwise_eq_zero value
      (fun item => projected item - competitor item) differenceCellwise
  calc
    distribution.expectation (fun item =>
          (value item - competitor item) ^ 2) =
        distribution.expectation (fun item =>
          (value item - projected item) ^ 2 +
            (projected item - competitor item) ^ 2 +
            2 * ((value item - projected item) *
              (projected item - competitor item))) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item =>
          (value item - projected item) ^ 2) +
        distribution.expectation (fun item =>
          (projected item - competitor item) ^ 2) := by
      rw [distribution.expectation_add, distribution.expectation_add,
        distribution.expectation_scale, orthogonal, mul_zero, add_zero]

/-- Powered-L2 Pythagorean identity, stated entirely with rational squares. -/
theorem poweredL2Distance_pythagorean
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Coordinate)
    (represented : CellwiseObservable partition competitor) :
    distribution.poweredL2Distance value competitor =
      distribution.poweredL2Distance value
          (partition.conditionalExpectation value) +
        distribution.poweredL2Distance
          (partition.conditionalExpectation value) competitor := by
  unfold Distribution.poweredL2Distance FiniteContent.poweredL2Distance
    FiniteContent.poweredL2 FiniteContent.integral
  exact partition.expectation_sq_sub_pythagorean value competitor represented

/-- Conditional expectation is the best cellwise powered-L2
approximation. -/
theorem poweredL2Distance_conditionalExpectation_le
    {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value competitor : α → Coordinate)
    (represented : CellwiseObservable partition competitor) :
    distribution.poweredL2Distance value
        (partition.conditionalExpectation value) ≤
      distribution.poweredL2Distance value competitor := by
  rw [partition.poweredL2Distance_pythagorean value competitor represented]
  exact le_add_of_nonneg_right
    (distribution.toFiniteContent.poweredL2Distance_nonnegative
      (partition.conditionalExpectation value) competitor)

end PositiveEventPartition

end FiniteMeasure
