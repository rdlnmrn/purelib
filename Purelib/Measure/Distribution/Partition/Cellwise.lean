module

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Conditional expectation as a finite L2 projection

A cellwise observable carries explicit rational values for the cells of a
positive finite event partition.  The conditional-expectation residual has
zero integral on each cell, hence is orthogonal to every such observable.
Expanding one rational square yields the exact Pythagorean identity and the
best powered-L2 approximation theorem.
-/

public section

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

set_option genInjectivity false in
/-- Retain one rational value for every event cell, certifying agreement with the exact observable on selected original
atoms.

The representation is indexed by the original positive partition and observable; agreement is required only on its
retained cells and distribution occurrences. -/
structure CellwiseObservable {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) where
  /-- The exact rational value assigned to each Boolean cell. -/ cellValue : (α → Bool) → Fraction.Rational
  /-- The original observable equals the retained cell value at every selected original atom of a retained partition
    cell. -/ agrees : ∀ event, event ∈ partition.events →
    ∀ atom, atom ∈ distribution.atoms → event atom.item = true →
      value atom.item = cellValue event

constructive_injectivity CellwiseObservable

namespace CellwiseObservable

/-! Postcomposition preserves the explicit value attached to every cell. -/
/-- Apply a scalar transform to the retained cell values and the original cellwise observable. -/
@[expose]
def map {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {value : α → Fraction.Rational}
    (represented : CellwiseObservable partition value)
    (transform : Fraction.Rational → Fraction.Rational) :
    CellwiseObservable partition (fun item => transform (value item)) where
  cellValue event := transform (represented.cellValue event)
  agrees event eventMember atom atomMember selected := by
    rw [represented.agrees event eventMember atom atomMember selected]

/-- Subtract two cellwise observables using the difference of their retained values on each original cell. -/
@[expose]
def sub {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {left right : α → Fraction.Rational}
    (leftCellwise : CellwiseObservable partition left)
    (rightCellwise : CellwiseObservable partition right) :
    CellwiseObservable partition (fun item => left item - right item) where
  cellValue event := leftCellwise.cellValue event -
    rightCellwise.cellValue event
  agrees event eventMember atom atomMember selected := by
    rw [leftCellwise.agrees event eventMember atom atomMember selected,
      rightCellwise.agrees event eventMember atom atomMember selected]

end CellwiseObservable

/-- Represent the partition's exact conditional expectation by its original conditional mean on every retained cell. -/
@[expose]
def conditionalExpectation_cellwise {α : Type}
    {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) :
    CellwiseObservable partition (partition.conditionalExpectation value) where
  cellValue event := distribution.conditionalMean event value
  agrees event eventMember atom atomMember selected :=
    partition.conditionalExpectation_eq_conditionalMean_on_cell
      value event eventMember atom atomMember selected
end PositiveEventPartition

end Purelib.Measure

end

section
public section

/-!
# Finite martingale differences

Every step of a displayed finite martingale has a rational difference whose
conditional expectation on the preceding partition is zero.  Consequently
the difference is orthogonal to every explicitly cellwise observable.  A
finite induction then gives exact second-moment and variance growth formulas.

There is no unbounded time index, limiting process, or stopping theorem here:
the expected quadratic variation below is a finite rational sum carried by
the inductive martingale itself.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition

/-- Represent the zero observable with zero value on every retained partition cell. -/
@[expose]
def zeroCellwise {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    CellwiseObservable partition (fun _ : α => (0 : Fraction.Rational)) where
  cellValue := fun _ => 0
  agrees := by
    intro event eventMember atom atomMember selected
    rfl
end PositiveEventPartition

end Purelib.Measure

end

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat

namespace PositiveEventPartition.CellwiseObservable

/-- Represent the universally true indicator with cell value one. -/
@[expose]
def indicatorTrue {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (fun _ : α => true)) where
  cellValue _ := 1
  agrees _event _eventMember _atom _atomMember _selected := rfl

/-- Represent an intersection indicator by multiplying the retained cell values of its two original indicators. -/
@[expose]
def indicatorIntersection {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {left right : α → Bool}
    (leftCellwise : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator left))
    (rightCellwise : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator right)) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (intersectionEvent left right)) where
  cellValue event :=
    leftCellwise.cellValue event * rightCellwise.cellValue event
  agrees event eventMember atom atomMember selected := by
    calc
      Distribution.indicator (intersectionEvent left right) atom.item =
          Distribution.indicator left atom.item *
            Distribution.indicator right atom.item := by
        unfold Distribution.indicator intersectionEvent
        cases left atom.item <;> cases right atom.item <;> rfl
      _ = leftCellwise.cellValue event * rightCellwise.cellValue event := by
        rw [leftCellwise.agrees event eventMember atom atomMember selected,
          rightCellwise.agrees event eventMember atom atomMember selected]

/-- Represent the complement indicator by subtracting each retained original cell value from one. -/
@[expose]
def indicatorComplement {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {event : α → Bool}
    (represented : PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator event)) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (complementEvent event)) where
  cellValue cell := 1 - represented.cellValue cell
  agrees cell cellMember atom atomMember selected := by
    calc
      Distribution.indicator (complementEvent event) atom.item =
          1 - Distribution.indicator event atom.item := by
        unfold Distribution.indicator complementEvent
        cases event atom.item <;> rfl
      _ = 1 - represented.cellValue cell := by
        rw [represented.agrees cell cellMember atom atomMember selected]

/-- Represent a threshold indicator by deciding the threshold against each retained original cell value. -/
@[expose]
def indicatorAtLeast {α : Type} {distribution : Distribution α}
    {partition : PositiveEventPartition distribution}
    {value : α → Fraction.Rational}
    (represented : PositiveEventPartition.CellwiseObservable partition value)
    (threshold : Fraction.Rational) :
    PositiveEventPartition.CellwiseObservable partition
      (Distribution.indicator (Measure.atLeastEvent threshold value)) where
  cellValue event :=
    match decide (threshold ≤ represented.cellValue event) with
    | true => 1
    | false => 0
  agrees event eventMember atom atomMember selected := by
    have same := represented.agrees event eventMember atom atomMember selected
    unfold Distribution.indicator Measure.atLeastEvent
    rw [same]
    rfl

end PositiveEventPartition.CellwiseObservable

namespace PositiveEventPartition

/-- Assert existence of a cellwise representation for the exact partition and observable. -/
@[expose]
def IsCellwiseObservable {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution)
    (value : α → Fraction.Rational) : Prop :=
  Nonempty (PositiveEventPartition.CellwiseObservable partition value)

end PositiveEventPartition

end Purelib.Measure

end
