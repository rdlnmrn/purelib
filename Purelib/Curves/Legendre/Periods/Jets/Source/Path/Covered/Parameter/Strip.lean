module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Regular
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip

/-! # One cached strip-and-regular allocation for the original finite cover

The table reads only the original retained Range entries. Its positive
finite minimum is tightened once by the original regular allocation, so
the same positive scalar pays every whole-parent strip and target frame.
No source stage, selected node or query callback enters the computation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} (ranges : ParameterRange covered)

/-- One retained table of actual whole-strip bounds and its positive common regular allocation. -/
@[expose] def StripAllocation :=
  (bounds : { values : List Rational // values = List.ofFn
    (fun index : Fin parents.length => (ranges.entry index).stripBound) }) ×
  { bound : Rational // bound = min (Rat.List.Minimum.positiveMinimum bounds.val) ranges.regularBound ∧ 0 < bound }

namespace StripAllocation

variable {ranges}

/-- Cache the finite original strip-bound table and one positive minimum before all source callbacks. -/
def build (ranges : ParameterRange covered) : StripAllocation ranges := by
  let bounds := List.ofFn (fun index : Fin parents.length => (ranges.entry index).stripBound)
  have positive : 0 < Rat.List.Minimum.positiveMinimum bounds :=
    Rat.List.Minimum.positiveMinimum_pos bounds (by
      intro value member
      rcases List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
      rewrite [← equal]
      exact (ranges.entry index).stripBound_positive)
  let bound := min (Rat.List.Minimum.positiveMinimum bounds) ranges.regularBound
  exact ⟨⟨bounds, rfl⟩, ⟨bound, rfl, Order.Basic.lt_min positive ranges.regularBound_positive⟩⟩

/-- Read the same cached finite table at the original covered-parent occurrences. -/
@[expose] def bounds (allocation : StripAllocation ranges) : List Rational := allocation.1.val

/-- The cached table contains exactly the original retained per-patch whole-strip bounds. -/
theorem bounds_eq (allocation : StripAllocation ranges) : allocation.bounds = List.ofFn
    (fun index : Fin parents.length => (ranges.entry index).stripBound) := allocation.1.property

/-- Read the single positive common allocation, independent of every later source-stage request. -/
@[expose] def bound (allocation : StripAllocation ranges) : Rational := allocation.2.val

/-- The common allocation is the actual finite strip minimum tightened by the original regular allocation. -/
theorem bound_eq (allocation : StripAllocation ranges) :
    allocation.bound = min (Rat.List.Minimum.positiveMinimum allocation.bounds) ranges.regularBound :=
  allocation.2.property.1

/-- The computed common strip-and-regular allocation is strictly positive. -/
theorem bound_positive (allocation : StripAllocation ranges) : 0 < allocation.bound := allocation.2.property.2

/-- Every retained original patch's complete strip is paid by the same computed common allocation. -/
theorem bound_le_entry (allocation : StripAllocation ranges) (index : Fin parents.length) :
    allocation.bound ≤ (ranges.entry index).stripBound := by
  rewrite [allocation.bound_eq]
  have member : (ranges.entry index).stripBound ∈ allocation.bounds := by
    rewrite [allocation.bounds_eq]
    exact List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
  exact (Order.Basic.min_le_left _ _).trans (Rat.List.Minimum.positiveMinimum_le_of_mem member)

/-- The same retained allocation pays the genuine target frame's original regularity request. -/
theorem bound_le_regularBound (allocation : StripAllocation ranges) : allocation.bound ≤ ranges.regularBound := by
  rewrite [allocation.bound_eq]
  exact Order.Basic.min_le_right _ _

/-- The computed allocation also pays every original actual source and endpoint continuation. -/
theorem bound_le_bound (allocation : StripAllocation ranges) : allocation.bound ≤ ranges.bound :=
  allocation.bound_le_regularBound.trans
    (ranges.regularBound_le_shiftedBound.trans ranges.shiftedBound_le_bound)

end StripAllocation

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

end
