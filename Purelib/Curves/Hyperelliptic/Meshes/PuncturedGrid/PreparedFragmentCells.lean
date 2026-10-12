module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Integration.PreparedParentSplitting
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Riemann.Integration.PreparedConstantModels

section

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

public section

/-!
# Actual cells containing the split standard-period fragments

The midpoint locator reads the retained framed grid. Since the parameter
partition contains every grid-line crossing, both fragment endpoints are in
that same closed cell. Location does not assert that the cell is regular or
select a root sheet; those are separate properties of the retained face bank.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Integration
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts (crossings crossings_mono)
open Purelib.Riemann.Branches
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval)
open Purelib.Riemann.Paths
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid
    curve.polynomial ambient} {axes :
    PrimitiveAxes grid}

namespace PrimitiveAxes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)

/-- Each crossing with an original retained vertical grid coordinate belongs to the parent's full split-parameter list.
-/
private theorem vertical_parameters (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source)
    {cut : Fraction.Rational} (present : cut ∈ axes.vertical) {parameter : Fraction.Rational}
    (member : parameter ∈ PreparedSegmentCuts.crossings (parent.edge.point 0).re
      ((parent.edge.point 1).re - (parent.edge.point 0).re) [cut]) : parameter ∈ axes.parameters parent := by
  apply List.mem_append_left
  exact PreparedSegmentCuts.crossings_mono _ _ (fun point member => Membership.mem_singleton.mp member ▸ present) _
    member

/-- Each crossing with an original retained horizontal grid coordinate belongs to the parent's full split-parameter
list. -/
private theorem horizontal_parameters (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source)
    {cut : Fraction.Rational} (present : cut ∈ axes.horizontal) {parameter : Fraction.Rational}
    (member : parameter ∈ PreparedSegmentCuts.crossings (parent.edge.point 0).im
      ((parent.edge.point 1).im - (parent.edge.point 0).im) [cut]) : parameter ∈ axes.parameters parent := by
  apply List.mem_append_right
  exact PreparedSegmentCuts.crossings_mono _ _ (fun point member => Membership.mem_singleton.mp member ▸ present) _
    member

/-- The selected actual cell contains the whole affine fragment, rather than only the point used by the finite locator.
-/
theorem cell_endpoints (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) {interval :
      PreparedAxisPartitions.Interval}
    (member : interval ∈ partition.intervals) {cell : ClearGrid.Cell curve.polynomial ambient} (cellMember : cell ∈
      grid.cells)
    (middleInside : cell.box.Contains (parent.edge.point ((interval.lower + interval.upper) / 2))) :
    cell.box.Contains (parent.edge.point interval.lower) ∧ cell.box.Contains (parent.edge.point interval.upper) := by
  obtain ⟨horizontal, horizontalMember, row⟩ := Flatten.mem_flatMap.mp cellMember
  obtain ⟨vertical, verticalMember, rfl⟩ := Map.mem_map.mp row
  have xs := Interval.endpoints_mem grid.vertical grid.vertical_ordered horizontalMember
  have ys := Interval.endpoints_mem grid.horizontal grid.horizontal_ordered verticalMember
  have xIncluded : ∀ cut ∈ [horizontal.lower.coordinate, horizontal.upper.coordinate],
      ∀ parameter ∈ PreparedSegmentCuts.crossings (parent.edge.point 0).re
        ((parent.edge.point 1).re - (parent.edge.point 0).re) [cut], parameter ∈ axes.parameters parent := by
    intro cut present parameter belongs
    apply vertical_parameters axes parent
      _ belongs
    rw [axes.vertical_eq]
    rcases Membership.mem_cons.mp present with rfl | present
    · exact Map.mem_map.mpr ⟨horizontal.lower, xs.1, rfl⟩
    · have equal := Membership.mem_singleton.mp present
      rw [equal]
      exact Map.mem_map.mpr ⟨horizontal.upper, xs.2, rfl⟩
  have yIncluded : ∀ cut ∈ [vertical.lower.coordinate, vertical.upper.coordinate],
      ∀ parameter ∈ PreparedSegmentCuts.crossings (parent.edge.point 0).im
        ((parent.edge.point 1).im - (parent.edge.point 0).im) [cut], parameter ∈ axes.parameters parent := by
    intro cut present parameter belongs
    apply horizontal_parameters axes
      parent _ belongs
    rw [axes.horizontal_eq]
    rcases Membership.mem_cons.mp present with rfl | present
    · exact Map.mem_map.mpr ⟨vertical.lower, ys.1, rfl⟩
    · have equal := Membership.mem_singleton.mp present
      rw [equal]
      exact Map.mem_map.mpr ⟨vertical.upper, ys.2, rfl⟩
  rw [PreparedParentSplitting.prepared_point_eq] at middleInside
  have xBounds := PreparedSegmentCuts.coordinate_bounds partition member _ _ _ _ xIncluded
    ⟨middleInside.1, middleInside.2.1⟩
  have yBounds := PreparedSegmentCuts.coordinate_bounds partition member _ _ _ _ yIncluded
    ⟨middleInside.2.2.1, middleInside.2.2.2⟩
  constructor <;> rw [PreparedParentSplitting.prepared_point_eq]
  · exact ⟨xBounds.1.1, xBounds.1.2, yBounds.1.1, yBounds.1.2⟩
  · exact ⟨xBounds.2.1, xBounds.2.2, yBounds.2.1, yBounds.2.2⟩

end PrimitiveAxes

set_option genInjectivity false in
/-- The retained cell and endpoints for one parent fragment.

The selected cell contains both endpoints and the complete affine fragment.
The indices and bounds refer to the original parent and splitting interval. -/
structure PrimitiveFragmentCell (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) (interval :
      PreparedAxisPartitions.Interval) where
  /-- The original interval belongs to its retained parent partition. -/ member : interval ∈ partition.intervals
  /-- The cached actual grid cell containing the original fragment. -/ cell : ClearGrid.Cell curve.polynomial ambient
  /-- The cached fragment cell belongs to the original retained grid. -/ cell_member : cell ∈ grid.cells
  /-- The cached original fragment starting point. -/ first : Data.Gaussian.Basic.Canonical
  /-- The cached start equals the original parent point at the retained lower partition endpoint. -/ first_eq : first =
    parent.edge.point interval.lower
  /-- The cached original fragment finishing point. -/ last : Data.Gaussian.Basic.Canonical
  /-- The cached finish equals the original parent point at the retained upper partition endpoint. -/ last_eq : last =
    parent.edge.point interval.upper
  /-- The original fragment start belongs to the cached cell. -/ first_inside : cell.box.Contains first
  /-- The original fragment finish belongs to the same cached cell. -/ last_inside : cell.box.Contains last

constructive_injectivity PrimitiveFragmentCell

namespace PrimitiveFragmentCell

variable {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
  curve.polynomial.natDegree}

/-- Locate the original fragment midpoint in the retained framed grid and certify both original endpoints in that same
cell. -/
@[expose] def build (bank : Branches.FramedBranchCellBank curve branches higher) (axes :
  PreparedPrimitiveSplits.PrimitiveAxes bank.grid)
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve source) (partition : Geometry.Rectangle.AxisPartition 0 1
      (axes.parameters parent))
    (interval : PreparedAxisPartitions.Interval) (member : interval ∈ partition.intervals)
    (inside : (Cuts.Ambient curve).Contains (parent.edge.point 0) ∧
      (Cuts.Ambient curve).Contains (parent.edge.point 1)) :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell axes parent partition
        interval := by
  let parameter := (interval.lower + interval.upper) / 2
  have bounds := partition.interval_bounds member
  have middle := PreparedSegmentCuts.midpoint_bounds interval
  have parameterInside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨bounds.1.trans middle.1.le, middle.2.le.trans bounds.2⟩
  let found := bank.locate (parent.edge.point parameter)
    (PreparedPrimitivePaths.point_inside_of_endpoints parent _ inside.1 inside.2 parameterInside)
  have endpoints := Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveAxes.cell_endpoints axes
    parent partition member found.member found.contains
  exact ⟨member, found.cell, found.member, parent.edge.point interval.lower, rfl,
    parent.edge.point interval.upper, rfl, endpoints.1, endpoints.2⟩

end PrimitiveFragmentCell

set_option genInjectivity false in
/-- Cell locations for every retained partition interval.

The dependent spine keeps each interval and its cell certificate in the
original partition order, including repeated parent occurrences. -/
inductive PrimitiveFragmentCells (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source)
    (partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)) : List PreparedAxisPartitions.Interval →
      Type
  /-- The empty original interval list retains no fragment locations. -/ | nil :
    PrimitiveFragmentCells axes parent partition
    []
  /-- Retain the original head interval location followed by the exact original interval tail. -/ | cons {interval :
    PreparedAxisPartitions.Interval} {intervals : List PreparedAxisPartitions.Interval}
      (head : PrimitiveFragmentCell axes parent
        partition interval) (tail :
        PrimitiveFragmentCells axes parent
        partition intervals) :
      PrimitiveFragmentCells axes parent
        partition (interval :: intervals)

constructive_injectivity PrimitiveFragmentCells

namespace PrimitiveFragmentCells

variable {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
  curve.polynomial.natDegree}

/-- Locate every original partition interval in order, retaining the actual grid cells and original endpoint
certificates. -/
@[expose] def build (bank : Branches.FramedBranchCellBank curve branches higher) (axes :
  PreparedPrimitiveSplits.PrimitiveAxes bank.grid)
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve source) (partition : Geometry.Rectangle.AxisPartition 0 1
      (axes.parameters parent))
    (inside : (Cuts.Ambient curve).Contains (parent.edge.point 0) ∧ (Cuts.Ambient curve).Contains (parent.edge.point 1))
      :
    (intervals : List PreparedAxisPartitions.Interval) → (∀ interval ∈ intervals, interval ∈ partition.intervals) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCells axes parent partition
        intervals
  | [], _ => .nil
  | interval :: intervals, members =>
      .cons (Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell.build bank axes
        parent partition interval (members _ List.mem_cons_self) inside)
        (build bank axes
          parent partition inside intervals (fun interval member => members interval (List.mem_cons_of_mem _ member)))

end PrimitiveFragmentCells

set_option genInjectivity false in
/-- Cell locations indexed by the exact parent splitting spine.

Every repeated parent occurrence retains the locations of all its primitive
fragments, with the original parent and interval identities. -/
inductive LocatedPrimitiveSplits (axes : PreparedPrimitiveSplits.PrimitiveAxes grid) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} → PreparedPrimitiveSplits.PrimitiveSplits
      axes parents → Type
  /-- The empty original parent splitting has no retained fragment cells. -/ | nil :
    LocatedPrimitiveSplits axes .nil
  /-- Retain all original head-parent fragment locations and the exact matching split tail. -/ | cons {parent :
    PreparedSubdivisionModelCore.CenteredEdge curve source} {parents : List (PreparedSubdivisionModelCore.CenteredEdge
    curve source)}
      {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)} {splits :
        PreparedPrimitiveSplits.PrimitiveSplits axes parents}
      (head : PrimitiveFragmentCells axes parent
        partition partition.intervals) (tail :
        LocatedPrimitiveSplits axes splits) :
      LocatedPrimitiveSplits axes (.cons
        partition splits)

constructive_injectivity LocatedPrimitiveSplits

namespace LocatedPrimitiveSplits

variable {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 <
  curve.polynomial.natDegree}

/-- Locate the fragments of every original parent splitting, preserving repeated parent occurrences and the exact
partition spine. -/
@[expose] def build (bank : Branches.FramedBranchCellBank curve branches higher) (axes :
  PreparedPrimitiveSplits.PrimitiveAxes bank.grid) :
    ∀ {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (splits :
      PreparedPrimitiveSplits.PrimitiveSplits axes parents),
      (∀ parent ∈ parents, (Cuts.Ambient curve).Contains (parent.edge.point 0) ∧
        (Cuts.Ambient curve).Contains (parent.edge.point 1)) →
          Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.LocatedPrimitiveSplits axes splits
  | _, .nil, _ => .nil
  | _, .cons (parent := parent) partition tail, inside =>
      .cons (Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCells.build bank axes
        parent partition (inside _ List.mem_cons_self) partition.intervals (fun _ member => member))
        (build bank axes
          tail (fun parent member => inside parent (List.mem_cons_of_mem _ member)))

end LocatedPrimitiveSplits
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
