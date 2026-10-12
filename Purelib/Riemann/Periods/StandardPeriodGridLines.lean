module
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Riemann.Periods.StandardPeriodAmbient
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Certified grid lines of the actual standard period parents

Every original segment has a fixed coordinate on a retained grid line.
The actual prepared banks and their root-subedge descendants preserve this
property, including reversed and stationary coordinate segments.
-/

namespace Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine VerticalLine)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} (grid : Polynomial.Geometry.Grid.ClearGrid
    curve.polynomial ambient)

open Purelib.Polynomial.Geometry.Grid.ClearGrid in
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid in
/-- A prepared parent has constant height or width on an actual retained grid line.

The varying coordinate need not be a grid coordinate, and the condition includes stationary and reversed segments. -/
def ParentOnLine (parent : CenteredEdge curve source) : Prop :=
  ((parent.edge.point 0).im ∈ grid.horizontal.map HorizontalLine.coordinate ∧
    (parent.edge.point 1).im = (parent.edge.point 0).im) ∨
  ((parent.edge.point 0).re ∈ grid.vertical.map VerticalLine.coordinate ∧
    (parent.edge.point 1).re = (parent.edge.point 0).re)

namespace ParentOnLine

variable {grid}

section
open Purelib.Data
open Purelib.Riemann
/-- Equal endpoint heights make every affine parent point have the same height. -/
theorem horizontal (parent : CenteredEdge curve source)
    (equal : (parent.edge.point 1).im = (parent.edge.point 0).im) (parameter : Rat.Fraction.Rational) :
    (parent.edge.point parameter).im = (parent.edge.point 0).im := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq]
  change (parent.edge.point 0).im + parameter * ((parent.edge.point 1).im - (parent.edge.point 0).im) = _
  rw [equal]
  ring1

/-- Equal endpoint horizontal coordinates make every affine parent point have the same horizontal coordinate. -/
theorem vertical (parent : CenteredEdge curve source)
    (equal : (parent.edge.point 1).re = (parent.edge.point 0).re) (parameter : Rat.Fraction.Rational) :
    (parent.edge.point parameter).re = (parent.edge.point 0).re := by
  rw [Integration.PreparedParentSplitting.prepared_point_eq]
  change (parent.edge.point 0).re + parameter * ((parent.edge.point 1).re - (parent.edge.point 0).re) = _
  rw [equal]
  ring1

end

open Purelib.Data in
/-- An actual root subedge inherits its parent's retained grid-line support.

The endpoint query locations preserve the parent's constant coordinate, including stationary parents and arbitrary
descendant direction. -/
theorem subedge {parent child : CenteredEdge curve source} (onLine : ParentOnLine grid parent)
    (relation : RootSubedge parent child) : ParentOnLine grid child := by
  rcases onLine with onLine | onLine
  · have same (parameter : Rat.Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
        (child.edge.point parameter).im = (parent.edge.point 0).im := by
      rw [← (relation.location parameter inside).point_eq]
      exact horizontal parent onLine.2 _
    exact Or.inl ⟨same 0 (by decide) ▸ onLine.1, (same 1 (by decide)).trans (same 0 (by decide)).symm⟩
  · have same (parameter : Rat.Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
        (child.edge.point parameter).re = (parent.edge.point 0).re := by
      rw [← (relation.location parameter inside).point_eq]
      exact vertical parent onLine.2 _
    exact Or.inr ⟨same 0 (by decide) ▸ onLine.1, (same 1 (by decide)).trans (same 0 (by decide)).symm⟩

end ParentOnLine

open Purelib.Polynomial.Geometry.Grid in
/-- Every entry of the retained parent list lies on an actual grid line. -/
def ParentsOnLines (grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient) : List (CenteredEdge curve
  source) → Prop
  | [] => True
  | parent :: parents => ParentOnLine grid parent ∧ ParentsOnLines grid parents

namespace ParentsOnLines

variable {grid}

/-- Append two parent lists supported on the same retained grid lines. -/
theorem append {first last : List (CenteredEdge curve source)}
    (a : ParentsOnLines grid first) (b : ParentsOnLines grid last) : ParentsOnLines grid (first ++ last) := by
  induction first with
  | nil => exact b
  | cons head tail ih => exact ⟨a.1, ih a.2⟩

/-- Every member of a line-supported parent list has retained grid-line support. -/
theorem member {parents : List (CenteredEdge curve source)} (onLines : ParentsOnLines grid parents)
    {parent : CenteredEdge curve source} (present : parent ∈ parents) : ParentOnLine grid parent := by
  induction parents with
  | nil => exact (List.not_mem_nil present).elim
  | cons head tail ih =>
      cases present with
      | head => exact onLines.1
      | tail _ present => exact ih onLines.2 present

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Riemann in
/-- Recasting the differential preserves every parent's actual grid-line support. -/
theorem recast (target : Basic.Differential genus) : ∀ {parents : List (CenteredEdge curve source)},
    ParentsOnLines grid parents → ParentsOnLines grid (parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge
      target))
  | [], _ => trivial
  | _ :: _, onLines => ⟨onLines.1, recast target onLines.2⟩

/-- A retained root-subedge block inherits the original parent's grid line. -/
private theorem block {parent : CenteredEdge curve source} (onLine : ParentOnLine grid parent) :
    ∀ {children : List (CenteredEdge curve source)}, RootSubedgeBlock parent children → ParentsOnLines grid children
  | _, .nil => trivial
  | _, .cons head tail => ⟨ParentOnLine.subedge onLine head, block onLine tail⟩

/-- A root-subedge refinement preserves grid-line support across its exact parent and child lists. -/
theorem refinement : ∀ {parents children : List (CenteredEdge curve source)},
    RootSubedgeRefinement parents children → ParentsOnLines grid parents → ParentsOnLines grid children
  | _, _, .nil, _ => trivial
  | _, _, .cons _ roots tail, onLines => ParentsOnLines.append (block onLines.1 roots) (refinement tail onLines.2)

end ParentsOnLines

open Purelib.Data in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial in
open Purelib.Polynomial.Geometry.Grid.ClearGrid in
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid in
/-- A clear segment has a constant coordinate on one of the retained grid lines. -/
private def SegmentOnLine {pathAmbient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial pathAmbient start finish) : Prop :=
  (start.im ∈ grid.horizontal.map HorizontalLine.coordinate ∧ ∀ parameter, (segment.pointAt parameter).im = start.im) ∨
  (start.re ∈ grid.vertical.map VerticalLine.coordinate ∧ ∀ parameter, (segment.pointAt parameter).re = start.re)

open Purelib.Data in
open Purelib.Data.Gaussian.Components in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial in
open Purelib.Polynomial.Geometry in
open Purelib.Polynomial.Geometry.Grid.FromStates in
/-- An axis-aligned clear segment starting at a grid vertex lies on an actual grid line. -/
private theorem segment_onLine {pathAmbient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial pathAmbient start finish) (onGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex
      grid start) :
    SegmentOnLine grid segment := by
  cases segment with
  | horizontal =>
      exact Or.inl ⟨onGrid.2, fun parameter => by
        dsimp only [ClearPath.ClearSegment.pointAt, Gaussian.Basic.add_im,
          Gaussian.Basic.sub_im, Gaussian.Scale.scale_im, Basic.point, Basic.point]
        ring1⟩
  | vertical =>
      exact Or.inr ⟨onGrid.1, fun parameter => by
        dsimp only [ClearPath.ClearSegment.pointAt, Gaussian.Basic.add_re,
          Gaussian.Basic.sub_re, Gaussian.Scale.scale_re, Basic.point, Basic.point]
        ring1⟩

open Purelib.Riemann.Integration in
/-- A prepared parent inherits the constant grid coordinate of its original clear segment. -/
private theorem parent_onLine (parent : CenteredEdge curve source) (onLine : SegmentOnLine grid parent.edge.segment) :
    ParentOnLine grid parent := by
  rcases onLine with onLine | onLine
  · apply Or.inl
    rw [PreparedConstantModels.PreparedEdge.point_zero, PreparedConstantModels.PreparedEdge.point_one, onLine.2,
      onLine.2]
    exact ⟨onLine.1, rfl⟩
  · apply Or.inr
    rw [PreparedConstantModels.PreparedEdge.point_zero, PreparedConstantModels.PreparedEdge.point_one, onLine.2,
      onLine.2]
    exact ⟨onLine.1, rfl⟩

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial in
open Purelib.Riemann in
/-- Every actual centered parent of a segment subdivision lies on its original grid line.

The proof follows the retained continuation subdivision and center states without requiring positive movement. -/
private theorem subdivision_onLines (source : Basic.Differential genus) {pathAmbient : Box} {start finish :
  Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial pathAmbient start finish) (within :
      segment.WithinAmbient)
    (sheet : Fin 2) (onLine : SegmentOnLine grid segment) :
    ∀ {left : Endpoint} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))}
      (subdivision : Subdivision segment within left owner) (centers : CenterStates curve source sheet subdivision),
      ParentsOnLines grid (centeredEdges curve source sheet subdivision centers)
  | _, _, .stop _ _, _ => trivial
  | _, _, .next _ _ _ _ _ _ remaining, centers =>
      ⟨parent_onLine grid _ onLine, subdivision_onLines source segment within sheet onLine remaining centers.2⟩

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Riemann
/-- A prepared clear path with original vertices on the grid has all centered parents on grid lines.

The segment spine and its accepted subdivisions preserve the exact grid membership of each source segment's constant
coordinate. -/
theorem prepared_onLines (source : Basic.Differential genus) (sheet : Fin 2) {pathAmbient : Box} :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial pathAmbient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (prepared : PreparedPath path
        owner),
      Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid path → ParentsOnLines grid
        (CenteredPathChain.ofPreparedPath curve source sheet
        prepared).parents
  | _, _, _, _, .nil _ _, _ => trivial
  | _, _, _, _, .cons head _ _ within first rest, onGrid => by
      change ParentsOnLines grid ((CenteredPathChain.dataOfCompleteSegment curve source sheet first).parents ++ _)
      apply ParentsOnLines.append _ (prepared_onLines source sheet rest onGrid.2)
      rw [CenteredPathChain.dataOfCompleteSegment_parents]
      exact subdivision_onLines grid source head within sheet (segment_onLine grid head onGrid.1) first.subdivision _

/-- Each supported dyadic-bank outcome retains grid-line support of its prepared parents. -/
private theorem bank_onLines (source : Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {diameter : Rat.Fraction.Rational} {positive : 0 < diameter}
    {pathAmbient : Box} {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
      curve.polynomial pathAmbient start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (bank : PreparedPath.DyadicBank depth diameter positive path owner) (onGrid :
      Polynomial.Geometry.Grid.FromStates.ContainsPathVertices grid path) :
    ParentsOnLines grid (CenteredPathChain.ofDyadicBank curve source sheet bank).parents := by
  cases bank with
  | safe checked => exact prepared_onLines grid source sheet checked.prepared onGrid
  | executed within prepared success => exact prepared_onLines grid source sheet prepared onGrid
  | executedCertified checked =>
      rw [CenteredPathChain.ofDyadicBank, CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath]
      exact prepared_onLines grid source sheet checked.prepared onGrid
  | certified certificate => exact prepared_onLines grid source sheet certificate.prepared onGrid

end

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid in
open Purelib.Riemann.Integration.PreparedOwnerClosedSchedules in
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates in
/-- The actual initial parents of a closed double-path tour lie on its retained grid lines.

The proof reads the forward, right-boundary, backward and left-boundary banks in their original order and sheet labels.
-/
theorem tour_initial_onLines (tour : ClosedBoundaryDoublePath curve) (source : Basic.Differential genus)
    (onGrid : Grid.ContainsTourVertices grid tour) : ParentsOnLines grid (ClosedBoundaryDoublePath.rootClosedInitial
      tour source).state.parents := by
  change ParentsOnLines grid (ClosedBoundaryDoublePath.schedule tour source).toDifferential.initial.parents
  rw [ClosedBoundaryDoublePath.schedule_initial_parents]
  exact (((bank_onLines grid source 0 tour.joined.data.forwardChecked onGrid.1).append
    (bank_onLines grid source 0 tour.joined.data.rightBoundaryChecked onGrid.2.1)).append
    (bank_onLines grid source 1 tour.joined.data.backwardChecked onGrid.2.2.1)).append
    (bank_onLines grid source 1 tour.joined.data.leftBoundaryChecked onGrid.2.2.2)

end Purelib.Riemann.Periods.StandardPeriodGridLines.Grid

namespace Purelib.Riemann.Periods.StandardPeriodGridLines.IntersectionRow

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index : Fin genus} (row : IntersectionRow
    lifted integral index)

section
open Purelib.Riemann.Periods.StandardPeriodGridLines
/-- The original A-period parents of an intersection row lie on the retained branch grid. -/
theorem a_initial_onLines : Grid.ParentsOnLines base.bank.grid row.period.aInitial.state.parents := by
  rw [row.period.aInitial_eq, PreparedCycleModels.OwnerClosedCyclePair.aInitial_state]
  apply Grid.tour_initial_onLines
  rw [← row.source_eq]
  exact row.pair.aOnGrid

/-- The original B-period parents of an intersection row lie on the retained branch grid. -/
theorem b_initial_onLines : Grid.ParentsOnLines base.bank.grid row.period.bInitial.state.parents := by
  rw [row.period.bInitial_eq, PreparedCycleModels.OwnerClosedCyclePair.bInitial_state]
  apply Grid.tour_initial_onLines
  rw [← row.source_eq]
  exact row.pair.bOnGrid

end

/-- Every scheduled A-period stage retains the original branch-grid line support. -/
theorem a_stage_onLines (stage : Nat) : Grid.ParentsOnLines base.bank.grid (row.period.aState stage).state.parents :=
  Grid.ParentsOnLines.refinement (row.period.aInitial.statesSubedges (standardDifferentials genus) stage)
    (a_initial_onLines row)

/-- Every scheduled B-period stage retains the original branch-grid line support. -/
theorem b_stage_onLines (stage : Nat) : Grid.ParentsOnLines base.bank.grid (row.period.bState stage).state.parents :=
  Grid.ParentsOnLines.refinement (row.period.bInitial.statesSubedges (standardDifferentials genus) stage)
    (b_initial_onLines row)

end Purelib.Riemann.Periods.StandardPeriodGridLines.IntersectionRow
