module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence
import Purelib.Tactic.QuotientFreeOmega

/-!
# Original query junctions fix the lifted containing edge

Adjacent fragments, including those from different parents, can choose
different regular incident faces. Their
actual common query and the winding of the same retained edge prefix force
the same starting vertex sheet. This uses the original query certificates;
coordinate agreement alone is never used to identify root occurrences.
-/

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
open Purelib.Geometry
open Purelib.Geometry.Rectangle.Partition
open Purelib.Polynomial.Clearance.Box
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.FromStates
open Purelib.Polynomial.Winding
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedQueryNegation
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerLoopMonodromy
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Data.Int
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.Reached
public section

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial ClearSegment)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Riemann.Paths.ClearBoxPathWinding

/-- Change the potential used by a realized owner path along a common certified segment. Only its winding certificate
changes. -/
theorem change_box_along {polynomial : ClearPath.GaussianPolynomial} {leftBox rightBox ambient :
  Rational.Box}
    {start finish : Data.Gaussian.Basic.Canonical} {first : SquareRootContinuationChain.Owner (polynomial.eval start)}
      {last : SquareRootContinuationChain.Owner (polynomial.eval finish)}
    (reached : PreparedFaceTracePrefixes.Reached leftBox first last)
    (leftClear : Region.RegionClearance polynomial leftBox)
    (rightClear : Region.RegionClearance polynomial rightBox) (degree : 0 < polynomial.natDegree)
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (leftFirst : leftBox.Contains start) (leftLast : leftBox.Contains finish)
    (rightFirst : rightBox.Contains start) (rightLast : rightBox.Contains finish) : PreparedFaceTracePrefixes.Reached
      rightBox first last := by
  obtain ⟨trace, winding⟩ := reached
  exact ⟨trace, winding.trans ((ClearBoxPaths.segment_winding leftClear degree segment leftFirst leftLast).symm.trans
    (ClearBoxPaths.segment_winding rightClear degree segment rightFirst rightLast))⟩

/-- Equal endpoint occurrences and a common edge prefix determine equal source occurrences, even when the two retained
face choices differ.

The same-point winding difference cancels directly in the retained integer operations. The resulting zero difference
supplies the original finite equivalence witness. -/
theorem source_equivalent_along {polynomial : ClearPath.GaussianPolynomial} {leftBox rightBox ambient :
  Rational.Box}
    {leftStart rightStart leftFinish rightFinish : Data.Gaussian.Basic.Canonical}
    {first : SquareRootContinuationChain.Owner (polynomial.eval leftStart)} {second : SquareRootContinuationChain.Owner
      (polynomial.eval rightStart)}
    {last : SquareRootContinuationChain.Owner (polynomial.eval leftFinish)} {other : SquareRootContinuationChain.Owner
      (polynomial.eval rightFinish)}
    (left : PreparedFaceTracePrefixes.Reached leftBox first last) (right : PreparedFaceTracePrefixes.Reached rightBox
      second other)
    (startEq : leftStart = rightStart) (finishEq : leftFinish = rightFinish)
    (equivalent : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName last) (OwnerTraceReadings.ownerName
      other))
    (leftClear : Region.RegionClearance polynomial leftBox)
    (rightClear : Region.RegionClearance polynomial rightBox) (degree : 0 < polynomial.natDegree)
    (segment : ClearPath.ClearSegment polynomial ambient leftStart leftFinish)
    (reference : OwnerLoopMonodromy.WindingOneLoop polynomial leftStart)
    (leftFirst : leftBox.Contains leftStart) (leftLast : leftBox.Contains leftFinish)
    (rightFirst : rightBox.Contains rightStart) (rightLast : rightBox.Contains rightFinish) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName first) (OwnerTraceReadings.ownerName
      second)) := by
  cases startEq
  cases finishEq
  have shared := change_box_along right
    rightClear leftClear degree segment rightFirst rightLast leftFirst leftLast
  have back := Reached.reverse_in_clear_box
    leftClear degree reference leftFirst leftLast
    (Reached.append shared
      (Reached.ofEquivalent equivalent.symm))
  obtain ⟨loop, winding⟩ := Reached.append left back
  have zero : Polygon.Basic.chainRaw polynomial leftStart loop.vertices = 8 * (0 : Int) := by
    rewrite [winding, Int.sub_eq_add_neg, Arithmetic.add_comm, Arithmetic.neg_add_cancel]
    exact Eq.refl _
  exact ⟨(OwnerPath.rootEquivalent_of_even_with_reference
    reference loop 0 zero).symm⟩

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.Reached

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.VertexBank
public section

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

/-- Compare the actual cached frame occurrences at a common grid vertex. -/
theorem sheet_eq_of_equivalent {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box}
  {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
    (vertices : LiftedVertices.VertexBank grid) (frames : RootIsolation.SquareRoot.Grid.RootFrames grid) (first last :
        Fin vertices.count)
    (equal : vertices.coordinate first = vertices.coordinate last)
    (equivalent : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames first))
      (OwnerTraceReadings.ownerName (vertices.owner frames last))) :
    vertices.sheet first = vertices.sheet last := by
  have names : ∀ (a b : Data.Gaussian.Basic.Canonical) (aMember : Polynomial.Geometry.Grid.FromStates.ContainsVertex
    grid a) (bMember :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid b),
      a = b → ∀ sheet, OwnerTraceReadings.ownerName ((frames.frameAt a aMember).owners sheet) =
        OwnerTraceReadings.ownerName ((frames.frameAt b bMember).owners sheet) := by
    intro a b aMember bMember same sheet
    cases same
    rfl
  change Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName ((frames.frameAt _
    (vertices.coordinate_onGrid first)).owners (vertices.sheet first)))
    (OwnerTraceReadings.ownerName ((frames.frameAt _ (vertices.coordinate_onGrid last)).owners (vertices.sheet last)))
      at equivalent
  rw [names _ _ (vertices.coordinate_onGrid first) (vertices.coordinate_onGrid last) equal (vertices.sheet first)]
    at equivalent
  exact (frames.frameAt _ (vertices.coordinate_onGrid last)).distinguish _ _ equivalent

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.VertexBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource
public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry (LiftedSource)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid} {parent :
    CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}
    {leftInterval rightInterval : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}
  {leftFragment : RegularPrimitiveFragment axes
    parent partition leftInterval}
  {rightFragment : RegularPrimitiveFragment axes
    parent partition rightInterval}
  {domains : FaceDomainBank frames
    base.faces.regulars}
  {count : Nat} {target : Rational} {request :
    LocalRequest parent count target}
  {leftEntry :
    SheetEntry
    leftFragment domains request} {rightEntry :
    SheetEntry
    rightFragment domains request}
  {mesh : LiftedMesh vertices edges base.faces}

/-- A certified original query junction fixes the same starting vertex sheet across different parents and different
selected incident faces. -/
theorem sheet_eq_of_query_junction
    {rightParent : PreparedSubdivisionModelCore.CenteredEdge curve source}
    {rightPartition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters rightParent)}
    {rightFragment : RegularFaces.RegularPrimitiveFragment axes rightParent rightPartition rightInterval}
    {rightRequest : UniformPreparedRequests.LocalRequest rightParent count target}
    {rightEntry : RegularPrimitiveFragment.SheetEntry rightFragment domains rightRequest}
    (left : SheetEntry.LiftedSource leftEntry mesh) (right : SheetEntry.LiftedSource rightEntry mesh)
    (pointEq : leftFragment.located.last = rightFragment.located.first)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName leftInterval.upper left.finishInside)
      (rightParent.edge.rootName rightInterval.lower rightEntry.fractionInside))
    (startEq : leftFragment.source.start = rightFragment.source.start) :
    vertices.sheet left.side.edge.start = vertices.sheet right.side.edge.start := by
  have coordinateEq := left.side.start_eq.trans (startEq.trans right.side.start_eq.symm)
  have equivalent : Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName (PreparedEdge.ownerAtPoint parent.edge leftInterval.upper left.finishInside
        leftFragment.located.last leftFragment.located.last_eq.symm))
      (OwnerTraceReadings.ownerName (PreparedEdge.ownerAtPoint rightParent.edge rightInterval.lower
        rightEntry.fractionInside
        rightFragment.located.first rightFragment.located.first_eq.symm)) := by
    rw [PreparedEdge.ownerAtPoint_name, PreparedEdge.ownerAtPoint_name]
    exact roots
  let leftFace := base.faces.regulars[leftFragment.face.located.index.val]
  let rightFace := base.faces.regulars[rightFragment.face.located.index.val]
  have leftCell : leftFace.cell = leftFragment.face.geometry.cell :=
    (congrArg RegularFace.cell leftFragment.face.located.indexed).trans leftFragment.face.located.cell_eq
  have rightCell : rightFace.cell = rightFragment.face.geometry.cell :=
    (congrArg RegularFace.cell rightFragment.face.located.indexed).trans rightFragment.face.located.cell_eq
  have leftFirst : leftFace.cell.box.Contains (vertices.coordinate left.side.edge.start) := by
    rw [left.side.start_eq, leftCell]
    exact leftFragment.face.geometry.first.corner.contains
  have leftLast : leftFace.cell.box.Contains leftFragment.located.last := by
    rw [leftCell]
    exact leftFragment.last_inside
  have rightFirst : rightFace.cell.box.Contains (vertices.coordinate right.side.edge.start) := by
    rw [right.side.start_eq, rightCell]
    exact rightFragment.face.geometry.first.corner.contains
  have rightLast : rightFace.cell.box.Contains rightFragment.located.first := by
    rw [rightCell]
    exact rightFragment.first_inside
  let raw := leftFragment.source.edge.segment.restrict leftFragment.source.edge.withinAmbient
    0 leftFragment.source.last.parameter (by decide) leftFragment.source.last.inside
  let segment := (raw.castStart (leftFragment.source.edge.segment.pointAt_zero.trans
    left.side.start_eq.symm)).castFinish
    leftFragment.source.last.point_eq
  obtain ⟨same⟩ := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.Reached.source_equivalent_along
    left.finish_reached right.first_reached coordinateEq pointEq equivalent
    leftFace.clearance rightFace.clearance (BranchIsolation.degreePositive curve) segment
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (vertices.coordinate_onGrid left.side.edge.start)).toLoop
    leftFirst leftLast rightFirst rightLast
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.VertexBank.sheet_eq_of_equivalent
    vertices frames _ _ coordinateEq same

/-- Actual grid edges with equal original endpoint coordinates have the same indexed lift on the supplied retained
sheet. -/
private theorem indexed_eq_of_endpoints {start finish otherStart otherFinish : Data.Gaussian.Basic.Canonical}
    (first : Walks.Edge base.bank.grid start finish) (last : Walks.Edge base.bank.grid otherStart otherFinish)
    (startEq : start = otherStart) (finishEq : finish = otherFinish) (sheet : Fin 2) :
    edges.indexedEdge vertices first sheet = edges.indexedEdge vertices last sheet := by
  cases startEq
  cases finishEq
  exact edges.indexedEdge_eq vertices first last
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ first.vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ first.vertices.2).toLoop sheet

/-- The repeated complete grid edge agrees across an actual original query junction, without requiring both fragments to
share a parent. -/
theorem edge_eq_of_query_junction
    {rightParent : PreparedSubdivisionModelCore.CenteredEdge curve source}
    {rightPartition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters rightParent)}
    {rightFragment : RegularFaces.RegularPrimitiveFragment axes rightParent rightPartition rightInterval}
    {rightRequest : UniformPreparedRequests.LocalRequest rightParent count target}
    {rightEntry : RegularPrimitiveFragment.SheetEntry rightFragment domains rightRequest}
    (left : SheetEntry.LiftedSource leftEntry mesh) (right : SheetEntry.LiftedSource rightEntry mesh)
    (pointEq : leftFragment.located.last = rightFragment.located.first)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName leftInterval.upper left.finishInside)
      (rightParent.edge.rootName rightInterval.lower rightEntry.fractionInside))
    (startEq : leftFragment.source.start = rightFragment.source.start)
    (finishEq : leftFragment.source.finish = rightFragment.source.finish) : left.side.edge = right.side.edge := by
  have sheet := left.sheet_eq_of_query_junction right pointEq roots startEq
  exact (left.side.indexed_eq leftFragment.source.edge).trans
    ((congrArg (edges.indexedEdge vertices leftFragment.source.edge) sheet).trans
      ((indexed_eq_of_endpoints
        leftFragment.source.edge rightFragment.source.edge startEq finishEq _).trans
        (right.side.indexed_eq rightFragment.source.edge).symm))

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource
