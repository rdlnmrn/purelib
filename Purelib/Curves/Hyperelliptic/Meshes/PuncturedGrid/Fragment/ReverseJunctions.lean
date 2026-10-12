module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedQueryNegation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Tactic.QuotientFreeOmega
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)} {leftInterval
    rightInterval : Rectangle.Partition.PreparedAxisPartitions.Interval}
  {leftFragment : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes parent
    partition leftInterval}
  {rightFragment : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes parent
    partition rightInterval}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {count : Nat} {target : Fraction.Rational} {request : Readings.UniformPreparedRequests.LocalRequest parent count
    target}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry leftFragment
    domains request} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry rightFragment domains
    request}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

/-- Reuse the cached face frame to read either query from the other full
edge endpoint. This changes only the proof of the same retained reach. -/
theorem from_finish (right : Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource rightEntry
  mesh) {point : Gaussian.Basic.Canonical}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval point)}
    (reached : Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached
      base.faces.regulars[rightFragment.face.located.index.val].cell.box
      (vertices.owner frames right.side.edge.start) owner) :
    Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached
      base.faces.regulars[rightFragment.face.located.index.val].cell.box
      (vertices.owner frames right.side.edge.finish) owner := by
  let face := base.faces.regulars[rightFragment.face.located.index.val]
  let cached := domains.get rightFragment.face.located.index
  have cellEq : face.cell = rightFragment.face.geometry.cell :=
    (congrArg Meshes.PuncturedGridFaces.RegularFace.cell rightFragment.face.located.indexed).trans
      rightFragment.face.located.cell_eq
  have lastInside : face.cell.box.Contains (vertices.coordinate right.side.edge.finish) := by
    rw [right.side.finish_eq, cellEq]
    exact rightFragment.face.geometry.last.corner.contains
  have corner := (right.side.reached cached.models).2
  have back := Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.Reached.reverse_in_clear_box
    face.clearance (Hyperelliptic.Branches.BranchIsolation.degreePositive curve)
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank
      face.cell.box.anchor (face.cell.anchor_mem face.member)).toLoop
    face.cell.box.contains_anchor lastInside corner
  exact Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached.append back
    (Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached.append (right.side.reached cached.models).1
      reached)

/-- A certified original query junction fixes the same starting vertex
sheet across different parents and different selected incident faces. -/
theorem sheet_eq_of_reverse_query_junction
    {rightParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
    {rightPartition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters rightParent)}
    {rightFragment : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes rightParent
      rightPartition rightInterval}
    {rightRequest : Readings.UniformPreparedRequests.LocalRequest rightParent count target}
    {rightEntry : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
      rightFragment domains rightRequest}
    (left : Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource leftEntry mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource rightEntry mesh)
    (pointEq : leftFragment.located.last = rightFragment.located.first)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName leftInterval.upper left.finishInside)
      (rightParent.edge.rootName rightInterval.lower rightEntry.fractionInside))
    (startEq : leftFragment.source.start = rightFragment.source.finish) :
    vertices.sheet left.side.edge.start = vertices.sheet right.side.edge.finish := by
  have coordinateEq := left.side.start_eq.trans (startEq.trans right.side.finish_eq.symm)
  have equivalent : Gaussian.Equivalence.NamedEquivalent
      (Paths.OwnerTraceReadings.ownerName (Integration.PreparedQueryNegation.PreparedEdge.ownerAtPoint parent.edge
        leftInterval.upper left.finishInside
        leftFragment.located.last leftFragment.located.last_eq.symm))
      (Paths.OwnerTraceReadings.ownerName (Integration.PreparedQueryNegation.PreparedEdge.ownerAtPoint rightParent.edge
        rightInterval.lower rightEntry.fractionInside
        rightFragment.located.first rightFragment.located.first_eq.symm)) := by
    rw [Integration.PreparedQueryNegation.PreparedEdge.ownerAtPoint_name,
      Integration.PreparedQueryNegation.PreparedEdge.ownerAtPoint_name]
    exact roots
  let leftFace := base.faces.regulars[leftFragment.face.located.index.val]
  let rightFace := base.faces.regulars[rightFragment.face.located.index.val]
  have leftCell : leftFace.cell = leftFragment.face.geometry.cell :=
    (congrArg Meshes.PuncturedGridFaces.RegularFace.cell leftFragment.face.located.indexed).trans
      leftFragment.face.located.cell_eq
  have rightCell : rightFace.cell = rightFragment.face.geometry.cell :=
    (congrArg Meshes.PuncturedGridFaces.RegularFace.cell rightFragment.face.located.indexed).trans
      rightFragment.face.located.cell_eq
  have leftFirst : leftFace.cell.box.Contains (vertices.coordinate left.side.edge.start) := by
    rw [left.side.start_eq, leftCell]
    exact leftFragment.face.geometry.first.corner.contains
  have leftLast : leftFace.cell.box.Contains leftFragment.located.last := by
    rw [leftCell]
    exact leftFragment.last_inside
  have rightFirst : rightFace.cell.box.Contains (vertices.coordinate right.side.edge.finish) := by
    rw [right.side.finish_eq, rightCell]
    exact rightFragment.face.geometry.last.corner.contains
  have rightLast : rightFace.cell.box.Contains rightFragment.located.first := by
    rw [rightCell]
    exact rightFragment.first_inside
  let raw := leftFragment.source.edge.segment.restrict leftFragment.source.edge.withinAmbient
    0 leftFragment.source.last.parameter (by decide) leftFragment.source.last.inside
  let segment := (raw.castStart (leftFragment.source.edge.segment.pointAt_zero.trans
    left.side.start_eq.symm)).castFinish
    leftFragment.source.last.point_eq
  obtain ⟨same⟩ := Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.Reached.source_equivalent_along
    left.finish_reached (right.from_finish right.first_reached) coordinateEq pointEq equivalent
    leftFace.clearance rightFace.clearance (Hyperelliptic.Branches.BranchIsolation.degreePositive curve) segment
    (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
      (vertices.coordinate_onGrid left.side.edge.start)).toLoop
    leftFirst leftLast rightFirst rightLast
  exact Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets.VertexBank.sheet_eq_of_equivalent
    vertices frames _ _ coordinateEq same

/-- Oppositely presented complete edges agree as reversed lifted indices
only after the original query owners have been identified. -/
theorem edge_eq_of_reverse_query_junction
    {rightParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
    {rightPartition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters rightParent)}
    {rightFragment : Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.RegularPrimitiveFragment axes rightParent
      rightPartition rightInterval}
    {rightRequest : Readings.UniformPreparedRequests.LocalRequest rightParent count target}
    {rightEntry : Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment.SheetEntry
      rightFragment domains rightRequest}
    (left : Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource leftEntry mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource rightEntry mesh)
    (pointEq : leftFragment.located.last = rightFragment.located.first)
    (roots : Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName leftInterval.upper left.finishInside)
      (rightParent.edge.rootName rightInterval.lower rightEntry.fractionInside))
    (startEq : leftFragment.source.start = rightFragment.source.finish)
    (finishEq : leftFragment.source.finish = rightFragment.source.start) :
    left.side.edge = right.side.edge.reverse := by
  have sheet := left.sheet_eq_of_reverse_query_junction right pointEq roots startEq
  have targetSheet : vertices.sheet right.side.edge.finish =
      (edges.edge rightFragment.source.edge).forward.target (vertices.sheet right.side.edge.start) := by
    have indexed := congrArg (fun edge => vertices.sheet edge.finish)
      (right.side.indexed_eq rightFragment.source.edge)
    exact indexed.trans (vertices.sheet_index _ rightFragment.source.edge.vertices.2 _)
  exact (left.side.indexed_eq leftFragment.source.edge).trans
    ((congrArg (edges.indexedEdge vertices leftFragment.source.edge) (sheet.trans targetSheet)).trans
      ((edges.indexedEdge_opposite_of_endpoints vertices rightFragment.source.edge leftFragment.source.edge
        startEq finishEq
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
          rightFragment.source.edge.vertices.1).toLoop
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
          rightFragment.source.edge.vertices.2).toLoop _).trans
          (congrArg Topology.Polygon.Stokes.OrientedEdge.reverse (right.side.indexed_eq
            rightFragment.source.edge).symm)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges.SheetEntry.LiftedSource
