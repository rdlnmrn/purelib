module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.JunctionSheets

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexOwners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Paths

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! An original query root at a grid vertex identifies the complete indexed
edge, including the correct starting sheet for the standard walk. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {axes :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    base.faces.regulars} {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Purelib.Data.Rat.Fraction.Rational}

/-- Grid edges with equal original endpoints induce the same retained indexed lifted edge on the supplied sheet. -/
private theorem indexed_eq_of_endpoints {start finish otherStart otherFinish : Data.Gaussian.Basic.Canonical}
    (first : Walks.Edge base.bank.grid start finish) (last : Walks.Edge base.bank.grid otherStart otherFinish)
    (startEq : start = otherStart) (finishEq : finish = otherFinish) (sheet : Fin 2) :
    edges.indexedEdge vertices first sheet = edges.indexedEdge vertices last sheet := by
  cases startEq
  cases finishEq
  exact edges.indexedEdge_eq vertices first last
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ first.vertices.1).toLoop
    (BranchCellBank.referenceAt base.bank.toBranchCellBank _ first.vertices.2).toLoop sheet

/-- The first actual query's root determines the sheet at either full containing-edge endpoint, even when the vertex
bank has repeated coordinates. -/
theorem first_vertex_sheet (piece : RootedWords.LiftedFragment axes domains mesh source count target) (atStart : Bool)
    (equal : vertices.coordinate (if atStart then piece.occurrence.side.edge.start else
      piece.occurrence.side.edge.finish) = piece.first)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = piece.first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      piece.firstName) :
    vertices.sheet (if atStart then piece.occurrence.side.edge.start else piece.occurrence.side.edge.finish) =
      vertices.sheet vertex := by
  obtain ⟨same⟩ := LiftedFragment.first_vertex_owner piece atStart equal
  exact VertexBank.sheet_eq_of_equivalent vertices frames _ _ (equal.trans coordinate.symm) (same.trans root.symm)

/-- Read the actual indexed edge from an original boundary root, without assuming that equal endpoint coordinates
identify its lift. -/
theorem edge_eq_of_first_vertex (piece : RootedWords.LiftedFragment axes domains mesh source count target) (atStart :
  Bool)
    {first last : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge base.bank.grid first last)
    (firstEq : (if atStart then piece.fragment.source.start else piece.fragment.source.finish) = first)
    (lastEq : (if atStart then piece.fragment.source.finish else piece.fragment.source.start) = last)
    (queryEq : piece.first = first)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      piece.firstName) :
    (if atStart then piece.occurrence.side.edge else piece.occurrence.side.edge.reverse) =
      edges.indexedEdge vertices edge (vertices.sheet vertex) := by
  have endpoint : vertices.coordinate (if atStart then piece.occurrence.side.edge.start else
    piece.occurrence.side.edge.finish) = piece.first := by
    cases atStart with
    | false => exact piece.occurrence.side.finish_eq.trans (firstEq.trans queryEq.symm)
    | true => exact piece.occurrence.side.start_eq.trans (firstEq.trans queryEq.symm)
  have sheet := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges.first_vertex_sheet piece atStart endpoint
    vertex (coordinate.trans queryEq.symm) root
  cases atStart with
  | true =>
      exact (piece.occurrence.side.indexed_eq piece.fragment.source.edge).trans
        ((congrArg (edges.indexedEdge vertices piece.fragment.source.edge) sheet).trans
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges.indexed_eq_of_endpoints
            piece.fragment.source.edge edge firstEq lastEq _))
  | false =>
      have targetSheet : vertices.sheet piece.occurrence.side.edge.finish =
          (edges.edge piece.fragment.source.edge).forward.target (vertices.sheet piece.occurrence.side.edge.start) := by
        have indexed := congrArg (fun edge => vertices.sheet edge.finish)
          (piece.occurrence.side.indexed_eq piece.fragment.source.edge)
        exact indexed.trans (vertices.sheet_index _ piece.fragment.source.edge.vertices.2 _)
      exact (congrArg OrientedEdge.reverse
        (piece.occurrence.side.indexed_eq piece.fragment.source.edge)).trans
          ((edges.indexedEdge_opposite_of_endpoints vertices piece.fragment.source.edge edge firstEq.symm lastEq.symm
            (BranchCellBank.referenceAt base.bank.toBranchCellBank _ piece.fragment.source.edge.vertices.1).toLoop
            (BranchCellBank.referenceAt base.bank.toBranchCellBank _ piece.fragment.source.edge.vertices.2).toLoop
              _).symm.trans
              (congrArg (edges.indexedEdge vertices edge) (targetSheet.symm.trans sheet)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges
