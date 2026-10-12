module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedRegularCoverage

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The two-sheet ordered regular correction is the exact full cut-surface area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedClosedSurfaceArea

open Purelib.Topology.Polygon.Stokes

namespace BranchCellBank.CircuitPartition.RegularOccurrence

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
  {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
    frames}

/-- Read the original cached regular face at its retained position and actual local sheet. -/
theorem area_readback (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularOccurrence faces
  vertices edges)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Topology.Mesh.RetracingWords.wordArea value occurrence.word = Topology.Mesh.RetracingWords.wordArea value
      (edges.indexedEdges vertices
      (faces.regulars[occurrence.location.index.val]'occurrence.location.index.isLt).boundary occurrence.sheet) := by
  apply congrArg (Topology.Mesh.RetracingWords.wordArea value)
  rw [occurrence.word_eq, occurrence.location.indexed]
  have move (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) (member :
    cell ∈ bank.grid.cells)
      (equal : occurrence.location.face.cell = cell) :
      edges.indexedEdges vertices (Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member) occurrence.sheet =
        edges.indexedEdges vertices occurrence.location.face.boundary occurrence.sheet := by
    cases equal
    rfl
  exact move occurrence.cell occurrence.member occurrence.location.cell_eq

end BranchCellBank.CircuitPartition.RegularOccurrence

namespace LiftedPuncturedGrid.BasedBranchBank.Ordered

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  (ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

/-- All regular cells and both actual sheets are included; the independent cut readback fixes the surface owner. -/
theorem twoSheet_correction_area
    (zero : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
      ordered.prepared.partition lifted.edges lifted.vertices 0)
    (one : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
      ordered.prepared.partition lifted.edges lifted.vertices 1) :
    Topology.Mesh.RetracingWords.AreaTerm.total data.value zero.areaTerms + Topology.Mesh.RetracingWords.AreaTerm.total
      data.value one.areaTerms =
      Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.GeneratorValuation.regular_correction_areas data zero,
    Hyperelliptic.Meshes.PuncturedGrid.ClosedCircuitCorrections.GeneratorValuation.regular_correction_areas data one]
  let reading := fun (index : Fin base.faces.regulars.length) (localSheet : Fin 2) =>
    Topology.Mesh.RetracingWords.wordArea data.value (lifted.edges.indexedEdges lifted.vertices
      (base.faces.regulars[index.val]'index.isLt).boundary localSheet)
  have readback (items : List
    (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularOccurrence
    base.faces lifted.vertices lifted.edges)) :
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea data.value
        occurrence.word) items =
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => reading occurrence.location.index occurrence.sheet)
          items := by
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro occurrence member
    exact
      BranchCellBank.CircuitPartition.RegularOccurrence.area_readback
      occurrence data.value
  rw [readback, readback, ordered.twoSheet_regular_sum]
  exact (Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank.LiftedMesh.closed_area_sum
    lifted.mesh data.value data.value_reverse data.face_zero).symm.trans
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas.surface_area data).symm

end LiftedPuncturedGrid.BasedBranchBank.Ordered
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedClosedSurfaceArea
