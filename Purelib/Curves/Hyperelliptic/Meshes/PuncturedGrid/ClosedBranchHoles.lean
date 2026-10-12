module
import Purelib.Data.List.Membership
import Purelib.Data.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ValuationAreas
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedClosedSurfaceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleGeometry
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-! Exact zero values and areas on each physical hole lap of the closed test valuation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
open Purelib.Data.List
open Purelib.Riemann.Meshes
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles (mem_flatten)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base}
  {values : Data.Vector Purelib.Data.Gaussian.Basic.Canonical
    lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

/-- Every lifted edge of an original retained hole lap belongs to the complete physical boundary list. -/
private theorem lap_supported (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (sheet : Fin 2) (edge : Stokes.OrientedEdge lifted.vertices.count)
    (member : edge ∈ lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary sheet) :
    edge ∈ lifted.boundaryLoops.flatten := by
  have onHole : ∀ selected : Fin 2, ∀ edge ∈ lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary selected,
      edge ∈ hole.liftedBoundary lifted.vertices lifted.edges := by
    intro selected
    rw [hole.liftedBoundary_eq]
    refine Data.Fin.cases_induction ?_ (Data.Fin.cases_induction ?_ (fun impossible => Fin.elim0 impossible)) selected
    · intro edge belongs
      exact Membership.mem_append.mpr (Or.inl belongs)
    · intro edge belongs
      exact Membership.mem_append.mpr (Or.inr belongs)
  exact SimpleBoundaryCycles.mem_flatten.mpr ⟨hole.liftedBoundary lifted.vertices lifted.edges,
    Membership.mem_append.mpr (Or.inr (Map.mem_map_of_mem retained)), onHole sheet edge member⟩

/-- The closed generator valuation has zero total on either original physical hole lap. -/
theorem hole_lap_value_zero (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (sheet : Fin 2) : SewingRetraction.wordValue data.value (lifted.edges.indexedEdges lifted.vertices
      hole.inwardBoundary sheet) = 0 := by
  have zero (word : List (Stokes.OrientedEdge lifted.vertices.count))
      (supported : ∀ edge ∈ word, edge ∈ lifted.boundaryLoops.flatten) : SewingRetraction.wordValue data.value word = 0
        := by
    induction word with
    | nil => rfl
    | cons edge rest ih =>
        change data.value edge + SewingRetraction.wordValue data.value rest = 0
        rw [ValuationAreas.boundary_edge_zero data edge (supported edge List.mem_cons_self),
          ih (fun other member => supported other (List.mem_cons_of_mem _ member)), zero_add]
  exact zero _ (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles.lap_supported hole retained sheet)

/-- The closed generator valuation has zero area on either original physical hole lap. -/
theorem hole_lap_area_zero (hole : PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (retained : hole ∈
  base.faces.holes)
    (sheet : Fin 2) : RetracingWords.wordArea data.value (lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary
      sheet) = 0 :=
  ValuationAreas.boundary_area_zero data _ (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles.lap_supported
    hole retained sheet)

/-- Each retained branch-bank hole word has zero value under the original closed generator valuation. -/
theorem holeWord_value_zero (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index
  branches) (sheet : Fin 2) :
    SewingRetraction.wordValue data.value (bank.holeWord index sheet) = 0 := by
  match base.faces.locateCell (base.bank.cell index) (base.bank.cell_mem index) with
  | .regular found => exact (found.face.unassigned index found.cell_eq).elim
  | .hole found =>
      have same : found.hole.index = index := FaceKind.branch_unique found.hole.cell_eq found.cell_eq
      have retained : found.hole ∈ base.faces.holes := by
        rw [← found.indexed]
        exact List.getElem_mem found.index.isLt
      have zero : SewingRetraction.wordValue data.value (bank.holeWord found.hole.index sheet) = 0 := by
        rw [bank.holeWord_reverse found.hole, SewingRetraction.wordValue_reverse data.value data.value_reverse,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles.hole_lap_value_zero data found.hole retained _,
            neg_zero]
      exact same ▸ zero

/-- Each retained branch-bank hole area vanishes under the original closed generator valuation. -/
theorem holeArea_zero (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index branches)
  (sheet : Fin 2) :
    bank.holeArea data.value index sheet = 0 := by
  match base.faces.locateCell (base.bank.cell index) (base.bank.cell_mem index) with
  | .regular found => exact (found.face.unassigned index found.cell_eq).elim
  | .hole found =>
      have same : found.hole.index = index := FaceKind.branch_unique found.hole.cell_eq found.cell_eq
      have retained : found.hole ∈ base.faces.holes := by
        rw [← found.indexed]
        exact List.getElem_mem found.index.isLt
      have zero : bank.holeArea data.value found.hole.index sheet = 0 := by
        rw [bank.holeArea_reverse found.hole sheet data.value data.value_reverse,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles.hole_lap_area_zero data found.hole retained _,
            neg_zero]
      exact same ▸ zero

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedBranchHoles

end
