module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemCancellation
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

@[expose] public section

/-! The literal reversed physical-hole words, independent of analytic chart comparisons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (holeArea)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_reverse)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}

/-- The original branch-hole word is the literal reversed inward boundary lift on its retained opposite sheet. -/
theorem
  holeWord_reverse
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (hole : BranchHole base.bank.toBranchCellBank) (sheet : Fin 2) :
    bank.holeWord hole.index sheet = CutPath.reverse
      (lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary
        (BranchCutLifts.otherSheet (RootEdgeBank.target lifted.edges (bank.rows.get hole.index).stem sheet))) := by
  rcases hole with ⟨index, cell, member, cellEq, state, boxEq⟩
  cases cellEq
  change lifted.edges.indexedEdges lifted.vertices (bank.rows.get index).boundary _ = _
  rw [(bank.rows.get index).boundary_eq]
  let boundary := CellBoundary.Cell.boundaryWalk (base.bank.cell index) (base.bank.cell_mem index)
  let startSheet := RootEdgeBank.target lifted.edges (bank.rows.get index).stem sheet
  have swapped := RootEdgeBank.target_odd lifted.edges boundary ((base.bank.cell index).anchor_mem (base.bank.cell_mem
    index)) 0
    ((CellBoundary.Cell.boundaryWalk_winding (base.bank.cell index) (base.bank.cell_mem index)).trans
      ((BranchCellWinding.selected_winding_four base.bank.toBranchCellBank index).trans (by decide))) startSheet
  have reversed := lifted.edges.indexedEdges_reverse lifted.vertices
    (fun point inside => (BranchCellBank.referenceAt base.bank.toBranchCellBank point inside).toLoop) boundary
      startSheet
  rw [swapped] at reversed
  have twice := congrArg CutPath.reverse reversed
  change CutPath.reverse (lifted.edges.indexedEdges lifted.vertices boundary.reverse (BranchCutLifts.otherSheet
    startSheet)) =
    CutPath.reverse (CutPath.reverse (lifted.edges.indexedEdges lifted.vertices boundary startSheet)) at twice
  rw [CutPath.reverse_reverse] at twice
  exact twice.symm

/-- An antisymmetric valuation gives the original branch-hole area as the negative actual reversed inward-lift area. -/
theorem
  holeArea_reverse
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (hole : BranchHole base.bank.toBranchCellBank) (sheet : Fin 2)
    (value : OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    bank.holeArea value hole.index sheet = -RetracingWords.wordArea value
      (lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary
        (BranchCutLifts.otherSheet (RootEdgeBank.target lifted.edges (bank.rows.get hole.index).stem sheet))) := by
  rw [BasedBranchBank.holeArea, bank.holeWord_reverse, RetracingWords.wordArea_reverse value anti]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
