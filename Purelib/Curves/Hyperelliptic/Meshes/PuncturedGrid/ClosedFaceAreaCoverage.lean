module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
public import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedRegularCoverage
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Meshes

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Both retained quadrilateral sheets contribute exactly the full triangle-area sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.IndexedQuadrilateral

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Mesh.RetracingWords (Retracing wordArea wordArea_append)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

/-- Cancel the literal two diagonal occurrences without permuting the path. -/
theorem triangles_retrace {count : Nat} (quad : IndexedQuadrilaterals.IndexedQuadrilateral count) :
    RetracingWords.Retracing (quad.firstTriangle.boundary ++ quad.secondTriangle.boundary) quad.boundary :=
  ((Retracing.refl [⟨quad.first, quad.second⟩, ⟨quad.second, quad.third⟩]).append
    (Retracing.cancel quad.diagonal)).append (Retracing.refl [⟨quad.third, quad.fourth⟩, ⟨quad.fourth, quad.first⟩])

/-- An antisymmetric edge valuation with a closed first triangle splits the actual quadrilateral area into its two
retained triangle areas. -/
theorem closed_word_area {count : Nat} (quad : IndexedQuadrilaterals.IndexedQuadrilateral count)
    (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value
      edge)
    (closed : SewingRetraction.wordValue value quad.firstTriangle.boundary = 0) :
    RetracingWords.wordArea value quad.boundary = RetracingWords.wordArea value quad.firstTriangle.boundary +
      RetracingWords.wordArea value quad.secondTriangle.boundary := by
  rw [← (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.IndexedQuadrilateral.triangles_retrace
    quad).areas value anti, RetracingWords.wordArea_append, closed, IncrementArea.area_zero_left, add_zero]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.IndexedQuadrilateral

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces LiftedMesh)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ sumFin_congr)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

/-- No regular face or lifted sheet is omitted from the cached triangle spine. -/
theorem LiftedFaces.closed_area_sum {faces : List (PuncturedGridFaces.RegularFace bank)} (lifts :
  GridLiftedMesh.LiftedFaces vertices edges faces)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge)
    (closed : ∀ triangle ∈ lifts.triangles, SewingRetraction.wordValue value triangle.boundary = 0) :
    CellBoundary.sumValues (fun triangle => RetracingWords.wordArea value triangle.boundary) lifts.triangles =
      CellBoundary.sumValues (fun face => RetracingWords.wordArea value (edges.indexedEdges vertices face.boundary 0) +
        RetracingWords.wordArea value (edges.indexedEdges vertices face.boundary 1)) faces := by
  induction lifts with
  | nil => rfl
  | cons zero one tail ih =>
      have firstClosed := closed zero.quad.firstTriangle List.mem_cons_self
      have secondClosed := closed one.quad.firstTriangle
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have remaining := ih (fun triangle member => closed triangle
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))))
      have firstArea :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.IndexedQuadrilateral.closed_word_area zero.quad
        value anti firstClosed
      have secondArea :=
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.IndexedQuadrilateral.closed_word_area one.quad
        value anti secondClosed
      rw [zero.boundary_eq] at firstArea
      rw [one.boundary_eq] at secondArea
      change RetracingWords.wordArea value zero.quad.firstTriangle.boundary +
        (RetracingWords.wordArea value zero.quad.secondTriangle.boundary +
          (RetracingWords.wordArea value one.quad.firstTriangle.boundary +
            (RetracingWords.wordArea value one.quad.secondTriangle.boundary + _))) = _
      rw [remaining]
      change _ = (_ + _) + _
      rw [firstArea, secondArea]
      ring1

/-- The complete finite indexed sum reads exactly the Gaussian sum over the original ordered list. -/
private theorem indexed_sum {Item : Type} (items : List Item) (value : Item → Data.Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index : Fin items.length => value (items[index.val]'index.isLt)) = CellBoundary.sumValues
      value items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact congrArg (value head + ·) ih

/-- Exact equality on the actual face-indexed mesh, with both sheets of each cached regular cell. -/
theorem LiftedMesh.closed_area_sum {faces : PuncturedGridFaces.PuncturedFaces bank} (mesh : GridLiftedMesh.LiftedMesh
  vertices edges faces)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge)
    (closed : ∀ index, SewingRetraction.wordValue value (mesh.triangulation.faces index).boundary = 0) :
    FiniteSum.Fin.sumFin (fun index => RetracingWords.wordArea value (mesh.triangulation.faces index).boundary) =
      FiniteSum.Fin.sumFin (fun position : Fin faces.regulars.length =>
        RetracingWords.wordArea value (edges.indexedEdges vertices (faces.regulars[position.val]'position.isLt).boundary
          0) +
          RetracingWords.wordArea value (edges.indexedEdges vertices
            (faces.regulars[position.val]'position.isLt).boundary 1)) := by
  have allClosed : ∀ triangle ∈ mesh.lifts.triangles, SewingRetraction.wordValue value triangle.boundary = 0 := by
    intro triangle member
    rw [← mesh.triangles_eq] at member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have zero := closed ⟨index, bound⟩
    rw [mesh.faces_eq, equal] at zero
    exact zero
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin mesh.triangles.length => RetracingWords.wordArea value
      (mesh.triangles[index.val]'index.isLt).boundary) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [mesh.faces_eq]
    _ = CellBoundary.sumValues (fun triangle => RetracingWords.wordArea value triangle.boundary) mesh.triangles :=
      Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank.indexed_sum mesh.triangles (fun
      triangle => RetracingWords.wordArea value triangle.boundary)
    _ = _ := by
      rw [mesh.triangles_eq,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank.LiftedFaces.closed_area_sum
        mesh.lifts value anti allClosed]
      exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank.indexed_sum faces.regulars
        (fun face => RetracingWords.wordArea value (edges.indexedEdges vertices face.boundary 0) +
        RetracingWords.wordArea value (edges.indexedEdges vertices face.boundary 1))).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedFaceAreaCoverage.BranchCellBank
