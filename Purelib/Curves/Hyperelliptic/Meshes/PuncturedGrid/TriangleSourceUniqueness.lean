module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Source-occurrence uniqueness on the actual lifted grid

Positive geometric area supplies injective triangle corners. Together with
the already proved oriented-edge uniqueness, this identifies retained source
indices and corners without performing another geometric lookup.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
open Purelib.Data.Rat
open Purelib.Integration.Energy
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedMesh
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)

/-- Strictly positive geometric triangle area forces its three retained corner indices to be distinct. -/
private theorem positive_corners {count : Nat} (coordinate : Fin count → Data.Gaussian.Basic.Canonical) (triangle :
  Stokes.OrientedTriangle count)
    (positive : 0 < Purelib.Integration.Energy.AffineTriangle.coordinateTriangleArea
      (coordinate triangle.first) (coordinate triangle.second) (coordinate triangle.third)) :
    Function.Injective (SewnPrimitiveFaces.corner triangle) := by
  have firstSecond : triangle.first ≠ triangle.second := by
    intro equal
    rw [equal] at positive
    have zero : AffineTriangle.coordinateTriangleArea
        (coordinate triangle.second) (coordinate triangle.second) (coordinate triangle.third) = 0 := by
      unfold AffineTriangle.coordinateTriangleArea
      rw [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rw [zero] at positive
    exact (lt_irrefl _) positive
  have secondThird : triangle.second ≠ triangle.third := by
    intro equal
    rw [equal] at positive
    have zero : AffineTriangle.coordinateTriangleArea
        (coordinate triangle.first) (coordinate triangle.third) (coordinate triangle.third) = 0 := by
      unfold AffineTriangle.coordinateTriangleArea
      rw [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rw [zero] at positive
    exact (lt_irrefl _) positive
  have firstThird : triangle.first ≠ triangle.third := by
    intro equal
    rw [equal] at positive
    have zero : AffineTriangle.coordinateTriangleArea
        (coordinate triangle.third) (coordinate triangle.second) (coordinate triangle.third) = 0 := by
      unfold AffineTriangle.coordinateTriangleArea
      rw [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rw [zero] at positive
    exact (lt_irrefl _) positive
  intro first last equal
  rcases first with ⟨first, firstBound⟩
  rcases last with ⟨last, lastBound⟩
  have firstCases : first = 0 ∨ first = 1 ∨ first = 2 := by omega
  have lastCases : last = 0 ∨ last = 1 ∨ last = 2 := by omega
  rcases firstCases with rfl | rfl | rfl <;> rcases lastCases with rfl | rfl | rfl <;>
    first | rfl | exact (firstSecond equal).elim | exact (secondThird equal).elim |
      exact (firstThird equal).elim | exact (firstSecond equal.symm).elim |
      exact (secondThird equal.symm).elim | exact (firstThird equal.symm).elim

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}

/-- Each actual lifted grid triangle has injective corner indices. -/
theorem LiftedMesh.corners_injective
    (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (index : Fin mesh.triangles.length) :
    Function.Injective (SewnPrimitiveFaces.corner (mesh.triangulation.faces index)) :=
  positive_corners vertices.coordinate _
    (mesh.face_positive index)

/-- Two positive source occurrences projecting to the same actual lifted edge are identical. -/
theorem
  LiftedMesh.source_eq_of_project_eq
    (mesh : GridLiftedMesh.LiftedMesh vertices edges faces)
    {first last : SewnPrimitiveContacts.SourceEdge mesh.triangles.length}
    (firstPositive : SourceEdge.Positive first mesh.triangulation.faces)
    (lastPositive : SourceEdge.Positive last mesh.triangulation.faces)
    (equal : first.project mesh.triangulation.faces = last.project mesh.triangulation.faces) : first = last :=
  SourceEdge.eq_of_project_eq
    mesh.orientedEdges_unique
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.corners_injective mesh)
    firstPositive lastPositive equal

/-- The retained edge location identifies a positive occurrence of its actual lifted triangle. -/
theorem
  LiftedFaces.EdgeLocation.sourceEdge_positive
    {edge : Stokes.OrientedEdge vertices.count}
    (location : LiftedFaces.EdgeLocation mesh.lifts edge) :
      Purelib.Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive location.sourceEdge mesh.triangulation.faces :=
        by
  unfold SourceEdge.Positive SewnPrimitiveContacts.SourceEdge.project LiftedFaces.EdgeLocation.sourceEdge
  rw [mesh.triangleIndex_face]
  cases location.kind <;> first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

namespace LiftedMesh

/-- Canonical edge routing recovers any certified positive source occurrence with the same projection. -/
theorem
  EdgeRoute.build_sourceEdge
    (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (edge : Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
    (positive : SourceEdge.Positive source mesh.triangulation.faces)
    (equal : source.project mesh.triangulation.faces = edge) :
    (EdgeRoute.build mesh edge supported).sourceEdge = source := by
  have member : edge ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces :=
    equal ▸ SourceEdge.member positive
  rw [EdgeRoute.build, dif_pos member]
  exact source_eq_of_project_eq mesh
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
      (mesh.locateEdge edge member)) positive
    ((mesh.locateEdge edge member).sourceEdge_project.trans equal.symm)

namespace RouteSpine

/-- A semantic certificate for generated spines, independent of the canonical route lookup and of all root preparation
or primitive accuracy. -/
@[expose] def
  Positive
    {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word) : Prop :=
  ∀ source ∈ spine.values (fun _ route => route.sourceEdge),
    SourceEdge.Positive source mesh.triangulation.faces

/-- Projecting the exact source-occurrence list of a retained route spine recovers its original edge word. -/
theorem
  sources_project
  :
    ∀ {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word),
      (spine.values (fun _ route => route.sourceEdge)).map (fun source => source.project mesh.triangulation.faces) =
        word
  | _, .nil => rfl
  | _, .cons head tail => congrArg₂ List.cons head.sourceEdge_project
      (sources_project
        tail)

/-- A positive retained route spine has exactly the supplied positive source list when their projected words agree. -/
theorem sources_eq {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word)
    (positive : Positive spine)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length))
    (sourcePositive : ∀ source ∈ sources,
      SourceEdge.Positive source mesh.triangulation.faces)
    (equal : sources.map (fun source => source.project mesh.triangulation.faces) = word) :
    spine.values (fun _ route => route.sourceEdge) = sources :=
  SourceEdge.list_eq_of_project_eq
    mesh.orientedEdges_unique
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.corners_injective mesh) _ _ positive
      sourcePositive
    (sources_project spine
      |>.trans equal.symm)

/-- Canonical routing preserves any checked positive source list. The list may come from a generated cut assembly;
equality with its lookup is proved, not required of the producer. Repeated path occurrences remain repeated. -/
theorem build_sources (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (sources : List
  (SewnPrimitiveContacts.SourceEdge mesh.triangles.length))
    (positive : ∀ source ∈ sources,
      SourceEdge.Positive source mesh.triangulation.faces)
    (word : List (Stokes.OrientedEdge vertices.count)) (equal : sources.map (fun source => source.project
      mesh.triangulation.faces) = word)
    (supported : CutPath.Supported
      (Stokes.triangleEdgeOccurrences mesh.triangulation.faces) word) :
    (RouteSpine.build mesh word supported).values
      (fun _ route => route.sourceEdge) = sources := by
  subst word
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      exact congrArg₂ List.cons
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.EdgeRoute.build_sourceEdge
          mesh _ _ source (positive source List.mem_cons_self) rfl)
        (ih (fun next member => positive next (List.mem_cons_of_mem _ member)) _)

/-- Reading primitive increments after collecting route sources equals reading those exact increments directly along the
spine. -/
theorem source_increments (localValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    ∀ {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word),
      (spine.values (fun _ route => route.sourceEdge)).map (fun source => source.increment localValues) =
        spine.values (fun _ route => route.sourceEdge.increment localValues)
  | _, .nil => rfl
  | _, .cons head tail => congrArg (List.cons (head.sourceEdge.increment localValues))
    (source_increments
    localValues tail)

end RouteSpine
end LiftedMesh

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness

end
