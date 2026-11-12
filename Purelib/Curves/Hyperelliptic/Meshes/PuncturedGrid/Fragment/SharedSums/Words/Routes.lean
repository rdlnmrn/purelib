module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.Words
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

/-! # Actual route endpoints in the same whole-word mesh readings

Both endpoints belong to every actual retained face occurrence of the
complete lifted edge. The original domain coverage and original finite
cell lookup locate each requested point in that same route-face mesh.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.WordPreparation

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source : Differential genus}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {frames : RootFrames base.bank.grid}
variable {vertices : VertexBank base.bank.grid} {edges : RootEdgeBank frames}
variable {mesh : LiftedMesh vertices edges base.faces} {axes : PrimitiveAxes base.bank.grid}
variable {domains : FaceDomainBank frames base.faces.regulars} {count : Nat} {target : Rational}
variable {pieces : List (LiftedFragment axes domains mesh source count target)}
variable {tolerance : Rational} {positive : 0 < tolerance} {minimum : Nat}
variable (prepared : WordPreparation pieces tolerance positive minimum) (position : Fin pieces.length)

/-- Both literal endpoints are actual mesh vertices in the supplied original routed face and sheet.

The route retains its signed edge occurrence. The original domain's
coverage supplies its cell; the whole-word split request supplies its
point membership. No zero-valued off-mesh lookup is used as evidence.
-/
theorem route_endpoints_on_mesh
    (route : MeshPathWalks.EdgeRoute mesh (pieces[position.val]'position.isLt).occurrence.side.edge) :
    (pieces[position.val]'position.isLt).first ∈
        ((MeshWords.FaceMeshBudgets.atRoute prepared.budgets route).atSheet
          route.sheet).mesh.surface.mesh.vertices ∧
      (pieces[position.val]'position.isLt).last ∈
        ((MeshWords.FaceMeshBudgets.atRoute prepared.budgets route).atSheet
          route.sheet).mesh.surface.mesh.vertices := by
  let piece := pieces[position.val]'position.isLt
  let domain := (domains.atRoute route).domain route.sheet
  let budget := (MeshWords.FaceMeshBudgets.atRoute prepared.budgets route).atSheet route.sheet
  have contained := RouteContacts.route_endpoints_inside piece route
  have endpoints := WordPoints.SegmentSplit.endpoints_mem piece.assigned.split
  let first := EnteredPaths.PeriodDomain.locate domain piece.first contained.1
  let last := EnteredPaths.PeriodDomain.locate domain piece.last contained.2
  exact ⟨budget.mesh.point_mem piece.first (wordPoints_included pieces position _ endpoints.1)
      first.column first.row (PreparedParentSplitting.Geometry.allCells_mem domain.geometry _ _) first.inside,
    budget.mesh.point_mem piece.last (wordPoints_included pieces position _ endpoints.2)
      last.column last.row (PreparedParentSplitting.Geometry.allCells_mem domain.geometry _ _) last.inside⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.WordPreparation

end
