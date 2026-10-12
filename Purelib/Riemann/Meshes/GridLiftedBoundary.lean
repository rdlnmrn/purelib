module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid

@[expose] public section

/-!
# Exterior and branch-hole boundary of the actual two-sheet mesh

Finite incidence on the lifted mesh agrees with the lifted exterior and all
clockwise branch-hole walks.  Sheet-dependent primitive values are allowed;
the two-sheet reindexing is proved from the shared actual root transports.
This is an exact boundary-area identity, not yet an A/B cut-polygon word or
an analytic comparison with the period programs.
-/

namespace Purelib.Riemann.Meshes

open Purelib.Geometry.Rational (Box)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeListArea edgeListArea_append triangleWedgeSum)
open Purelib.Data.Gaussian.Basic (Canonical)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (actualBoundaries)

variable {bank : BranchCellBank curve branches higher} {frames :
  RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Read the area of retained lifted face boundaries as the sum of their two-sheet walk areas.

The recursive identity preserves the face order, shared vertex bank and exact edge transports. -/
theorem GridLiftedMesh.LiftedFaces.actualBoundaries_area (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges : SquareRoot.Grid.RootEdgeBank frames)
    (primitive : Fin vertices.count → PrimitivePoint) : (faces : List (RegularFace bank)) →
    edgeListArea primitive (actualBoundaries vertices edges faces) =
      Geometry.Grid.CellBoundary.sumValues (fun face => edges.twoSheetArea vertices primitive face.boundary) faces
  | [] => rfl
  | _ :: faces => by
      rw [actualBoundaries, edgeListArea_append, edgeListArea_append, actualBoundaries_area vertices edges primitive
        faces]
      change (_ + _ + _) = (_ + _) + _
      rfl

namespace LiftedPuncturedGrid

variable {base : FramedPuncturedGrid curve branches higher}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Decompose the lifted mesh boundary area into the exterior and inward hole walk areas.

Internal shared sides and diagonals cancel using the actual root transports; both sheets contribute with their retained
primitive values. -/
theorem boundary_eq_exterior_and_holes (lifted : LiftedPuncturedGrid
  base)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    edgeListArea primitive lifted.mesh.triangulation.boundary =
      lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior +
        Geometry.Grid.CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices primitive
          hole.inwardBoundary) base.faces.holes := by
  let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
    base.bank.toBranchCellBank point member).toLoop
  let values := lifted.edges.edgeValues lifted.vertices primitive
  have walks {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk base.bank.grid start finish) :
      values.walk walk = lifted.edges.twoSheetArea lifted.vertices primitive walk :=
    lifted.edges.edgeValues_walk lifted.vertices primitive reference walk
  rw [lifted.mesh.boundary_eq_faceWalks, Meshes.GridLiftedMesh.LiftedFaces.actualBoundaries_area]
  calc
    _ = Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) base.faces.regulars :=
      Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun face _ => (walks face.boundary).symm)
    _ = values.perimeter base.bank.grid + Geometry.Grid.CellBoundary.sumValues (fun hole => values.walk
      hole.inwardBoundary) base.faces.holes :=
      base.faces.boundary_eq_exterior_sub_holes values
    _ = _ := congrArg₂ (fun first last : Gaussian.Basic.Canonical => first + last)
      ((base.bank.frame.boundary_value values).symm.trans (walks base.bank.exterior))
      (Geometry.Grid.CellBoundary.sumValues_congr _ _ _ (fun hole _ => walks hole.inwardBoundary))

open Purelib.Polynomial in
/-- Read the triangle wedge sum as exterior area plus inward hole areas on both sheets.

The equality uses the actual lifted mesh boundary and its retained vertex and edge banks. -/
theorem wedge_eq_exterior_and_holes (lifted : LiftedPuncturedGrid
  base)
    (primitive : Fin lifted.vertices.count → PrimitivePoint) :
    triangleWedgeSum primitive lifted.mesh.triangulation.faces =
      lifted.edges.twoSheetArea lifted.vertices primitive base.bank.exterior +
        Geometry.Grid.CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices primitive
          hole.inwardBoundary) base.faces.holes :=
  (lifted.mesh.wedge_eq_boundary primitive).trans (lifted.boundary_eq_exterior_and_holes primitive)

end LiftedPuncturedGrid

end Purelib.Riemann.Meshes
