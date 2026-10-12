module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
public import Purelib.Riemann.Meshes.GridLiftedWalkConnections
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Riemann.Integration.PuncturedVertexConnections
import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Topology.Polygon.Stokes
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Tactic.QuotientFreeOmega

open Purelib
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

public section

/-!
# Automatic global dual connectivity of the actual lifted punctured grid

Every retained triangle is decoded to its regular cell and anchor sheet.
The outer-frame star provides a regular root face. The existing winding-one
grid connector joins the requested sheets, and the constructed edge/vertex
interpretation turns that actual skeleton walk into a dual-face walk.
Neither dual connectivity nor a successful face-path search is an input.
-/

section

open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.GridLiftedWalkConnections (alongLiftedWalk)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.DualWalks (DualWalk DualConnection)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.GridLiftedDualConnectivity

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
set_option genInjectivity false in
/-- An original lifted triangle located at a retained regular grid incident.

The original vertex, regular face, sheet and upper/lower triangle flag retain an exact equality to the requested
triangle index. -/
structure TriangleAnchor (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (index : Fin
  mesh.triangles.length) where
  /-- The original grid vertex anchoring the retained triangle incident. -/ point : Basic.Canonical
  /-- The anchor belongs to the original grid's vertex set. -/ onGrid :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex
    base.bank.grid point
  /-- The retained regular cell incident at that exact anchor. -/ regular : RegularIncident base point
  /-- The original sheet index of the retained lift. -/ sheet : Fin 2
  /-- The retained upper/lower triangle choice within the lifted quadrilateral. -/ upper : Bool
  /-- The original regular-incident lift on the retained sheet. -/ lifted : regular.Lifted mesh sheet
  /-- The selected lifted occurrence has exactly the requested original triangle index. -/ index_eq :
    lifted.value.located.occurrence.triangle upper = index

constructive_injectivity TriangleAnchor

open Purelib.Riemann.Meshes in
/-- Decode an original lifted triangle into its retained regular anchor and sheet.

The original bounded face position and lower-side anchor determine the incident and lift; the exact occurrence index is
transported without replacing the triangle owner. -/
@[expose] def triangleAnchor (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (index : Fin
  mesh.triangles.length) :
    TriangleAnchor mesh index := by
  let decoded := mesh.locateTriangle index
  let face := base.faces.regulars[decoded.position.val]
  let point := face.cell.box.anchor
  let onGrid := face.cell.anchor_mem face.member
  let regular := RegularIncident.ofPosition base decoded.position point onGrid
    ⟨le_rfl, face.cell.box.x_valid, le_rfl, face.cell.box.y_valid⟩
  let lifted := regular.lift mesh decoded.sheet
  refine ⟨point, onGrid, regular, decoded.sheet, decoded.upper, lifted, ?_⟩
  have cornerEq : regular.corner.side = GridSide.bottom :=
    GridSide.start_injective face.cell.box_proper regular.corner.start_eq
  have sheetEq : lifted.value.sheet = decoded.sheet := by
    exact (congrArg lifted.value.located.lifted.sideStartSheet cornerEq.symm).trans lifted.value.start_eq
  calc
    lifted.value.located.occurrence.triangle decoded.upper =
        (mesh.locateFace regular.located.index lifted.value.sheet).occurrence.triangle decoded.upper :=
          lifted.triangle_eq _
    _ = (mesh.locateFace decoded.position decoded.sheet).occurrence.triangle decoded.upper := by rw [sheetEq]; rfl
    _ = index := decoded.index_eq

end Purelib.Riemann.Meshes.GridLiftedDualConnectivity

namespace Purelib.Riemann.Meshes.FramedPuncturedGrid

open Purelib in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
open Purelib.RootIsolation in
/-- Connect every original lifted triangle to the retained root triangle by a dual walk.

The ambient anchor, original sheet-connecting walk and actual lifted incidents determine each path, whose endpoint is
transported along the target triangle's exact index equality. -/
@[expose] def dualConnection (base : FramedPuncturedGrid curve
  branches higher)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) : Topology.Mesh.DualWalks.DualConnection
      mesh.triangulation.faces :=
  let rootPoint := (Cuts.Ambient curve).anchor
  let rootOnGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid rootPoint :=
    ⟨base.bank.frame.xLower,
    base.bank.frame.yLower⟩
  let rootStar := VertexStar.build base rootPoint rootOnGrid
  let root := rootStar.regularIncident
  let rootLift := root.lift mesh 0
  ⟨rootLift.value.located.occurrence.triangle false, fun index =>
    let target := Purelib.Riemann.Meshes.GridLiftedDualConnectivity.triangleAnchor mesh index
    let walk := base.bank.toBranchCellBank.connectSheets edges rootPoint target.point rootOnGrid target.onGrid 0
      target.sheet
    let path := alongLiftedWalk mesh walk rootStar root rootLift target.regular target.lifted false target.upper
    Eq.mp (congrArg (Topology.Mesh.DualWalks.DualWalk mesh.triangulation.faces
      (rootLift.value.located.occurrence.triangle false)) target.index_eq) path⟩

end Purelib.Riemann.Meshes.FramedPuncturedGrid

end

end
