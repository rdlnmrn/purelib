module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Riemann.Meshes.GridLiftedVertexConnections
public import Purelib.Topology.Mesh.CornerWalks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Riemann.Integration.PuncturedVertexConnections
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Actual vertex-preserving connections between retained lifted faces

Reuse the classified regular vertex star and its original selected root
lifts. Every crossed side or diagonal contains the same sheet-labelled
vertex. In particular the intermediate triangle is chosen at that corner;
an arbitrary lower triangle would not suffice at an upper-left corner.
-/

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Riemann.Meshes.GridLiftedCornerConnections

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Polynomial.Geometry.Grid.VertexCellSteps (IncidentCell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)
open Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident (Connection)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

namespace BranchCellBank.LiftedFace

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {face : RegularFace bank} {sheet : Fin 2}

open Purelib.Data in
/-- The second and fourth vertices of a retained lifted regular face are distinct. -/
theorem second_fourth_ne (lifted : LiftedFace vertices edges face sheet) : lifted.quad.second ≠ lifted.quad.fourth := by
  intro equal
  have coordinates := congrArg vertices.coordinate equal
  rw [lifted.coordinates.2.1, lifted.coordinates.2.2.2] at coordinates
  exact (ne_of_lt face.cell.box_proper.1) (congrArg (fun point : Gaussian.Basic.Canonical => point.re) coordinates).symm

end BranchCellBank.LiftedFace

namespace FramedPuncturedGrid.RegularIncident

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {point : Purelib.Data.Gaussian.Basic.Canonical} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    base.bank.grid} {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {first last : RegularIncident base point} {requested : Fin 2}

open Purelib.Data in
open Purelib.Polynomial in
/-- Equal grid coordinates give equal indexed vertices on the same retained sheet. -/
private theorem index_congr {first last : Gaussian.Basic.Canonical} (equal : first = last)
    (firstOn : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid first) (lastOn :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid last) (sheet : Fin 2) :
    vertices.index first firstOn sheet = vertices.index last lastOn sheet := by
  cases equal
  rfl

namespace Lifted

variable {regular : RegularIncident base point}

open Purelib.Topology in
/-- Select the triangle containing the regular incident's original corner. -/
def cornerUpper (_lifted : regular.Lifted mesh requested) : Bool := Mesh.QuadrilateralDual.QuadOccurrence.upperSide
  regular.corner.side.kind

section
open Purelib.Polynomial
/-- A side starting at the incident point has the exact retained sheet-labelled start vertex. -/
theorem start_vertex (lifted : regular.Lifted mesh requested) (onGrid :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex
  base.bank.grid point)
    (side : GridSide) (atPoint : side.start regular.incident.cell.box = point) :
    (lifted.value.located.lifted.quad.edge side.kind).start = vertices.index point onGrid requested := by
  rw [lifted.value.located.lifted.side_edge_eq]
  change vertices.index _ (base.faces.regulars[regular.located.index.val].side side).vertices.1
    (lifted.value.located.lifted.sideStartSheet side) = _
  rw [lifted.startSheet_at side atPoint]
  apply index_congr
  rw [regular.indexed_cell]
  exact atPoint

/-- A side ending at the incident point has the exact retained sheet-labelled finish vertex. -/
theorem finish_vertex (lifted : regular.Lifted mesh requested) (onGrid :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex
  base.bank.grid point)
    (side : GridSide) (atPoint : side.finish regular.incident.cell.box = point) :
    (lifted.value.located.lifted.quad.edge side.kind).finish = vertices.index point onGrid requested := by
  rw [lifted.value.located.lifted.side_edge_eq]
  change vertices.index _ (base.faces.regulars[regular.located.index.val].side side).vertices.2
    ((edges.edge (base.faces.regulars[regular.located.index.val].side side)).forward.target
      (lifted.value.located.lifted.sideStartSheet side)) = _
  rw [lifted.value.located.lifted.side_transport, lifted.finishSheet_at side atPoint]
  apply index_congr
  rw [regular.indexed_cell]
  exact atPoint

end

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Polynomial in
/-- The selected corner triangle contains the original indexed vertex on the requested sheet. -/
theorem corner_contains (lifted : regular.Lifted mesh requested) (onGrid :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex
  base.bank.grid point) :
    Mesh.CornerWalks.OrientedTriangle.ContainsVertex
      (mesh.triangulation.faces (lifted.value.located.occurrence.triangle (cornerUpper lifted)))
      (vertices.index point onGrid requested) :=
  Mesh.CornerWalks.QuadOccurrence.contains_of_edge
    lifted.value.located.occurrence regular.corner.side.kind
    (Or.inl (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.start_vertex
      lifted onGrid regular.corner.side regular.corner.start_eq).symm)

end Lifted

open Purelib.Topology in
open Purelib.Polynomial in
/-- A dual triangle path that preserves one specified original sheet-labelled vertex. -/
abbrev CornerRoute (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point)
    (firstLift : first.Lifted mesh requested) (lastLift : last.Lifted mesh requested) (firstUpper lastUpper : Bool) :=
  { path : Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) // Mesh.CornerWalks.DualWalk.AtVertex (vertices.index point
        onGrid requested) path }

section
open Purelib.Riemann
open Purelib.Topology
open Purelib.Polynomial
/-- Cross an incoming retained cell seam while preserving the specified lifted corner.

Both endpoint triangles contain the same indexed vertex, and the original side transports certify the crossing. -/
public def incomingCorner (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point)
    (firstLift : first.Lifted mesh requested) (lastLift : last.Lifted mesh requested)
    (seam : Geometry.Grid.VertexCellSteps.IncidentCell.Seam first.incident last.incident) (atPoint :
      seam.firstSide.finish first.incident.cell.box = point)
    (firstUpper lastUpper : Bool)
    (firstContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (firstLift.value.located.occurrence.triangle firstUpper))
      (vertices.index point onGrid requested))
    (lastContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (lastLift.value.located.occurrence.triangle lastUpper))
      (vertices.index point onGrid requested)) : CornerRoute onGrid firstLift lastLift firstUpper lastUpper :=
  let next : mesh.AtSide last.located.index seam.secondSide (firstLift.value.located.lifted.sideFinishSheet
    seam.firstSide) :=
    ⟨lastLift.value.sheet, lastLift.value.located,
      (lastLift.startSheet_at seam.secondSide (seam.start_eq.trans atPoint)).trans
        (firstLift.finishSheet_at seam.firstSide atPoint).symm⟩
  let opposite := Meshes.GridLiftedMesh.LiftedMesh.opposite_sides
    firstLift.value.located seam.firstSide seam.secondSide next
    (by simpa only [first.indexed_cell, last.indexed_cell] using seam.start_eq)
    (by simpa only [first.indexed_cell, last.indexed_cell] using seam.finish_eq)
  ⟨firstLift.value.located.occurrence.connectAcross lastLift.value.located.occurrence seam.firstSide.kind
    seam.secondSide.kind
      opposite firstUpper lastUpper,
    Mesh.CornerWalks.QuadOccurrence.connectAcross_at firstLift.value.located.occurrence
      lastLift.value.located.occurrence
      (Meshes.GridLiftedCornerConnections.BranchCellBank.LiftedFace.second_fourth_ne
        firstLift.value.located.lifted)
      (Meshes.GridLiftedCornerConnections.BranchCellBank.LiftedFace.second_fourth_ne
        lastLift.value.located.lifted)
      seam.firstSide.kind seam.secondSide.kind opposite firstUpper lastUpper firstContains lastContains
      (Or.inr (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.finish_vertex
        firstLift onGrid seam.firstSide atPoint).symm)⟩

/-- Interpret a retained regular-cell step as a corner-preserving dual path.

Same-cell and seam-crossing cases retain the selected endpoint triangles and the same original indexed vertex. -/
def cornerStep (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point)
    (firstLift : first.Lifted mesh requested) (lastLift : last.Lifted mesh requested)
    (step : Geometry.Grid.VertexCellSteps.IncidentCell.Step first.incident last.incident) (firstUpper lastUpper : Bool)
    (firstContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (firstLift.value.located.occurrence.triangle firstUpper))
      (vertices.index point onGrid requested))
    (lastContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (lastLift.value.located.occurrence.triangle lastUpper))
      (vertices.index point onGrid requested)) : CornerRoute onGrid firstLift lastLift firstUpper lastUpper :=
  match step with
  | .same equal => by
      have same := first.eq_of_cell last equal
      subst last
      rw [firstLift.value_eq] at firstContains
      rw [lastLift.value_eq] at lastContains
      unfold CornerRoute
      rw [firstLift.value_eq, lastLift.value_eq]
      let located := (mesh.locateAtSide first.located.index first.corner.side requested).located
      exact ⟨located.occurrence.connect firstUpper lastUpper,
        Mesh.CornerWalks.QuadOccurrence.connect_at located.occurrence
          (Meshes.GridLiftedCornerConnections.BranchCellBank.LiftedFace.second_fourth_ne located.lifted)
          firstUpper lastUpper firstContains lastContains⟩
  | .across seam =>
      if atPoint : seam.firstSide.finish first.incident.cell.box = point then
        incomingCorner onGrid firstLift lastLift seam atPoint firstUpper lastUpper firstContains lastContains
      else
        let route := incomingCorner onGrid lastLift firstLift seam.reverse
          (seam.finish_eq.trans (seam.at_vertex.resolve_right atPoint)) lastUpper firstUpper lastContains firstContains
        ⟨route.val.reverse, Mesh.CornerWalks.DualWalk.AtVertex.reverse route.property⟩

end

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Polynomial in
/-- Compose a classified two-step connection through the retained middle corner triangle.

Both paths preserve the same sheet-labelled vertex, including when the intermediate corner requires the upper triangle.
-/
def Connection.cornerRoute (connection : Connection first last) (onGrid :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex
  base.bank.grid point)
    (firstLift : first.Lifted mesh requested) (middleLift : connection.middle.Lifted mesh requested)
    (lastLift : last.Lifted mesh requested) (firstUpper lastUpper : Bool)
    (firstContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (firstLift.value.located.occurrence.triangle firstUpper))
      (vertices.index point onGrid requested))
    (lastContains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex (mesh.triangulation.faces
      (lastLift.value.located.occurrence.triangle lastUpper))
      (vertices.index point onGrid requested)) : CornerRoute onGrid firstLift lastLift firstUpper lastUpper :=
  let left := cornerStep onGrid firstLift middleLift connection.firstStep firstUpper
    (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.cornerUpper middleLift)
    firstContains (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.corner_contains
      middleLift onGrid)
  let right := cornerStep onGrid middleLift lastLift connection.lastStep
    (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.cornerUpper middleLift) lastUpper
    (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.corner_contains middleLift onGrid)
      lastContains
  ⟨left.val.append right.val, Mesh.CornerWalks.DualWalk.AtVertex.append left.property right.property⟩

open Purelib.Riemann in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A classified regular connection with three retained root lifts and its corner-preserving path.

The route joins the original selected corner triangles through their common indexed vertex. -/
structure CornerConnection (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex base.bank.grid point)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first last : RegularIncident base point) (requested : Fin 2) where
  /-- The retained original classified connection between the incident cells. -/ connection : Connection first last
  /-- The retained first incident lift at the requested sheet. -/ firstLift : first.Lifted mesh requested
  /-- The retained lift of the classified intermediate incident. -/ middleLift : connection.middle.Lifted mesh requested
  /-- The retained last incident lift at the requested sheet. -/ lastLift : last.Lifted mesh requested
  /-- The actual dual path preserving the original sheet-labelled corner. -/ route : CornerRoute onGrid firstLift
    lastLift
    (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.cornerUpper firstLift)
    (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.cornerUpper lastLift)

constructive_injectivity CornerConnection

open Purelib.Riemann in
/-- Build and retain the lifted corner connection from the existing classified vertex star.

Select each of its three incident lifts once, then connect the actual corner triangles while preserving their common
indexed vertex. -/
def connectCorners (star : VertexStar base point) (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first last : RegularIncident base point) (requested : Fin 2) :
    CornerConnection star.geometry.onGrid mesh first last requested :=
  let connection := Integration.PuncturedVertexConnections.RegularIncident.connect star first last
  let firstLift := first.lift mesh requested
  let middleLift := connection.middle.lift mesh requested
  let lastLift := last.lift mesh requested
  ⟨connection, firstLift, middleLift, lastLift,
    Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Connection.cornerRoute
      connection star.geometry.onGrid firstLift middleLift lastLift _ _
      (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.corner_contains
        firstLift star.geometry.onGrid)
      (Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Lifted.corner_contains
        lastLift star.geometry.onGrid)⟩

end FramedPuncturedGrid.RegularIncident
end Purelib.Riemann.Meshes.GridLiftedCornerConnections
