module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
public import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Tactic.QuotientFreeOmega

open Purelib
open Purelib.Riemann

public section

/-!
# Transport-aware dual crossings between actual regular grid faces

A requested source sheet on a side selects one of the two already retained
lifts. For neighboring base sides with reversed endpoints, actual transport
determines the destination sheet and proves literal reversal of the lifted
indices. The resulting dual walk uses the mesh's cached triangle occurrences.
Beyond base-side adjacency, no extra sheet-matching, lifted-seam-validity or
path-search-success premise is supplied.
Global construction of a connected family of such crossings remains separate.
-/

section

open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

namespace Purelib.Riemann.Meshes.GridLiftedDualSteps

/-- One of the four oriented sides of the original rectangular grid cell. -/
inductive GridSide where
  /-- The bottom side, oriented from lower left to lower right. -/ | bottom /-- The right side, oriented from lower
    right to upper right. -/ | right /-- The top side, oriented from upper right to upper left. -/ | top /-- The left
    side, oriented from upper left to lower left. -/ | left
  deriving DecidableEq

end Purelib.Riemann.Meshes.GridLiftedDualSteps

section

namespace Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

open Purelib.Geometry.Rectangle.Partition in
/-- The original rectangle-edge kind corresponding to the selected grid side. -/
@[expose] def kind : GridSide → RectangularEdgeUniqueness.RectangleEdge.Kind
  | .bottom => .bottom
  | .right => .right
  | .top => .top
  | .left => .left

open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
/-- The original oriented start coordinate of the selected box side. -/
@[expose] def start (side : GridSide) (box : Box) : Basic.Canonical :=
  (RectangularEdgeUniqueness.RectangleEdge.coordinates box side.kind).1
/-- The original oriented finish coordinate of the selected box side. -/
@[expose] def finish (side : GridSide) (box : Box) : Basic.Canonical :=
  (RectangularEdgeUniqueness.RectangleEdge.coordinates box side.kind).2

end Purelib.Riemann.Meshes.GridLiftedDualSteps.GridSide

end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

open Purelib.Polynomial in
/-- The exact original grid edge corresponding to a regular face's selected side. -/
@[expose] def side (face : RegularFace bank) : (side :
  Meshes.GridLiftedDualSteps.GridSide) →
    Geometry.Grid.Walks.Edge bank.grid (side.start face.cell.box) (side.finish face.cell.box)
  | .bottom => face.cell.bottomSide face.member
  | .right => face.cell.rightSide face.member
  | .top => face.cell.topSide face.member
  | .left => face.cell.leftSide face.member

end Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

section

variable {face : RegularFace bank} {sheet : Fin 2}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- The retained transported sheet at the original selected side's start corner. -/
@[expose] def sideStartSheet (lifted :
  LiftedFace vertices edges face sheet) : Meshes.GridLiftedDualSteps.GridSide → Fin 2
  | .bottom => sheet
  | .right => lifted.lowerRight
  | .top => lifted.upperRight
  | .left => lifted.upperLeft

/-- The retained transported sheet at the original selected side's finish corner. -/
@[expose] def sideFinishSheet (lifted :
  LiftedFace vertices edges face sheet) : Meshes.GridLiftedDualSteps.GridSide → Fin 2
  | .bottom => lifted.lowerRight
  | .right => lifted.upperRight
  | .top => lifted.upperLeft
  | .left => sheet

/-- Original edge transport sends the retained side-start sheet to its exact side-finish sheet. -/
theorem side_transport (lifted : LiftedFace
  vertices edges face sheet) (side : Meshes.GridLiftedDualSteps.GridSide) :
    (edges.edge (face.side side)).forward.target (lifted.sideStartSheet side) = lifted.sideFinishSheet side := by
  cases side
  · exact lifted.bottom_eq.symm
  · exact lifted.right_eq.symm
  · exact lifted.top_eq.symm
  · exact lifted.closed

open Purelib in
/-- The retained quadrilateral side is exactly the original grid edge indexed at its transported start sheet. -/
theorem side_edge_eq (lifted : LiftedFace
  vertices edges face sheet) (side : Meshes.GridLiftedDualSteps.GridSide) :
    Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge lifted.quad side.kind = edges.indexedEdge vertices
      (face.side side) (lifted.sideStartSheet side) := by
  cases side with
  | bottom =>
      exact congrArg₂ OrientedEdge.mk lifted.first_eq
        (lifted.second_eq.trans (congrArg (vertices.index _ _) lifted.bottom_eq))
  | right =>
      exact congrArg₂ OrientedEdge.mk lifted.second_eq
        (lifted.third_eq.trans (congrArg (vertices.index _ _) lifted.right_eq))
  | top =>
      exact congrArg₂ OrientedEdge.mk lifted.third_eq
        (lifted.fourth_eq.trans (congrArg (vertices.index _ _) lifted.top_eq))
  | left =>
      exact congrArg₂ OrientedEdge.mk lifted.fourth_eq
        (lifted.first_eq.trans (congrArg (vertices.index _ _) lifted.closed.symm))

/-- The two original lifts of a regular face have distinct start sheets on every selected side. -/
theorem sideStartSheet_ne (zero : LiftedFace
  vertices edges face 0) (one : LiftedFace vertices edges face 1)
    (side : Meshes.GridLiftedDualSteps.GridSide) : zero.sideStartSheet side ≠ one.sideStartSheet side := by
  intro equal
  have different := zero.opposite_corners one
  cases side with
  | bottom => exact (by decide : (0 : Fin 2) ≠ 1) equal
  | right =>
      apply different.2.1
      rw [zero.second_eq, one.second_eq]
      exact congrArg (vertices.index _ _) equal
  | top =>
      apply different.2.2.1
      rw [zero.third_eq, one.third_eq]
      exact congrArg (vertices.index _ _) equal
  | left =>
      apply different.2.2.2
      rw [zero.fourth_eq, one.fourth_eq]
      exact congrArg (vertices.index _ _) equal

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

end

section

variable {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

set_option genInjectivity false in
/-- A located original face lift whose selected side starts on the requested retained sheet.

The original mesh, face position and side remain indices, and the stored equality identifies the exact side-start sheet.
-/
structure AtSide (mesh : LiftedMesh vertices edges faces)
  (position : Fin faces.regulars.length)
    (side : Meshes.GridLiftedDualSteps.GridSide) (requested : Fin 2) where
  /-- The original lift sheet selected for the requested side-start sheet. -/ sheet : Fin 2
  /-- The retained original face occurrence at the selected lift sheet. -/ located : mesh.LocatedFace position sheet
  /-- The retained selected side begins on exactly the requested sheet. -/ start_eq : located.lifted.sideStartSheet side
    = requested

constructive_injectivity AtSide

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (AtSide)

/-- Select the original face lift whose chosen side starts at the requested sheet.

The exact two retained lifts have distinct side-start sheets. A decidable comparison chooses the first or certifies the
second without changing either occurrence. -/
@[expose] def selectSide {position : Fin faces.regulars.length}
  (zero : mesh.LocatedFace position 0)
    (one : mesh.LocatedFace position 1) (side : Meshes.GridLiftedDualSteps.GridSide)
      (requested : Fin 2) : mesh.AtSide position side requested :=
  if equal : zero.lifted.sideStartSheet side = requested then ⟨0, zero, equal⟩
  else ⟨1, one, by
    have different := zero.lifted.sideStartSheet_ne one.lifted side
    have unequalValues : (zero.lifted.sideStartSheet side).val ≠ requested.val := fun same => equal (Fin.ext same)
    have differentValues : (zero.lifted.sideStartSheet side).val ≠ (one.lifted.sideStartSheet side).val :=
      fun same => different (Fin.ext same)
    have zeroBound := (zero.lifted.sideStartSheet side).isLt
    have oneBound := (one.lifted.sideStartSheet side).isLt
    have requestedBound := requested.isLt
    apply Fin.ext
    omega⟩

open Purelib.Riemann.Meshes in
/-- Locate the original face lift with the requested exact sheet at the selected side's start. -/
@[expose] def locateAtSide (mesh : LiftedMesh vertices edges
  faces) (position : Fin faces.regulars.length)
    (side : Meshes.GridLiftedDualSteps.GridSide) (requested : Fin 2) : mesh.AtSide position side requested :=
  selectSide (mesh.locateFace position 0) (mesh.locateFace position 1) side requested

open Purelib in
open Purelib.Curves.Hyperelliptic in
/-- Oppositely directed original geometric sides yield reversed lifted indexed edges with matching transported sheets.

The exact endpoint equations and retained root-edge coherence identify both original vertex indices and sheet
transports. -/
theorem opposite_sides {firstPosition nextPosition : Fin
  faces.regulars.length} {sheet : Fin 2}
    (first : mesh.LocatedFace firstPosition sheet) (firstSide nextSide : Meshes.GridLiftedDualSteps.GridSide)
    (next : mesh.AtSide nextPosition nextSide (first.lifted.sideFinishSheet firstSide))
    (startEq : nextSide.start faces.regulars[nextPosition.val].cell.box =
      firstSide.finish faces.regulars[firstPosition.val].cell.box)
    (finishEq : nextSide.finish faces.regulars[nextPosition.val].cell.box =
      firstSide.start faces.regulars[firstPosition.val].cell.box) :
    Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge next.located.lifted.quad nextSide.kind =
      (Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.edge first.lifted.quad firstSide.kind).reverse := by
  rw [next.located.lifted.side_edge_eq, first.lifted.side_edge_eq, next.start_eq, ← first.lifted.side_transport]
  exact edges.indexedEdge_opposite_of_endpoints vertices _ _ startEq finishEq
    (Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank _ (faces.regulars[firstPosition.val].side
      firstSide).vertices.1).toLoop
    (Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank _ (faces.regulars[firstPosition.val].side
      firstSide).vertices.2).toLoop _

open Purelib in
set_option genInjectivity false in
/-- A retained next-face location and dual walk across two original matching sides.

The next lift starts on the original first side's terminal sheet, while both triangle-half selectors remain exact
dual-walk endpoint indices. -/
structure Crossing {firstPosition : Fin faces.regulars.length}
  {sheet : Fin 2}
    (first : mesh.LocatedFace firstPosition sheet) (firstSide : Meshes.GridLiftedDualSteps.GridSide)
      (nextPosition : Fin faces.regulars.length)
    (nextSide : Meshes.GridLiftedDualSteps.GridSide) (firstUpper lastUpper : Bool) where
  /-- The retained next-face location beginning at the original side's terminal sheet. -/ next : mesh.AtSide
    nextPosition nextSide (first.lifted.sideFinishSheet firstSide)
  /-- The dual walk between the exact original selected triangle occurrences. -/ path : Topology.Mesh.DualWalks.DualWalk
    mesh.triangulation.faces (first.occurrence.triangle firstUpper)
    (next.located.occurrence.triangle lastUpper)

constructive_injectivity Crossing

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (Crossing)

open Purelib.Riemann.Meshes in
/-- Construct a dual crossing between original face sides with reversed geometric endpoints.

The next lift is selected at the exact transported terminal sheet, and its retained quadrilateral occurrence connects
the requested original triangle halves. -/
@[expose] def crossSide {firstPosition : Fin
  faces.regulars.length} {sheet : Fin 2}
    (first : mesh.LocatedFace firstPosition sheet) (firstSide : Meshes.GridLiftedDualSteps.GridSide)
      (nextPosition : Fin faces.regulars.length)
    (nextSide : Meshes.GridLiftedDualSteps.GridSide)
    (startEq : nextSide.start faces.regulars[nextPosition.val].cell.box =
      firstSide.finish faces.regulars[firstPosition.val].cell.box)
    (finishEq : nextSide.finish faces.regulars[nextPosition.val].cell.box =
      firstSide.start faces.regulars[firstPosition.val].cell.box) (firstUpper lastUpper : Bool) :
    Crossing first firstSide nextPosition nextSide firstUpper lastUpper :=
  let next := mesh.locateAtSide nextPosition nextSide (first.lifted.sideFinishSheet firstSide)
  ⟨next, first.occurrence.connectAcross next.located.occurrence firstSide.kind nextSide.kind
    (opposite_sides first firstSide nextSide next startEq finishEq) firstUpper lastUpper⟩

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

end
end

end
