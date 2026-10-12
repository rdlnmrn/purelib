module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
public import Purelib.Riemann.Meshes.PuncturedEdgeFaces
public import Purelib.Riemann.Meshes.GridLiftedCornerCoherence
import Purelib.Riemann.Meshes.GridLiftedVertexConnections
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Moving along actual grid edges inside selected regular lifted faces

The source corner sheet is transported by the original cached grid edge.
Endpoint coherence and the reverse-transport inverse law prove that the
destination corner selects the same actual lifted face. Its two triangle
occurrences therefore give a dual walk between either requested halves.
Regular incident faces, side orientation and sheet agreement are constructed,
not supplied as successful checks by the caller.
-/

namespace Purelib.Riemann.Meshes.PuncturedEdgeFaces.RegularEdgeCell

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)
open Purelib.Riemann.Meshes.PuncturedEdgeFaces.RegularEdgeCell (acquire)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {requested : Fin 2}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Polynomial in
/-- Transport the first selected face lift to the actual last corner sheet.

Endpoint coherence for the retained grid edge proves the statement in either cell orientation, using the original root
frames and cached forward target. -/
theorem target_at_lastCorner (cell : RegularEdgeCell
  base start finish) (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish)
    (firstLift : cell.first.Lifted mesh requested) :
    firstLift.value.located.lifted.sideStartSheet cell.last.corner.side = (edges.edge edge).forward.target requested :=
      by
  let side := base.faces.regulars[cell.located.index.val].side cell.geometry.side
  have cellEq : base.faces.regulars[cell.located.index.val].cell = cell.geometry.cell :=
    (congrArg Meshes.PuncturedGridFaces.RegularFace.cell cell.located.indexed).trans cell.located.cell_eq
  cases reversedEq : cell.geometry.reversed with
  | false =>
      have startEq : cell.geometry.side.start cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [reversedEq] at retained
        exact retained
      have finishEq : cell.geometry.side.finish cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [reversedEq] at retained
        exact retained
      have cornerEq : cell.last.corner.side = cell.geometry.side.next :=
        GridSide.start_injective cell.geometry.cell.box_proper
          (cell.last.corner.start_eq.trans (finishEq.symm.trans (cell.geometry.side.start_next
            cell.geometry.cell.box).symm))
      rw [cornerEq, firstLift.value.located.lifted.startSheet_next]
      have transported := firstLift.value.located.lifted.side_transport cell.geometry.side
      rw [firstLift.startSheet_at cell.geometry.side startEq] at transported
      have coherent := edges.target_eq_of_endpoints edge side
        (by
            change cell.geometry.side.start base.faces.regulars[cell.located.index.val].cell.box = start
            rw [cellEq];
            exact startEq)
        (by
            change cell.geometry.side.finish base.faces.regulars[cell.located.index.val].cell.box = finish
            rw [cellEq];
            exact finishEq)
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank start
          edge.vertices.1).toLoop
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank finish
          edge.vertices.2).toLoop requested
      exact transported.symm.trans coherent
  | true =>
      have startEq : cell.geometry.side.finish cell.geometry.cell.box = start := by
        have retained := cell.geometry.start_eq
        rw [reversedEq] at retained
        exact retained
      have finishEq : cell.geometry.side.start cell.geometry.cell.box = finish := by
        have retained := cell.geometry.finish_eq
        rw [reversedEq] at retained
        exact retained
      have cornerEq : cell.last.corner.side = cell.geometry.side :=
        GridSide.start_injective cell.geometry.cell.box_proper (cell.last.corner.start_eq.trans finishEq.symm)
      rw [cornerEq]
      have inverse := edges.target_opposite_of_endpoints side edge
        (by
            change start = cell.geometry.side.finish base.faces.regulars[cell.located.index.val].cell.box
            rw [cellEq];
            exact startEq.symm)
        (by
            change finish = cell.geometry.side.start base.faces.regulars[cell.located.index.val].cell.box
            rw [cellEq];
            exact finishEq.symm)
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
          side.vertices.1).toLoop
        (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
          side.vertices.2).toLoop
        (firstLift.value.located.lifted.sideStartSheet cell.geometry.side)
      have transported : (edges.edge side).forward.target (firstLift.value.located.lifted.sideStartSheet
        cell.geometry.side) =
          firstLift.value.located.lifted.sideFinishSheet cell.geometry.side :=
            firstLift.value.located.lifted.side_transport _
      rw [transported, firstLift.finishSheet_at cell.geometry.side startEq] at inverse
      exact inverse.symm

open Purelib.Polynomial in
/-- The endpoint corner lifts selected by the cached edge transport have the same face sheet.

Equality of their last-corner start sheets determines equality of the two retained face lifts' sheet labels. -/
theorem same_faceSheet (cell : RegularEdgeCell base
  start finish) (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish)
    (firstLift : cell.first.Lifted mesh requested)
    (lastLift : cell.last.Lifted mesh ((edges.edge edge).forward.target requested)) :
    firstLift.value.sheet = lastLift.value.sheet :=
  firstLift.value.located.lifted.sheet_eq_of_startSheet_eq lastLift.value.located.lifted cell.last.corner.side
    ((cell.target_at_lastCorner edge firstLift).trans lastLift.value.start_eq.symm)

open Purelib.Topology in
open Purelib.Polynomial in
/-- Connect either requested triangle halves inside the same retained lifted quadrilateral.

The edge target identifies the endpoint face sheets, so their original triangle occurrences are joined by the
quadrilateral's dual walk. -/
def dualPath (cell : RegularEdgeCell base start finish)
  (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish)
    (firstLift : cell.first.Lifted mesh requested)
    (lastLift : cell.last.Lifted mesh ((edges.edge edge).forward.target requested)) (firstUpper lastUpper : Bool) :
    Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) := by
  rw [firstLift.triangle_eq, lastLift.triangle_eq, ← cell.same_faceSheet edge firstLift lastLift]
  exact (mesh.locateFace cell.located.index firstLift.value.sheet).occurrence.connect firstUpper lastUpper

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained regular cell and lifted dual connection along an actual grid edge.

The source lift uses the requested sheet; the destination lift uses the cached forward target. The stored walk joins the
specified triangle halves of those exact lifts. -/
structure LiftedConnection (mesh :
  Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish) (requested : Fin 2) (firstUpper lastUpper : Bool)
      where
  /-- The retained regular cell incident to the original oriented edge. -/ cell : RegularEdgeCell base start finish
  /-- The actual first-corner lift with the requested source sheet. -/ firstLift : cell.first.Lifted mesh requested
  /-- The actual last-corner lift with the cached edge target sheet. -/ lastLift : cell.last.Lifted mesh ((edges.edge
    edge).forward.target requested)
  /-- The dual walk between the requested halves of the retained endpoint lifts. -/ path : Mesh.DualWalks.DualWalk
    mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
    (lastLift.value.located.occurrence.triangle lastUpper)

constructive_injectivity Purelib.Riemann.Meshes.PuncturedEdgeFaces.RegularEdgeCell.LiftedConnection

open Purelib.Riemann.Meshes.PuncturedEdgeFaces.RegularEdgeCell (LiftedConnection)

open Purelib.Riemann in
open Purelib.Polynomial in
/-- Construct the lifted dual connection from a source vertex star and actual grid edge.

Acquire the incident regular cell, select both endpoint lifts using the cached transport, and retain the walk after
proving their face-sheet agreement. -/
def connectLifted (star : VertexStar base start) (mesh
  : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish) (requested : Fin 2) (firstUpper lastUpper : Bool) :
    LiftedConnection mesh edge requested firstUpper lastUpper :=
  let cell := acquire star edge
  let firstLift := cell.first.lift mesh requested
  let lastLift := cell.last.lift mesh ((edges.edge edge).forward.target requested)
  ⟨cell, firstLift, lastLift, cell.dualPath edge firstLift lastLift firstUpper lastUpper⟩

end Purelib.Riemann.Meshes.PuncturedEdgeFaces.RegularEdgeCell
