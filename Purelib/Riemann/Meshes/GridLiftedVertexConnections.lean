module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices

open Purelib

public section

/-!
# Automatic dual connections within an actual lifted vertex star

Choose the requested sheet at the common vertex in each retained regular
face. Interpret each constructed base-side step using the shared root-edge
transport; outgoing steps reverse an incoming_public dual walk. The intermediate
regular face avoids any incident branch hole, so local connectivity is total
and does not depend on a successful graph search or a sheet-matching premise.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)
open Purelib.Polynomial.Geometry.Grid.VertexCellSteps (IncidentCell)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)
open Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident (Connection connect)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {point : Purelib.Data.Gaussian.Basic.Canonical} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    base.bank.grid} {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {first last : RegularIncident base point} {requested : Fin 2}

namespace Purelib.Riemann.Meshes.GridLiftedVertexConnections

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Polynomial in
/-- Construct a dual walk across an incident seam ending at the common vertex.

The two retained lifts use the same requested sheet there; their transport equations identify the actual opposite sides
and selected endpoint triangles. -/
@[expose] public def incoming (firstLift : first.Lifted mesh requested) (lastLift : last.Lifted mesh requested)
    (seam : Geometry.Grid.VertexCellSteps.IncidentCell.Seam first.incident last.incident)
    (atPoint : seam.firstSide.finish first.incident.cell.box = point) (firstUpper lastUpper : Bool) :
    Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) :=
  let next : mesh.AtSide last.located.index seam.secondSide
      (firstLift.value.located.lifted.sideFinishSheet seam.firstSide) :=
    ⟨lastLift.value.sheet, lastLift.value.located,
      (lastLift.startSheet_at seam.secondSide (seam.start_eq.trans atPoint)).trans
        (firstLift.finishSheet_at seam.firstSide atPoint).symm⟩
  let opposite := Meshes.GridLiftedMesh.LiftedMesh.opposite_sides firstLift.value.located seam.firstSide seam.secondSide
    next
    (by simpa only [first.indexed_cell, last.indexed_cell] using seam.start_eq)
    (by simpa only [first.indexed_cell, last.indexed_cell] using seam.finish_eq)
  firstLift.value.located.occurrence.connectAcross lastLift.value.located.occurrence seam.firstSide.kind
    seam.secondSide.kind
    opposite firstUpper lastUpper

open Purelib.Topology in
open Purelib.Polynomial in
/-- Lift one local incident-cell step to a dual walk between the retained triangles.

Coincident cells reuse their canonical lookup equations. Crossing cells use the incoming seam walk or its reversal
according to the common vertex. -/
@[expose] def dualStep (firstLift : first.Lifted mesh requested) (lastLift : last.Lifted mesh requested)
    (step : Geometry.Grid.VertexCellSteps.IncidentCell.Step first.incident last.incident) (firstUpper lastUpper : Bool)
      :
    Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) :=
  match step with
  | .same equal => by
      have same := first.eq_of_cell last equal
      subst last
      rw [firstLift.value_eq, lastLift.value_eq]
      exact (mesh.locateAtSide first.located.index first.corner.side requested).located.occurrence.connect firstUpper
        lastUpper
  | .across seam =>
      if atPoint : seam.firstSide.finish first.incident.cell.box = point then
        incoming firstLift lastLift seam atPoint firstUpper lastUpper
      else
        (incoming lastLift firstLift seam.reverse
          (seam.finish_eq.trans (seam.at_vertex.resolve_right atPoint)) lastUpper firstUpper).reverse

end Purelib.Riemann.Meshes.GridLiftedVertexConnections

namespace Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Connection

open Purelib.Topology in
/-- Compose the two local dual steps through the retained intermediate lift.

The common intermediate triangle is the lower triangle of that exact lift; both endpoint triangle choices are preserved.
-/
@[expose] def dualPath
  (connection : Connection first last)
    (firstLift : first.Lifted mesh requested) (middleLift : connection.middle.Lifted mesh requested)
    (lastLift : last.Lifted mesh requested) (firstUpper lastUpper : Bool) :
    Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) :=
  (Meshes.GridLiftedVertexConnections.dualStep firstLift middleLift connection.firstStep firstUpper false).append
    (Meshes.GridLiftedVertexConnections.dualStep middleLift lastLift connection.lastStep false lastUpper)

end Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Connection

namespace Purelib.Riemann.Meshes.GridLiftedVertexConnections

open Purelib.Riemann in
open Purelib.Topology in
set_option genInjectivity false in
/-- A retained local cell connection with three compatible lifts and its actual dual path.

The first, intermediate and last lifts all select the same sheet at the common vertex, while the path connects the
requested endpoint triangles. -/
structure LiftedConnection (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first last : RegularIncident base point) (requested : Fin 2) (firstUpper lastUpper : Bool) where
  /-- The retained base connection through a regular intermediate cell. -/ connection : Connection first last
  /-- The selected lift of the first incident cell. -/ firstLift : first.Lifted mesh requested
  /-- The selected lift of the connection's exact intermediate cell. -/ middleLift : connection.middle.Lifted mesh
    requested
  /-- The selected lift of the last incident cell. -/ lastLift : last.Lifted mesh requested
  /-- The actual dual walk connecting the requested endpoint triangles. -/ path : Mesh.DualWalks.DualWalk
    mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
    (lastLift.value.located.occurrence.triangle lastUpper)

constructive_injectivity LiftedConnection

open Purelib.Riemann in
/-- Construct and retain a local connection and its three sheet-compatible lifts once.

The cached vertex star selects a regular intermediate cell; the supplied mesh supplies the exact lifts used to build the
dual path. -/
@[expose] def connectLifted (star : VertexStar base point) (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
  base.faces)
    (first last : RegularIncident base point) (requested : Fin 2) (firstUpper lastUpper : Bool) :
    LiftedConnection mesh first last requested firstUpper lastUpper :=
  let connection := connect star first last
  let firstLift := first.lift mesh requested
  let middleLift := connection.middle.lift mesh requested
  let lastLift := last.lift mesh requested
  ⟨connection, firstLift, middleLift, lastLift, connection.dualPath firstLift middleLift lastLift firstUpper lastUpper⟩

end Purelib.Riemann.Meshes.GridLiftedVertexConnections

end
