module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.DualWalks
public import Purelib.Riemann.Meshes.GridLiftedEdgeConnections
public import Purelib.Riemann.Meshes.GridLiftedConnections
public import Purelib.Riemann.Meshes.GridLiftedVertexConnections

@[expose] public section

/-!
# Dual-face traversal along the actual transported grid skeleton

Each grid edge selects a regular incident face. Local vertex-star dual walks
join the incoming face to that edge face, and exact corner transport moves
to its other endpoint. Structural recursion follows the original finite walk,
including reversed edges and winding-one sheet exchanges. No graph-search
success or global dual-connectivity certificate is assumed.
-/

namespace Purelib.Riemann.Meshes.GridLiftedWalkConnections

open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

open Purelib.Data in
open Purelib.Polynomial.Geometry.Grid in
open Purelib.Riemann in
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank in
open Purelib.Topology in
/-- Construct a dual-face path along the actual transported finite grid walk.

Each edge uses its retained regular incident face and local vertex-star connections. Structural recursion preserves the
original endpoint sheets, face choices and triangle halves. -/
def alongWalk (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    {start finish : Gaussian.Basic.Canonical} → (walk : Walks.Walk base.bank.grid start finish) → (sheet : Fin 2) →
      (star : VertexStar base start) → (first : RegularIncident base start) → (firstLift : first.Lifted mesh sheet) →
      (last : RegularIncident base finish) → (lastLift : last.Lifted mesh (RootEdgeBank.target edges walk sheet)) →
      (firstUpper lastUpper : Bool) → Mesh.DualWalks.DualWalk mesh.triangulation.faces
        (firstLift.value.located.occurrence.triangle firstUpper) (lastLift.value.located.occurrence.triangle lastUpper)
  | _, _, .nil _, sheet, star, first, firstLift, last, lastLift, firstUpper, lastUpper =>
      let connection := RegularIncident.connect star first last
      connection.dualPath firstLift (connection.middle.lift mesh sheet) lastLift firstUpper lastUpper
  | _, _, .cons edge tail, sheet, star, first, firstLift, last, lastLift, firstUpper, lastUpper =>
      let crossing := RegularEdgeCell.connectLifted star mesh edge sheet false false
      let connection := RegularIncident.connect star first crossing.cell.first
      let initialPath := connection.dualPath firstLift (connection.middle.lift mesh sheet) crossing.firstLift firstUpper
        false
      let nextStar := VertexStar.build base _ edge.vertices.2
      let suffix := alongWalk mesh tail ((edges.edge edge).forward.target sheet) nextStar crossing.cell.last
        crossing.lastLift
        last lastLift false lastUpper
      initialPath.append (crossing.path.append suffix)

open Purelib.Data in
open Purelib.Riemann in
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank in
open Purelib.Topology in
/-- Construct the dual-face path of a retained lifted skeleton walk.

The stored endpoint-sheet equation identifies the exact transported target, preserving both supplied endpoint faces and
their selected triangle halves. -/
def alongLiftedWalk (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    {start finish : Gaussian.Basic.Canonical} {firstSheet lastSheet : Fin 2}
    (walk : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish lastSheet)
    (star : VertexStar base start) (first : RegularIncident base start) (firstLift : first.Lifted mesh firstSheet)
    (last : RegularIncident base finish) (lastLift : last.Lifted mesh lastSheet) (firstUpper lastUpper : Bool) :
    Mesh.DualWalks.DualWalk mesh.triangulation.faces (firstLift.value.located.occurrence.triangle firstUpper)
      (lastLift.value.located.occurrence.triangle lastUpper) := by
  rcases walk with ⟨walk, firstMember, lastMember, reached⟩
  subst lastSheet
  exact alongWalk mesh walk firstSheet star first firstLift last lastLift firstUpper lastUpper

end Purelib.Riemann.Meshes.GridLiftedWalkConnections
