module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! Actual path assignments feed the common route-word chart request API.
The retained face, sheet and direction of every occurrence are preserved. -/

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : LiftedMesh vertices edges base.faces} {ambient : Rational.Box}

/-- Retain the actual original face, sheet and direction assignments as a route spine on the same indexed path. -/
def routeSpine : {start finish :
  Gaussian.Basic.Canonical} → {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} →
    (assigned : PathFaces mesh path) → Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh assigned.indexed
  | _, _, _, .nil _ => .nil
  | _, _, _, .cons first rest => .cons first.location rest.routeSpine

/-- Reading the retained route spine gives exactly the original assigned path values. -/
theorem routeSpine_values {α : Type} (value : (edge :
  OrientedEdge vertices.count) → Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge → α)
    {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish} (assigned : PathFaces mesh path) :
    assigned.routeSpine.values value = assigned.values value := by
  induction assigned with
  | nil => rfl
  | cons first rest ih => exact congrArg (List.cons (value _ first.location)) ih

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces
