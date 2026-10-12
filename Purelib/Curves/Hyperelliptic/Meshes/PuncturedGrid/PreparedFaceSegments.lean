module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
public import Purelib.Riemann.Paths.PreparedPathDecomposition
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.PreparedPathTrace

open Purelib

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Topology

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Face assignments indexed by the actual retained segment decomposition

Zipping geometry onto a preparation preserves the original cached segments
and owner handoffs literally. No root transport or re-preparation is needed.
The output retains one lifted-face occurrence for every original segment.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace PathFaces)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank}

set_option genInjectivity false in
/-- Face placements indexed by the actual retained preparation segments.

Each original segment keeps its cached preparation and owner handoff, together with its original lifted-face occurrence.
-/
inductive AssignedSegments (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) {ambient :
  Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} → {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      →
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} → {prepared :
        PreparedClearPathModels.PreparedPath path owner} →
        PreparedPath.CoveredSegments prepared → Type
  /-- The empty original preparation retains no face placements. -/ | nil (point : Data.Gaussian.Basic.Canonical) (owner
    : SquareRootContinuationChain.Owner (curve.polynomial.eval point)) :
    AssignedSegments mesh (.nil point owner)
  /-- Retain the original prepared head segment's face placement and the exact prepared tail. -/ | cons {start middle
    finish : Data.Gaussian.Basic.Canonical} {head : ClearPath.ClearSegment curve.polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath curve.polynomial ambient middle finish} {owner :
        SquareRootContinuationChain.Owner
        (curve.polynomial.eval start)}
      {first : PreparedPathDecomposition.CoveredSegment head owner} {rest : PreparedClearPathModels.PreparedPath tail
        first.traced.finishOwner}
      {remaining : PreparedPath.CoveredSegments rest}
      (placement : LiftedMesh.SegmentFace mesh head) (assigned :
        AssignedSegments mesh remaining) :
      AssignedSegments mesh (.cons first
        remaining)

constructive_injectivity AssignedSegments

namespace AssignedSegments

variable {mesh : LiftedMesh vertices edges faces} {ambient :
  Purelib.Geometry.Rational.Box}

/-- Attach the original path's face placements to its retained preparation decomposition without rebuilding segments or
roots. -/
def build : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  ambient start
  finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} (pieces : PreparedPath.CoveredSegments prepared),
      LiftedMesh.PathFaces mesh path → Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments
        mesh pieces
  | _, _, _, _, _, .nil point owner, .nil _ => .nil point owner
  | _, _, _, _, _, .cons _ rest, geometry => by
      cases geometry with
      | cons first tail =>
        exact .cons first (build
          rest tail)

/-- Read the retained oriented vertex-bank edges in the original preparation order. -/
def indexed : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  ambient
  start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared},
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces → List
        (Stokes.OrientedEdge vertices.count)
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons first tail => first.indexed :: tail.indexed

/-- Attaching face placements preserves exactly the original path assignment's indexed edges. -/
theorem build_indexed : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial
  ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} (pieces : PreparedPath.CoveredSegments prepared)
    (geometry : LiftedMesh.PathFaces mesh path),
      (build pieces geometry).indexed =
      geometry.indexed
  | _, _, _, _, _, .nil _ _, .nil _ => rfl
  | _, _, _, _, _, .cons _ rest, geometry => by
      cases geometry with
      | cons first tail =>
        exact congrArg (List.cons first.indexed)
          (build_indexed rest
          tail)

/-- There is one retained indexed edge for each actual preparation segment. -/
theorem indexed_length : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial
  ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces),
      assigned.indexed.length = pieces.count
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons _ tail => by
      change tail.indexed.length + 1 = 1 + _
      rw [tail.indexed_length, Nat.add_comm]

end AssignedSegments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
