module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
public import Purelib.Topology.Surface.Cut.JumpBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Riemann

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest

open Purelib.Topology.Surface.Cut.JumpBank

@[expose] public section

/-!
# Actual closed mesh paths for all retained cut jumps

The paths come from the canonical sewn boundary, keep its traversal order,
and use only original lifted triangle edges (in either orientation). Their
endpoints agree as lifted vertex indices, not merely as base coordinates.
Identifying an integral symplectic basis among these actual cycles remains
separate; nominal branch-cut A/B labels are not geometric evidence for it.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Topology.Surface.Cut.JumpBank (CutJumpBank CutJumpEntry)
open Purelib.Topology.Surface.Cut.JumpPaths

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The complete jump-cycle bank is constructed without new owner preparation, path-search success, or supplied
cycle-identification data. -/
def cutJumpPaths (lifted : Meshes.LiftedPuncturedGrid base) :
    JumpBank.CutJumpBank lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary
      lifted.cutBoundaryPairs.pairs :=
  ProjectedEdgePairing.jumpPaths lifted.cutBoundaryPairs
    lifted.cutPolygon.patch.cut.closed

/-- The retained cut-jump bank has exactly one entry per original paired cut-edge occurrence. -/
theorem cutJumpPaths_length (lifted : Meshes.LiftedPuncturedGrid base)
  :
    lifted.cutJumpPaths.entries.length = lifted.cutBoundaryPairs.pairs.length :=
  CutJumpBank.length_eq lifted.cutJumpPaths

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.JumpPaths

/-- The retained jump path at the pair's starting endpoint uses original surface triangle edges in either orientation.
-/
theorem cutJump_start_supported (lifted : Meshes.LiftedPuncturedGrid base)
    (entry : JumpBank.CutJumpEntry lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) entry.paths.start.surfaceEdges :=
  CutPath.supported_mono entry.paths.start_supported (by
    intro edge member
    exact SinglePolygon.boundary_member lifted.cutPolygon (by
      simpa only [lifted.cutPolygon.patch.cut.boundary_eq] using member))

/-- The retained jump path at the pair's finishing endpoint uses original surface triangle edges in either orientation.
-/
theorem cutJump_finish_supported (lifted : Meshes.LiftedPuncturedGrid base)
    (entry : JumpBank.CutJumpEntry lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary) :
    CutPath.Supported (Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) entry.paths.finish.surfaceEdges
      :=
  CutPath.supported_mono entry.paths.finish_supported (by
    intro edge member
    exact SinglePolygon.boundary_member lifted.cutPolygon (by
      simpa only [lifted.cutPolygon.patch.cut.boundary_eq] using member))

/-- The first retained jump path starts and finishes at the exact same original lifted vertex index. -/
theorem cutJump_start_closed (lifted : Meshes.LiftedPuncturedGrid base)
    (entry : JumpBank.CutJumpEntry lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish entry.paths.start.surfaceEdges
      (lifted.cutPolygon.patch.cut.vertexLabels entry.pair.first.start)
      (lifted.cutPolygon.patch.cut.vertexLabels entry.pair.first.start) := entry.paths.start_closed

/-- The second retained jump path starts and finishes at the exact same original lifted vertex index. -/
theorem cutJump_finish_closed (lifted : Meshes.LiftedPuncturedGrid base)
    (entry : JumpBank.CutJumpEntry lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.boundary) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish entry.paths.finish.surfaceEdges
      (lifted.cutPolygon.patch.cut.vertexLabels entry.pair.first.finish)
      (lifted.cutPolygon.patch.cut.vertexLabels entry.pair.first.finish) := entry.paths.finish_closed

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.JumpPaths

end
