module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Topology.Surface.Sewing.SewingTree

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBoundary
public import Purelib.Riemann.Meshes.GridLiftedEdgeUniqueness
import Purelib.Topology.Mesh.Replay.DualReplay
public import Purelib.Riemann.Meshes.GridLiftedDualConnectivity
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Joining
import Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Sewing.SewingForest
open _root_.Purelib.Topology.Surface.Sewing renaming SewingForest -> SewingForest

open Purelib.Topology.Surface.Sewing.SewingTree
open _root_.Purelib.Topology.Surface.Sewing renaming SewingTree -> SewingTree

@[expose] public section

/-!
# Ordered tree-sewing forests on the actual lifted mesh

All original lifted triangles occur exactly once in the constructed forest.
Every patch has a closed, cyclically ordered boundary and retained sewing
history, and no two distinct patches have an available seam.  Unglued reverse
occurrences inside a patch remain cuts.  Each patch also carries an indexed
cut triangulation with endpoint-only gluing and independent cut-vertex
primitive values. Unique oriented incidence is proved from the actual grid
geometry and root-sheet injectivity. Actual sheet-connected grid walks now
construct global dual connectivity, so every checked maximal forest is one
polygon with no caller-supplied connectivity premise. Reducing its boundary
to the standard symplectic A/B word remains a separate obligation.
-/

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Construct the ordered maximal sewing forest of the original lifted mesh triangles. -/
def cutForest (lifted : LiftedPuncturedGrid base) :
  Topology.Surface.Sewing.SewingForest lifted.mesh.triangulation.faces :=
  SewingForest.build lifted.mesh.triangulation.faces

/-- Any checked maximal forest on this actual mesh is one polygon. Both unique incidence and global dual connectivity
are constructed. -/
def singlePolygon (lifted : LiftedPuncturedGrid base) (forest :
  Topology.Surface.Sewing.SewingForest lifted.mesh.triangulation.faces) :
    SewingForest.SinglePolygon forest := lifted.mesh.singlePolygon forest (base.dualConnection lifted.mesh)

/-- The canonical forest is one polygon, without a supplied connectivity certificate or a successful one-patch search.
-/
def cutPolygon (lifted : LiftedPuncturedGrid base) :
  SewingForest.SinglePolygon lifted.cutForest :=
  lifted.singlePolygon lifted.cutForest

/-- The retained sewing-forest boundary area equals the exact original lifted mesh boundary area. -/
theorem cutForest_boundary (lifted : LiftedPuncturedGrid base)
    (forest : Topology.Surface.Sewing.SewingForest lifted.mesh.triangulation.faces) (primitive : Fin
      lifted.vertices.count →
      PrimitivePoint) :
    edgeListArea primitive (forest.patches.flatMap SewnPatch.boundary) = edgeListArea primitive
      lifted.mesh.triangulation.boundary :=
  (forest.boundary_area primitive).trans (lifted.mesh.wedge_eq_boundary primitive)

/-- The retained sewing-forest boundary area equals the actual original based boundary walk area. -/
theorem cutForest_basedBoundary (lifted : LiftedPuncturedGrid base)
    (forest : Topology.Surface.Sewing.SewingForest lifted.mesh.triangulation.faces) (primitive : Fin
      lifted.vertices.count →
      PrimitivePoint) :
    edgeListArea primitive (forest.patches.flatMap SewnPatch.boundary) = lifted.basedBoundary.area lifted.vertices
      primitive :=
  (lifted.cutForest_boundary forest primitive).trans (lifted.boundary_eq_basedBoundary primitive)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid
