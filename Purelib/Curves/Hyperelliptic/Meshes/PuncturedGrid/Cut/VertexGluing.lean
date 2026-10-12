module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Riemann.Meshes.GridLiftedTriangleStars
public import Purelib.Topology.Surface.Cut.VertexGluing
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank

open Purelib.Riemann

open Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.VertexGluing

open Purelib.Topology.Surface.Cut.VertexGluing.SewingForest

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Word

@[expose] public section

/-!
# Automatic exact vertex gluing for the actual root-backed cut surface

The lifted grid supplies every geometric premise: unique oriented edges,
nondegeneracy, and routes within each root-labelled vertex star. Its recorded
cut pairs therefore generate precisely the equalities of active surface
vertices, with no extra identifications or caller connectivity certificate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexGluing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedTriangleStars.FramedPuncturedGrid (vertexConnection)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.VertexGluing (PairVertexJoin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Reuse any retained checked polygon and pairing on the original mesh. -/
theorem vertexJoin_iff (lifted : Meshes.LiftedPuncturedGrid base)
    {forest : Topology.Surface.Sewing.SewingForest lifted.mesh.triangulation.faces}
    (polygon : SewingForest.SinglePolygon forest)
    (pairing : ProjectedEdgePairs.ProjectedEdgePairing polygon.patch.cut.vertexLabels polygon.patch.cut.boundary)
    {first last : Fin polygon.patch.cut.count}
    (firstActive : CutPatch.ActiveVertex polygon.patch.cut first)
    (lastActive : CutPatch.ActiveVertex polygon.patch.cut last) :
    VertexGluing.PairVertexJoin pairing.pairs first last ↔ polygon.patch.cut.vertexLabels first =
      polygon.patch.cut.vertexLabels last :=
    SinglePolygon.vertexJoin_iff polygon
      lifted.mesh.orientedEdges_unique
      (LiftedMesh.orientedEdges_nonloop lifted.mesh)
      (FramedPuncturedGrid.vertexConnection base lifted.mesh) pairing firstActive lastActive

/-- The canonical cut polygon has exactly the vertex fibers prescribed by its actual paired edge endpoints, uniformly in
genus. -/
theorem cutVertexJoin_iff (lifted : Meshes.LiftedPuncturedGrid base)
    {first last : Fin lifted.cutPolygon.patch.cut.count}
    (firstActive : CutPatch.ActiveVertex
      lifted.cutPolygon.patch.cut first)
    (lastActive : CutPatch.ActiveVertex
      lifted.cutPolygon.patch.cut last) :
    VertexGluing.PairVertexJoin lifted.cutBoundaryPairs.pairs first last ↔
      lifted.cutPolygon.patch.cut.vertexLabels first = lifted.cutPolygon.patch.cut.vertexLabels last :=
  vertexJoin_iff
    lifted lifted.cutPolygon lifted.cutBoundaryPairs firstActive lastActive

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexGluing
