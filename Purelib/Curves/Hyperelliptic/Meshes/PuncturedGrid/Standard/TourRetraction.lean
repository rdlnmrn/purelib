module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.List.Permutation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Sewing.SewingTree

/-!
# Actual A/B tour words on the canonical cut boundary

The existing sewing tree supplies the chain comparison automatically. Both
tour words reuse one retraction and retain their signed face corrections.
Closure and original sheet-labelled vertices are preserved. This does not
yet identify the resulting boundary cycles with the computed handle basis.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
open Purelib.Data.List
open Purelib.Riemann
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewingConnected
open Purelib.Topology.Surface.Sewing.SewingRetraction

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.SewingRetraction (Retraction WordRoute wordValue faceValue)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath (supported_mono)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- Every actual lifted-triangle edge occurs among the original edges retained by the canonical cut patch.

The cut forest covers the same lifted triangulation. Its original edge permutation transports the displayed occurrence
into the retained cut patch. -/
theorem originalEdge_on_cutPatch (lifted : Meshes.LiftedPuncturedGrid base)
    {edge : Stokes.OrientedEdge lifted.vertices.count}
    (member : edge ∈ Stokes.triangleEdgeOccurrences lifted.mesh.triangulation.faces) :
    edge ∈ SewnPatch.originalEdges lifted.cutPolygon.patch := by
  have coverage := SewingForest.originalEdges_coverage lifted.cutForest
  rewrite [lifted.cutPolygon.equation, Flatten.flatMap_cons] at coverage
  dsimp only [List.flatMap, List.map_nil, List.flatten] at coverage
  rewrite [Append.append_nil] at coverage
  exact (Permutation.mem_iff coverage edge).mpr member

/-- Build the canonical boundary retraction from the actual retained sewing patch. -/
@[expose] def boundaryRetraction (lifted : Meshes.LiftedPuncturedGrid base) :
    SewingRetraction.Retraction lifted.mesh.triangulation.faces lifted.cutPolygon.patch.faceIndices
      lifted.cutPolygon.patch.boundary :=
  Retraction.ofPatch lifted.cutPolygon.patch

namespace StandardTours.Pair

variable {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {index : Fin genus}

set_option genInjectivity false in
/-- One retained retraction and both materialized tour images. No new path preparation, root selection, or analytic
certificate is needed.

The cached routes use the same triangulation and boundary retraction, with separate signed corrections. -/
structure BoundaryRoutes (pair : StandardTours.Pair lifted index) where
  /-- The shared retained retraction of the actual triangulation to its cut boundary. -/ retraction :
    SewingRetraction.Retraction lifted.mesh.triangulation.faces
    lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary
  /-- The cached boundary image and signed face correction of the original A word. -/ a : SewingRetraction.WordRoute
    lifted.mesh.triangulation.faces lifted.cutPolygon.patch.boundary pair.aFaces.geometry.indexed
  /-- The cached boundary image and signed face correction of the original B word. -/ b : SewingRetraction.WordRoute
    lifted.mesh.triangulation.faces lifted.cutPolygon.patch.boundary pair.bFaces.geometry.indexed

constructive_injectivity BoundaryRoutes

namespace BoundaryRoutes

variable {pair : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index}

/-- Route both original tour words using the same supplied retained boundary retraction.

Both original signed tour words are routed through the supplied common retraction, retaining their own face corrections
and starting vertices. -/
@[expose] def ofRetraction (pair : StandardTours.Pair lifted index)
    (retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary) :
        TourRetraction.StandardTours.Pair.BoundaryRoutes pair :=
  ⟨retraction,
    retraction.word pair.aFaces.geometry.indexed
      (CutPath.supported_mono pair.aFaces.supported (fun _ member => TourRetraction.originalEdge_on_cutPatch lifted
        member)),
    retraction.word pair.bFaces.geometry.indexed
      (CutPath.supported_mono pair.bFaces.supported (fun _ member => TourRetraction.originalEdge_on_cutPatch lifted
        member))⟩

/-- Cache the canonical boundary retraction and both original tour images.

The canonical cut patch determines the shared retraction, and both original tour routes cache their exact boundary
images. -/
@[expose] def build (pair : StandardTours.Pair lifted index) : TourRetraction.StandardTours.Pair.BoundaryRoutes pair :=
  TourRetraction.StandardTours.Pair.BoundaryRoutes.ofRetraction pair (TourRetraction.boundaryRetraction lifted)

/-- The retained A boundary image closes on the original selected lifted starting vertex. -/
theorem a_closed (routes : TourRetraction.StandardTours.Pair.BoundaryRoutes pair) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish routes.a.path
      (lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet)
      (lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet) := routes.a.endpoints pair.a_closed

/-- The retained B boundary image closes on the same actual lifted base vertex as A. -/
theorem b_closed (routes : TourRetraction.StandardTours.Pair.BoundaryRoutes pair) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish routes.b.path
      (lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet)
      (lifted.vertices.index _ pair.aFaces.first pair.aFaces.sheet) :=
  (routes.b.endpoints pair.b_closed).castStart pair.common_base.symm |>.castFinish pair.common_base.symm

/-- The original A word, its actual boundary image, and the signed face correction appear in the same exact identity. -/
theorem a_value (routes : TourRetraction.StandardTours.Pair.BoundaryRoutes pair) (value : Stokes.OrientedEdge
  lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (antisymmetric : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.aFaces.geometry.indexed = SewingRetraction.wordValue value routes.a.path +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value routes.a.correction := routes.a.value_eq value
        antisymmetric

/-- The original B word value equals its actual boundary-image value plus the retained signed face correction. -/
theorem b_value (routes : TourRetraction.StandardTours.Pair.BoundaryRoutes pair) (value : Stokes.OrientedEdge
  lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (antisymmetric : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.bFaces.geometry.indexed = SewingRetraction.wordValue value routes.b.path +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value routes.b.correction := routes.b.value_eq value
        antisymmetric

end BoundaryRoutes
end StandardTours.Pair
end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
