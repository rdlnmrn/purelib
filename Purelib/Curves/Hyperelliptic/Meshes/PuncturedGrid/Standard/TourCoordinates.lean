module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
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
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction.StandardTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction.StandardTours.Pair

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Actual standard-tour rows in the computed cut alphabet

Both integer rows are extracted from the already routed, sheet-labelled
tour words. Their exact period identities retain every signed face term
and every physical-boundary generator. This is a chain comparison, not an
assumed symplectic identification.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours (Pair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction.StandardTours.Pair (BoundaryRoutes)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {index : Fin genus}

set_option genInjectivity false in
/-- The actual routed paths and the two materialized integer rows share the canonical cut alphabet. No new geometric or
analytic witness is requested. -/
structure BoundaryCoordinates (pair : StandardTours.Pair lifted index) where
  /-- The cached actual A and B boundary routes with their original signed face corrections. -/ routes :
    Pair.BoundaryRoutes pair
  /-- The exact retained integer coordinates of the actual routed A word in the original cut alphabet. -/ a :
    BoundaryCoordinates.WordCoordinates lifted.cutBoundaryWord.alphabet routes.a.path
  /-- The exact retained integer coordinates of the actual routed B word in the original cut alphabet. -/ b :
    BoundaryCoordinates.WordCoordinates lifted.cutBoundaryWord.alphabet routes.b.path

constructive_injectivity BoundaryCoordinates

namespace BoundaryCoordinates

variable {pair : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index}

/-- Materialize both actual integer coordinate rows using the supplied retained boundary routes. -/
@[expose] def ofRoutes (routes : Pair.BoundaryRoutes pair) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair :=
  ⟨routes,
    WordCoordinates.build lifted.cutBoundaryWord.alphabet routes.a.path (by
      rw [lifted.cutPolygon.patch.cut.boundary_eq]
      exact routes.a.supported),
    WordCoordinates.build lifted.cutBoundaryWord.alphabet routes.b.path (by
      rw [lifted.cutPolygon.patch.cut.boundary_eq]
      exact routes.b.supported)⟩

/-- Cache the original boundary retraction routes and materialize their exact A and B coordinate rows. -/
@[expose] def build (pair : StandardTours.Pair lifted index) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates.ofRoutes (BoundaryRoutes.build
  pair)

/-- The actual retained A coordinate row has zero boundary at every lifted vertex. -/
theorem a_boundary_zero (coordinates :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair) (vertex : Fin
  lifted.vertices.count) :
    coordinates.a.boundaryAt vertex = 0 := coordinates.a.boundary_zero coordinates.routes.a_closed vertex

/-- The actual retained B coordinate row has zero boundary at every lifted vertex. -/
theorem b_boundary_zero (coordinates :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair) (vertex : Fin
  lifted.vertices.count) :
    coordinates.b.boundaryAt vertex = 0 := coordinates.b.boundary_zero coordinates.routes.b_closed vertex

/-- The original A tour value equals its retained cut-generator combination plus its actual signed face correction. -/
theorem a_value (coordinates : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates
  pair) (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.aFaces.geometry.indexed =
      WordCoordinates.combine coordinates.a.totals
        (fun index => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value coordinates.routes.a.correction :=
  (coordinates.routes.a_value value anti).trans
    (congrArg (· + SewingRetraction.faceValue lifted.mesh.triangulation.faces value coordinates.routes.a.correction)
      (coordinates.a.value_eq value anti))

/-- The original B tour value equals its retained cut-generator combination plus its actual signed face correction. -/
theorem b_value (coordinates : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates
  pair) (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value pair.bFaces.geometry.indexed =
      WordCoordinates.combine coordinates.b.totals
        (fun index => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value coordinates.routes.b.correction :=
  (coordinates.routes.b_value value anti).trans
    (congrArg (· + SewingRetraction.faceValue lifted.mesh.triangulation.faces value coordinates.routes.b.correction)
      (coordinates.b.value_eq value anti))

end BoundaryCoordinates
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
