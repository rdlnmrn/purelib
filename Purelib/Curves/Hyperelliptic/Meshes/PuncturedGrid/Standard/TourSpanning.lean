module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCompleteness
public import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
public import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm

public section

/-!
# Automatic integer spanning coefficients for the actual A/B tours

The canonical root-backed grid supplies all topology inputs. Reuse a
retained normal form, or construct it from the existing paired matrix. Both
original-tour value identities preserve the physical and signed-face terms.
No claim about standard intersection signs or the handle count is made yet.
-/

section

open Purelib.Curves
open Purelib.Data
open Purelib.LinearAlgebra.Alternating
open Purelib.Riemann
open Purelib

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {index : Fin genus} {pair :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning

set_option genInjectivity false in
/-- Integer spanning coordinates for both original A/B tour totals in one retained integral pairing. -/
structure Spanning (coordinates : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) where
  /-- The original A-tour spanning coordinates, retaining physical boundary contributions. -/ a :
    Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates integral coordinates.a.totals
  /-- The original B-tour spanning coordinates, retaining physical boundary contributions. -/ b :
    Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates integral coordinates.b.totals

constructive_injectivity Spanning

/-- Construct both original tour spanning certificates using the supplied retained normal form and actual cut-surface
topology. -/
@[expose] def spanningWith (coordinates :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning coordinates integral :=
  ⟨Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon.closed_spanning lifted.cutPolygon
    lifted.mesh.orientedEdges_unique
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
        lifted.mesh)
      (Meshes.GridLiftedTriangleStars.FramedPuncturedGrid.vertexConnection base lifted.mesh)
      lifted.cutBoundaryPairs integral normal coordinates.a
      coordinates.routes.a_closed coordinates.routes.a.supported,
    Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon.closed_spanning lifted.cutPolygon
      lifted.mesh.orientedEdges_unique
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
        lifted.mesh)
      (Meshes.GridLiftedTriangleStars.FramedPuncturedGrid.vertexConnection base lifted.mesh)
      lifted.cutBoundaryPairs integral normal coordinates.b
      coordinates.routes.b_closed coordinates.routes.b.supported⟩

/-- The existing word reduction supplies the normal form automatically.
Call `spanningWith` when it is already retained by the area consumer. -/
@[expose] def spanning (coordinates : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates
  pair) : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning coordinates lifted.cutIntegralPairing :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.spanningWith coordinates lifted.cutIntegralPairing
    (Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordNormalForm lifted.cutIntegralPairing).normal

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning

/-- The original A-tour value equals its integer pairing combination plus retained physical and signed-face corrections.
-/
theorem a_value {coordinates : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord} (span :
      Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning coordinates integral)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value pair.aFaces.geometry.indexed =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine span.a.coefficients (fun index =>
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (integral.paired index)
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine span.a.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.a.correction := by
  rw [coordinates.a_value value anti, span.a.value_eq]

/-- The original B-tour value equals its integer pairing combination plus retained physical and signed-face corrections.
-/
theorem b_value {coordinates : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates.BoundaryCoordinates pair}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord} (span :
      Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning coordinates integral)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value pair.bFaces.geometry.indexed =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine span.b.coefficients (fun index =>
        Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (integral.paired index)
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine span.b.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.b.correction := by
  rw [coordinates.b_value value anti, span.b.value_eq]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning.Spanning

end
