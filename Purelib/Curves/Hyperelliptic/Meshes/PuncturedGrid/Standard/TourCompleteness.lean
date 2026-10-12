module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexGluing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Topology.Surface.Cut.PairingKernel
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.VertexSewing
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
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Riemann

open Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Surface.Cut.PairingKernel.SewingForest

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Actual standard tours are detected by the cut pairing and physical edges

All finite topology premises are supplied by the retained root-backed grid.
Every paired-kernel valuation with zero physical values annihilates the
actual A/B boundary rows. Original tour values retain their explicit signed
face corrections; no analytic face-zero or boundary-vanishing theorem is
silently asserted here.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCompleteness

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.JumpPaths.CutPath (Supported)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates (BoundaryCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours (Pair)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge (map)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}

/-- An antisymmetric valuation vanishes on any actual supported closed cut-boundary path when its physical edges and
integral paired-kernel readings vanish. -/
theorem closed_value_zero_of_kernel (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge)
    (physical : ∀ edge ∈ lifted.cutBoundaryPairs.boundary,
      value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge) = 0)
    (kernel : ∀ index, lifted.cutBoundaryWord.alphabet.oneSided index = false →
      WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) = 0)
    {edges : List (Stokes.OrientedEdge lifted.vertices.count)} {anchor : Fin lifted.vertices.count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
    (supported : CutPath.Supported lifted.cutPolygon.patch.boundary edges) : SewingRetraction.wordValue value edges = 0
      :=
    SinglePolygon.closed_value_zero_of_kernel
      lifted.cutPolygon lifted.mesh.orientedEdges_unique
      (LiftedMesh.orientedEdges_nonloop lifted.mesh)
    (FramedPuncturedGrid.vertexConnection base lifted.mesh)
    lifted.cutBoundaryPairs integral value anti physical kernel closed supported

namespace StandardTours.Pair.BoundaryCoordinates

variable {branches : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {index : Fin genus} {pair :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours.Pair lifted index}

/-- The actual retained A and B coordinate rows annihilate every valuation vanishing on the original physical edges and
integral paired kernel. -/
theorem annihilates_kernel (coordinates : TourCoordinates.BoundaryCoordinates pair)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge)
    (physical : ∀ edge ∈ lifted.cutBoundaryPairs.boundary,
      value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge) = 0)
    (kernel : ∀ index, lifted.cutBoundaryWord.alphabet.oneSided index = false →
      WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) = 0) :
    WordCoordinates.combine coordinates.a.totals
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) = 0 ∧
      WordCoordinates.combine coordinates.b.totals
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) = 0 :=
  ⟨(coordinates.a.value_eq value anti).symm.trans
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCompleteness.closed_value_zero_of_kernel lifted integral
        value anti physical kernel coordinates.routes.a_closed coordinates.routes.a.supported),
    (coordinates.b.value_eq value anti).symm.trans
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCompleteness.closed_value_zero_of_kernel lifted integral
        value anti physical kernel coordinates.routes.b_closed coordinates.routes.b.supported)⟩

/-- Original root-closed tours, with every retraction face term retained. -/
theorem values_eq_face_corrections (coordinates : TourCoordinates.BoundaryCoordinates pair)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value
      edge.reverse = -value edge)
    (physical : ∀ edge ∈ lifted.cutBoundaryPairs.boundary,
      value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge) = 0)
    (kernel : ∀ index, lifted.cutBoundaryWord.alphabet.oneSided index = false →
      WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) = 0) :
    SewingRetraction.wordValue value pair.aFaces.geometry.indexed = SewingRetraction.faceValue
      lifted.mesh.triangulation.faces value coordinates.routes.a.correction ∧
      SewingRetraction.wordValue value pair.bFaces.geometry.indexed = SewingRetraction.faceValue
        lifted.mesh.triangulation.faces value coordinates.routes.b.correction := by
  have zero :=
    annihilates_kernel
    coordinates integral value anti physical kernel
  constructor
  · rw [coordinates.a_value value anti, zero.1, zero_add]
  · rw [coordinates.b_value value anti, zero.2, zero_add]

end StandardTours.Pair.BoundaryCoordinates
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCompleteness
