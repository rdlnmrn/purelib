module
import Purelib.Riemann.Integration.RectangularSharedPrimitives

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceDirection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseJunctions
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-!
# Canonical readings under reversal of the containing edge

Reorienting a retained route preserves its face, sheet and cached primitive
point readings. Opposite presentations of the same lifted edge therefore
select identical point readings when their traversal flags are reversed.
-/

open Purelib.Riemann.Integration.RectangularSharedPrimitives renaming SharedPrimitiveValues -> SharedValues

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseRoutes

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {numerator : CoefficientPolynomial}

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {source : Differentials.Basic.Differential genus} {axes :
    PreparedPrimitiveSplits.PrimitiveAxes base.bank.grid}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars} {mesh :
    Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Fraction.Rational}
  {points : List Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} {index : Nat}
  {budgets : Face.CommonMeshes.FaceMeshBudgets source points tolerance (numerator := numerator) domains}
    {numerics : Face.PrimitiveData.FacePrimitiveBank source index (numerator := numerator) domains}

/-- Reorientation changes neither the selected face nor the sheet used by
the actual shared primitive point lookup. -/
theorem reverseRoute_point_eq {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge.reverse) (shared :
      Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared
        (RouteWords.reverseRoute route)).atSheet
        (RouteWords.reverseRoute route).sheet).readings point =
      SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared route).atSheet
        route.sheet).readings point := by
  cases route with
  | forward location => rfl
  | backward location => rfl

/-- Opposite original edges with reversed traversal flags select the same retained primitive point reading. -/
private theorem directed_reverse_point_eq {left right : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (leftSupported : left ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      left.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (rightSupported : right ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      right.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    {first last : Bool} (edgeEq : left = right.reverse) (directionEq : first = !last)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared
        (RouteWords.directedRoute mesh left leftSupported first)).atSheet
      (RouteWords.directedRoute mesh left leftSupported
        first).sheet).readings point =
    SharedValues.atPoint
      ((Face.MeshWords.FaceSharedMeshes.atRoute shared
        (RouteWords.directedRoute mesh right rightSupported last)).atSheet
      (RouteWords.directedRoute mesh right rightSupported
        last).sheet).readings point := by
  cases edgeEq
  rcases right with ⟨start, finish⟩
  cases last <;> cases directionEq
  · exact (ReverseRoutes.reverseRoute_point_eq (edge := ⟨start, finish⟩)
      (MeshPathWalks.EdgeRoute.build mesh ⟨finish, start⟩ leftSupported) shared
        point).symm
  · exact ReverseRoutes.reverseRoute_point_eq (edge := ⟨finish, start⟩)
      (MeshPathWalks.EdgeRoute.build mesh ⟨start, finish⟩ rightSupported) shared
        point

/-- This is equality of retained primitive values, not merely equality of
coordinates. The hypothesis identifies the actual lifted reversed edge. -/
theorem canonicalPoint_eq_reverse {left right : RootedWords.LiftedFragment
  axes domains mesh source count target}
    (edgeEq : left.occurrence.side.edge = right.occurrence.side.edge.reverse)
    (directionEq : (RouteWords.routeForward left) =
      !(RouteWords.routeForward right))
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) (point :
      Gaussian.Basic.Canonical) :
    (RouteCancellation.canonicalPoint left) shared point =
      (RouteCancellation.canonicalPoint right) shared point :=
  ReverseRoutes.directed_reverse_point_eq _ _ edgeEq directionEq shared
    point

/-- The actual original junction and moving source certificates discharge
both the sheet and direction obligations for opposite edge presentations. -/
theorem Junction.canonical_join_reverse {left right :
  RootedWords.LiftedFragment axes domains mesh source count target}
    (joined : WordJunctions.Junction left right)
    {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    (leftSource : Paths.PreparedSegmentSources.SegmentSource segment left.parent)
    (rightSource : Paths.PreparedSegmentSources.SegmentSource segment right.parent)
    (leftMoving : left.last ≠ left.first) (rightMoving : right.last ≠ right.first)
    (startEq : left.fragment.source.start = right.fragment.source.finish)
    (finishEq : left.fragment.source.finish = right.fragment.source.start)
    (shared : Face.CommonMeshes.FaceSharedMeshes budgets numerics) :
    (RouteCancellation.canonicalPoint left) shared left.last =
      (RouteCancellation.canonicalPoint right) shared right.first := by
  obtain ⟨roots⟩ := joined.2.1
  exact (ReverseRoutes.canonicalPoint_eq_reverse
    (left.occurrence.edge_eq_of_reverse_query_junction right.occurrence joined.1 roots startEq finishEq)
    (SourceDirection.routeForward_reverse_of_source leftSource rightSource
      leftMoving rightMoving startEq finishEq) shared left.last).trans
      (congrArg ((RouteCancellation.canonicalPoint right) shared) joined.1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseRoutes
