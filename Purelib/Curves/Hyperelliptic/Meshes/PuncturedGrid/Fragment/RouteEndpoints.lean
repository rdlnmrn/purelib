module
import Purelib.Algebra.Group.Basic
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ReverseRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.VertexEdges
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.CompleteGroups
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! The first retained query at a full-edge vertex fixes both the lookup
direction and the actual standard indexed route, including its sheet. -/

section

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AxisCancellation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings.RectangularPrimitiveBoundary
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords (routeForward canonicalRoute directedRoute)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteCancellation (canonicalPoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteContacts (routeValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceGeometry (Presents)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints

/-- The endpoints of every actual retained grid edge are distinct. -/
private theorem edge_endpoints_ne {first last : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge base.bank.grid first
  last) : first ≠ last := by
  induction edge with
  | horizontal interval _ _ _ => exact fun equal => interval.ordered.ne (congrArg Data.Gaussian.Basic.re equal)
  | vertical interval _ _ _ => exact fun equal => interval.ordered.ne (congrArg Data.Gaussian.Basic.im equal)
  | reverse edge ih => exact Ne.symm ih

/-- Equal points on a nondegenerate original segment have equal rational parameters. -/
private theorem pointAt_parameter_eq {ambient : Rational.Box} {first last :
  Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient first last) (different : first ≠ last)
    {a b : Fraction.Rational} (equal : segment.pointAt a = segment.pointAt b) : a = b := by
  have scaled (parameter : Fraction.Rational) : segment.pointAt parameter - first = (⟨parameter, 0⟩ :
    Data.Gaussian.Basic.Canonical) * (last - first) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [ClearSegment.pointAt, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
        Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im, -eq_self, -iff_self] <;> ring1
  have delta := congrArg (fun point : Data.Gaussian.Basic.Canonical => point - first) equal
  rw [scaled, scaled] at delta
  exact congrArg Data.Gaussian.Basic.re
    (Data.Gaussian.Field.mul_right_cancel_of_ne (fun zero => different.symm (Algebra.Group.eq_of_sub_eq_zero zero))
      delta)

/-- A moving query starting at either endpoint must traverse into the edge. The actual rational parameters therefore fix
the route flag. -/
theorem routeForward_at_vertex (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    (moving : piece.last ≠ piece.first) (atStart : Bool)
    (equal : piece.first = if atStart then piece.fragment.source.start else piece.fragment.source.finish) :
    (RouteWords.routeForward piece) = atStart := by
  have distinct := edge_endpoints_ne
    piece.fragment.source.edge
  cases atStart with
  | true =>
      have parameter : piece.fragment.source.first.parameter = 0 :=
        pointAt_parameter_eq _ distinct
          (piece.fragment.source.first.point_eq.trans
          (equal.trans piece.fragment.source.edge.segment.pointAt_zero.symm))
      have ordered : piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter :=
        parameter ▸ piece.fragment.source.last.inside.1
      exact show decide (piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter) = true from
        decide_eq_true ordered
  | false =>
      have parameter : piece.fragment.source.first.parameter = 1 :=
        pointAt_parameter_eq _ distinct
          (piece.fragment.source.first.point_eq.trans
          (equal.trans piece.fragment.source.edge.segment.pointAt_one.symm))
      have backward : ¬piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter := by
        intro ordered
        have lastEq : piece.fragment.source.last.parameter = 1 := le_antisymm piece.fragment.source.last.inside.2
          (parameter ▸ ordered)
        have query := piece.fragment.source.last.point_eq
        rw [lastEq, ClearSegment.pointAt_one] at query
        exact moving (query.symm.trans equal.symm)
      exact show decide (piece.fragment.source.first.parameter ≤ piece.fragment.source.last.parameter) = false from
        decide_eq_false backward

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints

variable {points : List Purelib.Data.Gaussian.Basic.Canonical} {tolerance : Rational} {index :
  Nat}
  {budgets : FaceMeshBudgets source points tolerance
    domains} {numerics : FacePrimitiveBank source
    index domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints

/-- The original directed route reads the same primitive chart as the standard route of its exact oriented edge. -/
private theorem directed_point_build {left right : Stokes.OrientedEdge vertices.count}
    (leftSupported : left ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      left.reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (rightSupported : right ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      right.reverse ∈ Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (forward : Bool) (equal : (if forward then left else left.reverse) = right)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (point : Data.Gaussian.Basic.Canonical) :
    SharedPrimitiveValues.atPoint
      ((FaceSharedMeshes.atRoute shared (RouteWords.directedRoute mesh left leftSupported forward)).atSheet
      (RouteWords.directedRoute mesh left leftSupported forward).sheet).readings point =
    SharedPrimitiveValues.atPoint
      ((FaceSharedMeshes.atRoute shared (EdgeRoute.build mesh right rightSupported)).atSheet
      (EdgeRoute.build mesh right rightSupported).sheet).readings point := by
  cases forward with
  | true => cases equal; rfl
  | false =>
      cases equal
      exact ReverseRoutes.reverseRoute_point_eq (edge := left) (EdgeRoute.build mesh left.reverse rightSupported) shared
        point

/-- The first original query root identifies the very lookup used by the standard grid walk, rather than merely an
incident chart with equal coordinates. -/
theorem canonicalPoint_eq_of_first_vertex (piece : RootedWords.LiftedFragment axes domains mesh source count target)
    (moving : piece.last ≠ piece.first) (atStart : Bool)
    {first last : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge base.bank.grid first last)
    (firstEq : (if atStart then piece.fragment.source.start else piece.fragment.source.finish) = first)
    (lastEq : (if atStart then piece.fragment.source.finish else piece.fragment.source.start) = last)
    (queryEq : piece.first = first)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      piece.firstName)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) (point : Data.Gaussian.Basic.Canonical) :
    (RouteCancellation.canonicalPoint piece) shared point =
      SharedPrimitiveValues.atPoint
      ((FaceSharedMeshes.atRoute shared (EdgeRoute.build mesh (edges.indexedEdge vertices edge (vertices.sheet vertex))
        (SkeletonFaceAssignments.indexedEdge_supported mesh edge _))).atSheet
        (EdgeRoute.build mesh (edges.indexedEdge vertices edge (vertices.sheet vertex))
          (SkeletonFaceAssignments.indexedEdge_supported mesh edge _)).sheet).readings point := by
  have direction := routeForward_at_vertex piece
    moving atStart (queryEq.trans firstEq.symm)
  have indexed := VertexEdges.edge_eq_of_first_vertex piece atStart edge firstEq lastEq queryEq vertex coordinate root
  have oriented : (if (RouteWords.routeForward piece) then piece.occurrence.side.edge else
    piece.occurrence.side.edge.reverse) =
      edges.indexedEdge vertices edge (vertices.sheet vertex) := by rw [direction]; exact indexed
  exact directed_point_build _ _
    (RouteWords.routeForward piece) oriented shared point

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints.RootedWord

/-- A whole original rooted group contributes exactly the standard indexed edge increment on the sheet identified by its
incoming root. -/
theorem routed_increment {head : RootedWords.LiftedFragment axes domains mesh source count target}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    {first last : Data.Gaussian.Basic.Canonical} {firstName lastName : Gaussian.Name.Basic.Named}
    (word : LiftedFragment.RootedWord (head :: pieces) first firstName last lastName)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {segment :
      ClearPath.ClearSegment curve.polynomial ambient start finish}
    (original : ∀ piece ∈ head :: pieces, PreparedSegmentSources.SegmentSource segment piece.parent)
    (moving : ∀ piece ∈ head :: pieces, piece.last ≠ piece.first)
    (geometry : ∀ piece ∈ head :: pieces, (SourceGeometry.Presents piece) first last)
    (edge : Walks.Edge base.bank.grid first last)
    (vertex : Fin vertices.count) (coordinate : vertices.coordinate vertex = first)
    (root : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName (vertices.owner frames vertex))
      firstName)
    (shared : CommonMeshes.FaceSharedMeshes budgets numerics) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((head :: pieces).map (fun piece => (RouteContacts.routeValue piece)
      (RouteWords.canonicalRoute piece) shared)) =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.FaceSharedMeshes.edgeIncrement shared
        (EdgeRoute.build mesh (edges.indexedEdge vertices edge (vertices.sheet vertex))
        (SkeletonFaceAssignments.indexedEdge_supported mesh edge _)) := by
  have incoming : first = head.first ∧ Nonempty (Gaussian.Equivalence.NamedEquivalent firstName head.firstName) := by
    cases word with
    | cons _ equal equivalent _ => exact ⟨equal, equivalent⟩
  obtain ⟨entry⟩ := incoming.2
  have same : ∀ point, (RouteCancellation.canonicalPoint head) shared point =
      SharedPrimitiveValues.atPoint
      ((FaceSharedMeshes.atRoute shared (EdgeRoute.build mesh (edges.indexedEdge vertices edge (vertices.sheet vertex))
        (SkeletonFaceAssignments.indexedEdge_supported mesh edge _))).atSheet
        (EdgeRoute.build mesh (edges.indexedEdge vertices edge (vertices.sheet vertex))
          (SkeletonFaceAssignments.indexedEdge_supported mesh edge _)).sheet).readings point := by
    intro point
    rcases geometry head List.mem_cons_self with forward | backward
    · exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints.canonicalPoint_eq_of_first_vertex head
        (moving head List.mem_cons_self) true edge forward.1 forward.2
        incoming.1.symm vertex coordinate (root.trans entry) shared point
    · exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints.canonicalPoint_eq_of_first_vertex head
        (moving head List.mem_cons_self) false edge backward.1 backward.2
        incoming.1.symm vertex coordinate (root.trans entry) shared point
  rw [RootedWord.presentations_telescope word original moving geometry shared, same last, same first]
  have firstEq : vertices.coordinate (edges.indexedEdge vertices edge (vertices.sheet vertex)).start = first :=
    vertices.coordinate_index _ edge.vertices.1 _
  have lastEq : vertices.coordinate (edges.indexedEdge vertices edge (vertices.sheet vertex)).finish = last :=
    vertices.coordinate_index _ edge.vertices.2 _
  unfold FaceSharedMeshes.edgeIncrement
  rw [firstEq, lastEq]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteEndpoints.RootedWord

end
