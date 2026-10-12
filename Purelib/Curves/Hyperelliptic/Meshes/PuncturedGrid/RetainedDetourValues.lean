module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.RectangleDetours
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Topology

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Exact telescoping on the retained face's side detours

Both diagonal halves and both traversal orientations consume the same four
cached values. The two side increments telescope without an analytic error.
The proof then follows the literal original preparation's segment spine.
-/

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge (Kind)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners (triangleValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine EdgeRoute)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {domains : FaceDomainBank frames faces.regulars}
    {differential : Differential genus} {index : Nat}

namespace LiftedFaces.EdgeLocation

/-- The actual retained forward face-side increment is the difference of its original cached endpoint corner values. -/
private theorem forward_increment (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge) (kind :
      RectangleEdge.Kind) :
    cached.edgeIncrement (.forward (location.atKind kind)) =
      ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).finish -
        ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).start :=
  cached.edgeIncrement_eq (.forward (location.atKind kind))

/-- The actual retained reverse face-side increment is the reversed difference of its original cached endpoint corner
values. -/
private theorem backward_increment (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge) (kind :
      RectangleEdge.Kind) :
    cached.edgeIncrement (.backward (mesh := mesh) (edge := (location.lifted.quad.edge kind).reverse) (location.atKind
      kind)) =
        ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).start -
        ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).finish :=
  cached.edgeIncrement_eq (.backward (mesh := mesh) (edge := (location.lifted.quad.edge kind).reverse) (location.atKind
    kind))

/-- The actual retained side detour telescopes exactly to the original endpoint-corner increment. -/
theorem detour_sum (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge) (kind :
      RectangleEdge.Kind) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((EdgeLocation.detourRoutes location kind).values (fun _
      route => cached.edgeIncrement route)) =
      ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).finish -
        ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).start := by
  cases kind <;> simp only [LiftedFaces.EdgeLocation.detourRoutes,
    RouteSpine.values, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
  all_goals simp only
    [forward_increment
    cached location,
    backward_increment
    cached location]
  all_goals dsimp only [FaceCorners.quad,
    IndexedQuadrilateral.edge]; ring1

/-- The reversed actual side detour telescopes exactly to the original reversed endpoint-corner increment. -/
theorem reverse_detour_sum (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (location : LiftedFaces.EdgeLocation mesh.lifts edge) (kind :
      RectangleEdge.Kind) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((EdgeLocation.reverseDetourRoutes location kind).values
      (fun _ route => cached.edgeIncrement route)) =
      ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).start -
        ((cached.get location.position).atSheet location.sheet).corners.values
          (FaceCorners.quad.edge kind).finish := by
  cases kind <;> first
    | exact
      detour_sum
        cached location .upDiagonal
    | (simp only [LiftedFaces.EdgeLocation.reverseDetourRoutes,
       RouteSpine.values, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
         backward_increment
         cached location]
       dsimp only [FaceCorners.quad,
         IndexedQuadrilateral.edge]
       ring1)

end LiftedFaces.EdgeLocation

namespace LiftedMesh

/-- The actual retained side detour telescopes exactly to the original endpoint-corner increment. -/
theorem EdgeRoute.detour_sum (cached : PrimitiveData.FacePrimitiveBank differential index domains)
    {edge : Stokes.OrientedEdge vertices.count} (route : MeshPathWalks.EdgeRoute mesh edge) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (route.detourRoutes.values (fun _ next => cached.edgeIncrement next))
      = cached.edgeIncrement route := by
  cases route with
  | forward location =>
    exact
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedFaces.EdgeLocation.detour_sum
      cached location location.kind).trans (cached.edgeIncrement_eq (.forward location)).symm
  | backward location => exact
    (LiftedFaces.EdgeLocation.reverse_detour_sum
      cached location location.kind).trans (cached.edgeIncrement_eq (.backward location)).symm

/-- The Gaussian sum of concatenated actual increment lists is the sum of their original totals. -/
private theorem sum_append (first second : List Data.Gaussian.Basic.Canonical) :
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ second) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first
  + Data.Gaussian.Norm.Sum.Basic.gaussianSum second := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum second = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum
      second; ring1
  | cons head tail ih => simp only [List.cons_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- Replacing each actual retained mesh route by its original side detour preserves the complete cached increment sum.
-/
theorem RouteSpine.detoured_sum (cached : PrimitiveData.FacePrimitiveBank differential index domains) :
    ∀ {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (spine.detoured.values (fun _ route => cached.edgeIncrement route))
        =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (spine.values (fun _ route => cached.edgeIncrement route))
  | _, .nil => rfl
  | _, .cons head tail => by
      dsimp only [RouteSpine.detoured, RouteSpine.detour]
      rw [RouteSpine.values_append,
        sum_append,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh.EdgeRoute.detour_sum
          cached head,

          RouteSpine.detoured_sum
          cached tail]
      rfl

/-- The actual triangle source-edge readings equal the same route spine's retained cached corner increments entry by
entry. -/
theorem RouteSpine.triangle_values {cached : PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings cached mesh) :
    ∀ {word : List (Stokes.OrientedEdge vertices.count)} (spine : MeshPathWalks.RouteSpine mesh word),
      spine.values (fun _ route => route.sourceEdge.increment readings.values) =
        spine.values (fun _ route => cached.edgeIncrement route)
  | _, .nil => rfl
  | _, .cons head tail => congrArg₂ List.cons (readings.route_increment head)

        (RouteSpine.triangle_values
        readings tail)

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Assigning the actual original covered segment spine to its retained geometry reads exactly the original ordered
cached route increments. -/
theorem AssignedSegments.build_cornerIncrements (cached : PrimitiveData.FacePrimitiveBank differential index domains)
  {ambient : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner}
      (pieces : PreparedPath.CoveredSegments prepared) (geometry : LiftedMesh.PathFaces mesh path),
      AssignedSegments.cornerIncrements cached
        (AssignedSegments.build pieces geometry) =
          geometry.values (fun _ route => cached.edgeIncrement route)
  | _, _, _, _, _, .nil _ _, .nil _ => rfl
  | _, _, _, _, _, .cons _ tail, geometry => by
      cases geometry with
      | cons first rest =>
        exact congrArg (List.cons (cached.edgeIncrement first.location)) (build_cornerIncrements cached tail rest)

end LiftedMesh
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.FaceBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.PathFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (RouteSpine EdgeRoute)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {source :
    Differential genus}

/-- An already checked generated segment bank is allowed. Detour alignment is constructed from the retained geometry,
not supplied by the caller. -/
theorem ofSegments_corner_sum (prepared : CyclePrograms.CutCycleProgram lifted source)
    (segments : PeriodSegmentBanks.SegmentBank prepared.period)
    {domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus} {index : Nat}
    (cached : PrimitiveData.FacePrimitiveBank differential index domains) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (AssignedSegments.cornerIncrements cached
      (FaceBank.ofSegments prepared segments).assigned) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.routed.spine.values (fun _ route => cached.edgeIncrement
        route)) := by
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (AssignedSegments.cornerIncrements cached
    (AssignedSegments.build segments.pieces prepared.pathFaces)) = _
  rw [RetainedDetourValues.BranchCellBank.LiftedMesh.AssignedSegments.build_cornerIncrements]
  rw [prepared.pathFaces_eq]
  simp only [PathFaces.ofRoutes_values,
    RouteSpine.values_castWord]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh.RouteSpine.detoured_sum
    cached prepared.routed.spine

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.FaceBank
