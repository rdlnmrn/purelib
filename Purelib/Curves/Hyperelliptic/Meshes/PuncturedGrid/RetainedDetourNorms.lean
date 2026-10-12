module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues
import Purelib.Data.Gaussian.Norm.Sum.Prefix
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# Squared increment bounds through retained side detours

Each original diagonal is at most two retained side increments. The sum of
squared original increments is therefore bounded by twice the corresponding
sum on the actual prepared segments. Both orientations keep the same face.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat}

/-- Reading a retained route spine preserves the original indexed word length. -/
theorem RouteSpine.values_length
    {α : Type} (value : (edge : Topology.Polygon.Stokes.OrientedEdge vertices.count) →
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge → α) :
    ∀ {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} (spine :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word), (spine.values value).length = word.length
  | _, .nil => rfl
  | _, .cons _ tail => congrArg Nat.succ
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh.RouteSpine.values_length value
        tail)

/-- An original edge increment is bounded in squared norm by twice the squared-increment sum on its retained side
detour. -/
theorem EdgeRoute.detour_norm_le (cached : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  differential index domains)
    {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    Data.Gaussian.Norm.Basic.normSq (cached.edgeIncrement route) ≤
      2 * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (route.detourRoutes.values (fun _ next => cached.edgeIncrement
        next)) := open Purelib.Data.Rat in by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourValues.BranchCellBank.LiftedMesh.EdgeRoute.detour_sum
    cached route]
  have estimate := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le
    (route.detourRoutes.values (fun _ next => cached.edgeIncrement next))
  have spineLength := Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh.RouteSpine.values_length
    (fun _ next => cached.edgeIncrement next) route.detourRoutes
  rw [spineLength, ← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct route.detour_length_le) (Gaussian.Basic.Canonical.Norm.Sum.Prefix.nonnegative
      _))

/-- The original routed word's squared-increment sum is at most twice that of its exact retained detoured word. -/
theorem RouteSpine.detoured_norm_le (cached : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  differential index domains) :
    ∀ {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} (spine :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word),
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum (spine.values (fun _ route => cached.edgeIncrement route)) ≤
        2 * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (spine.detoured.values (fun _ route => cached.edgeIncrement
          route))
  | _, .nil => by change (0 : Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate) ≤ 2 * 0; rw [mul_zero]
  | _, .cons head tail => by
      change Gaussian.Basic.Canonical.normSq (cached.edgeIncrement head) + Gaussian.Norm.Sum.Basic.gaussianNormSqSum
        (tail.values (fun _ route => cached.edgeIncrement route)) ≤
        2 * Gaussian.Norm.Sum.Basic.gaussianNormSqSum ((head.detourRoutes.append tail.detoured).values (fun _ route =>
          cached.edgeIncrement route))
      rw [Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.values_append,
        Purelib.Data.Gaussian.Basic.Canonical.Norm.Sum.Prefix.append]
      have firstScalar := Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh.EdgeRoute.detour_norm_le
        cached head
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      exact (Rat.Fraction.Order.Arithmetic.add_le_add_direct firstScalar
        (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh.RouteSpine.detoured_norm_le
          cached tail)).trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.FaceBank

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {source : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The original period route's squared-increment sum is bounded by twice the sum over its actual retained prepared side
segments. -/
theorem ofSegments_norm_sum (prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted
  source)
    (segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank prepared.period)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat}
    (cached : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (prepared.routed.spine.values (fun _ route => cached.edgeIncrement route))
      ≤
      2 * Gaussian.Norm.Sum.Basic.gaussianNormSqSum
        (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements cached
        (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments).assigned) := by
  change _ ≤ 2 * Gaussian.Norm.Sum.Basic.gaussianNormSqSum
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests.AssignedSegments.cornerIncrements cached
    (Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments.build segments.pieces prepared.pathFaces))
  rw
    [RetainedDetourValues.BranchCellBank.LiftedMesh.AssignedSegments.build_cornerIncrements,
    prepared.pathFaces_eq]
  simp only [Meshes.GridLiftedMesh.LiftedMesh.PathFaces.ofRoutes_values,
    Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.values_castWord]
  exact Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.LiftedMesh.RouteSpine.detoured_norm_le
    cached prepared.routed.spine

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourNorms.FaceBank
