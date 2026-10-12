module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
public import Purelib.Topology.Surface.Chord.SourceBanks
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Budget.PreparedPrimitiveBatchBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples

/-!
# Sewn chord jumps compared with the actual routed period programs

Canonical routing selects the unique positive original triangle occurrence
of each chord edge. Retained-face detours preserve its primitive increment.
The resulting comparison needs no caller-supplied source alignment, while
still paying the actual sewn-path allowance and analytic sampling tolerance.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison

open Purelib.Curves
open Purelib.Data
open Purelib.Riemann
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

/-- Canonical routing reads exactly the supplied positive original triangle-source occurrences for the retained cycle.

Duplicate-free oriented incidence and injective triangle corners identify every source occurrence, preserving the
cycle's ordered edge list. -/
theorem build_sourceEdges (cycle : Topology.Surface.Sewing.CutCycleChains.ClosedCutCycle
  lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels)))
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (sources :
      Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      cycle.path.cutEdges)
    (positive : sources.Positive) :
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source).routed.spine.values
      (fun _ route => route.sourceEdge) = sources.sources :=
  Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.build_sources lifted.mesh
    sources.sources positive _
    (sources.sources_project.trans cycle.path.projection_eq.symm) _

/-- Checked generated preparations and spines use the same comparison.
Positive occurrence certificates replace equality with any canonical lookup,
cover, subdivision, or numerical witness-producing algorithm. -/
theorem path_program_bound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted
  source) (routedPositive : Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
  prepared.routed.spine)
    (segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank prepared.period)
    {differential : Fin genus} (comparison :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments prepared segments) differential)
    {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat} (result :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
      minimumStage)
    (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result
      lifted.cutPolygon.patch)
    (sources : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      prepared.cycle.path.cutEdges) (positive : sources.Positive) :
    Data.Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values prepared.cycle.finish - sample.surface.sewn.values
      prepared.cycle.start) -
      ((prepared.program differential).integral.model result.sample.stage).integralSample) ≤
        2 * ((Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
          sources).bound + target) := by
  have aligned := Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.sources_eq
    prepared.routed.spine routedPositive sources.sources positive
    (sources.sources_project.trans prepared.cycle.path.projection_eq.symm)
  apply (Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
    sources).compare_bound prepared.cycle.path.endpoints
  rw [(Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
    sources).value_eq_sources, ← aligned,
    Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.source_increments]
  exact (Hyperelliptic.Meshes.PuncturedGrid.Cut.DetourComparison.original_triangles_accurate result sample.triangles).le

/-- The only source condition is positive boundary ownership, checked before
accuracy selection. No equality of independently selected source lists is
assumed, and diagonal detours may change the actual integration word length. -/
theorem build_path_program_bound (cycle : Topology.Surface.Sewing.CutCycleChains.ClosedCutCycle
  lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutPolygon.patch.cut.boundary.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels)))
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (segments :
      Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source).period)
    {differential : Fin genus} (comparison :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source) segments)
      differential)
    {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat} (result :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
      minimumStage)
    (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result
      lifted.cutPolygon.patch)
    (sources : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
      cycle.path.cutEdges) (positive : sources.Positive) :
    Data.Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values cycle.finish - sample.surface.sewn.values
      cycle.start) -
      (((Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source).program
        differential).integral.model result.sample.stage).integralSample) ≤
        2 * ((Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
          sources).bound + target) := by
  apply Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison.path_program_bound
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source) ?_ segments
    comparison result sample sources positive
  change ∀ edge ∈ (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle
    source).routed.spine.values (fun _ route => route.sourceEdge),
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive edge lifted.mesh.triangulation.faces
  rw [Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison.build_sourceEdges cycle source sources positive]
  exact positive

/-- Every canonical chord slot, including empty physical-boundary slots,
gets the comparison without an additional ownership or detour premise. -/
theorem build_chord_program_bound (routes : Topology.Surface.Sewing.ChordCycleBank
  lifted.cutBoundaryWord)
    (index : Fin lifted.cutBoundaryWord.alphabet.count) (source : Hyperelliptic.Differentials.Basic.Differential genus)
    (segments : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted (routes.cycles index)
      source).period)
    {differential : Fin genus}
    (comparison : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks.FaceBank.ofSegments
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted (routes.cycles index) source)
      segments) differential)
    {target : Readings.PreparedPrimitiveChargeBounds.Coordinate} {minimumStage : Nat} (result :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodPrimitiveComparison.PrimitiveBank.RequestedPeriod comparison target
      minimumStage)
    (sample : Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.RequestedPeriod.Sewn result
      lifted.cutPolygon.patch) :
    Data.Gaussian.Norm.Basic.normSq ((sample.surface.sewn.values (routes.cycles index).finish -
      sample.surface.sewn.values (routes.cycles index).start) -
      (((Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted (routes.cycles index)
        source).program differential).integral.model result.sample.stage).integralSample) ≤
        2 * ((Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.CachedSample.pathSample sample.surface
          (Topology.Surface.Chord.SourceBanks.sourceBank lifted.cutPolygon.patch.cut routes index)).bound + target) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison.build_path_program_bound _ source segments comparison result
    sample _ (Topology.Surface.Chord.SourceBanks.sourceBank_positive routes index)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison

end
