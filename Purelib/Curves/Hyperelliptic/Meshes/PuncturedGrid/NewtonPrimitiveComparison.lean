module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedPrimitiveSideArea
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedBoundarySegments
public import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives

public section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

/-!
# Newton-band bounds consumed by actual shared face primitives

A retained segment comparison on a Newton side supplies all parent geometry.
Its fixed reference sum is resampled under the band error ceiling. Every later
shared face bank, with its actual oriented sheet and corner ownership, then
inherits the shrinking bound. The reference also caches the full polynomial
trace on its actual resampled children, including a nonzero-origin bound.
Identifying this trace with the shared face bank along the whole two-lap
boundary still requires the pathwise comparison, not just equal totals.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
    {ambient : Rational.Box}
  {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start
    finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {fixed : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile differential.exponent}
  {target tolerance : Fraction.Rational}

set_option genInjectivity false in
/-- Both the original face reference and its boundary-controlled sample are
cached. Geometry is attached to the original occurrence, not a new segment. -/
structure NewtonReference (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
  placement piece differential parentSheet)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target) (tolerance : Fraction.Rational)
      where
  /-- The original segment's first endpoint lies in the retained Newton output box. -/ firstInside :
    band.sample.output.box.Contains start
  /-- The original segment's last endpoint lies in the retained Newton output box. -/ lastInside :
    band.sample.output.box.Contains finish
  /-- The original endpoints occupy the same retained Newton-box side. -/ side : Paths.PreparedBoundarySegments.SameSide
    band.sample.output.box start finish
  /-- The cached original face primitive reference with its retained target and entered owner. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference compared.entered tolerance
  /-- The original reference request sampled under the retained Newton-band error ceiling. -/ sampled :
    RootContinuation.PreparedNewtonPrimitiveComparison.PrimitiveSample band reference.request.toPrimitiveSumRequest
  /-- The cached complete original polynomial area trace on the actual resampled children. -/ area :
    RootContinuation.PreparedNewtonPrimitiveArea.PrimitiveSample.AreaSample sampled

constructive_injectivity NewtonReference

namespace NewtonReference

variable {compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
  differential parentSheet} {band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target}

/-- The original domain-primitive bank for the retained entered segment and selected numerical stage. -/
abbrev PointDomain (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
  placement piece differential parentSheet) (index : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives compared.entered.domain differential index

/-- Reuse a reference already shared with period consumers. All numerical
and parent-boundary obligations are discharged by retained certificates. -/
@[expose] def ofReference (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
  placement piece differential parentSheet)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (reference : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference compared.entered tolerance)
    (first : band.sample.output.box.Contains start) (last : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish) :
      Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared band tolerance :=
  let sampled := RootContinuation.PreparedNewtonPrimitiveComparison.PrimitiveSample.build band
    reference.request.toPrimitiveSumRequest
    compared.entered.cache.proper (fun _ member => Paths.PreparedSegmentBoundaryGeometry.segment_parent_boundary
      compared.entered.cache first last side member)
  ⟨first, last, side, reference, sampled,
    RootContinuation.PreparedNewtonPrimitiveArea.PrimitiveSample.areaSample sampled⟩

/-- Prepare the original face reference and cache its Newton-band sample and complete resampled area trace. -/
@[expose] def build (compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
  placement piece differential parentSheet) (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed
  target)
    (positive : 0 < tolerance) (first : band.sample.output.box.Contains start) (last : band.sample.output.box.Contains
      finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish) :
      Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared band tolerance :=
  Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference.ofReference compared band
    (Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.build compared.entered tolerance positive)
    first last side

/-- The original segment displacement is bounded by thirty-two times the retained Newton radius squared. -/
private theorem movement_le (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference
  compared band tolerance) :
    Data.Gaussian.Norm.Basic.normSq (finish - start) ≤ 32 * band.sample.output.radius ^ 2 :=
  (band.sample.output.box.normSq_sub_le_diagonalSq bounded.lastInside bounded.firstInside).trans
    (band.sample.output.band.diagonalSq_le band.sample.output.radiusPositive)

/-- The retained original Newton-band integral sample satisfies its target squared-norm bound. -/
theorem sample_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared
  band tolerance) :
    Data.Gaussian.Norm.Basic.normSq bounded.sampled.sample.integralSample ≤ target :=
  bounded.sampled.integral_bound (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth
    (Paths.PreparedSegmentBoundaryGeometry.segment_parentCount compared.entered.cache)
    bounded.movement_le (fun _ member => (Paths.PreparedSegmentBoundaryGeometry.segment_parent_movement
      compared.entered.cache member).le)

/-- The cached original reference sum is bounded by twice its quarter tolerance plus Newton target. -/
theorem reference_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared
  band tolerance) :
    Data.Gaussian.Norm.Basic.normSq bounded.reference.value ≤ 2 * (tolerance / 4 + target) := by
  rw [bounded.reference.value_eq]
  exact bounded.sampled.primitive_bound (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth
    (Paths.PreparedSegmentBoundaryGeometry.segment_parentCount compared.entered.cache)
    bounded.movement_le (fun _ member => (Paths.PreparedSegmentBoundaryGeometry.segment_parent_movement
      compared.entered.cache member).le)

/-- The complete retained resampled area trace has the exact original reference sum as its total. -/
theorem area_total (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared band
  tolerance) :
    bounded.area.source.total = bounded.reference.value := bounded.area.source_total.trans
      bounded.reference.value_eq.symm

/-- The full fine trace uses the retained reference's polynomial bank on
the actual resampled children. Both subdivision levels have disappeared. -/
theorem primitive_area_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference
  compared band tolerance) :
    Data.Gaussian.Norm.Basic.normSq bounded.area.source.area ≤ 256 * (tolerance / 4) * (tolerance / 4 + target) + 32
      * target ^ 2 :=
  bounded.area.paid (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth
    (Gaussian.Norm.Basic.normSq_nonneg _)
    (Paths.PreparedSegmentBoundaryGeometry.segment_parentCount compared.entered.cache) bounded.movement_le
    (fun _ member => (Paths.PreparedSegmentBoundaryGeometry.segment_parent_movement compared.entered.cache member).le)

/-- The actual retained fine trace satisfies the paid area bound including its supplied nonzero anchor contribution. -/
theorem primitive_trace_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference
  compared band tolerance) (anchor : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea anchor
      (Readings.PreparedPrimitiveSideArea.areaBlocks bounded.sampled.sample.requests |>.map Prod.fst).flatten) ≤
      512 * (tolerance / 4) * (tolerance / 4 + target) + 64 * target ^ 2 + 16 * Data.Gaussian.Norm.Basic.normSq
        anchor * (tolerance / 4 + target) := by
  rw [bounded.area.trace_eq]
  exact bounded.area.trace_bound anchor (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth
    (Gaussian.Norm.Basic.normSq_nonneg _)
    (Paths.PreparedSegmentBoundaryGeometry.segment_parentCount compared.entered.cache) bounded.movement_le
    (fun _ member => (Paths.PreparedSegmentBoundaryGeometry.segment_parent_movement compared.entered.cache member).le)

/-- The Newton reference also controls arbitrary retained boundary readings.
The endpoint equalities identify coordinates only; the supplied domain data
and fixed reference retain the actual sheet and path ownership. -/
theorem point_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared
  band tolerance)
    {index : Nat} (later : bounded.reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference.PointDomain compared index)
    {count : Nat} {points : Fin count → Gaussian.Basic.Canonical}
    (readings : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = start) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq (readings.values last - readings.values first) ≤ 3 * tolerance + 4 * target :=
      by
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_bound bounded.reference band
    bounded.firstInside bounded.lastInside bounded.side
    later data readings first last firstEq lastEq

/-- The actual selected face/sheet corner increment tends to zero with the
band budget and reference tolerance. No fine parent or child count remains. -/
theorem corner_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared
  band tolerance)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {index : Nat} (later : bounded.reference.budget.grid.index ≤ index) (shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement placement.location) ≤ 3 * tolerance + 4 * target := by
  have coordinates := Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.corner_coordinates placement.location
  have bounded := bounded.point_bound later (compared.sharedData shared aligned)
    (compared.sharedData shared aligned).corners
    placement.location.corners.start placement.location.corners.finish
    ((congrArg Prod.fst coordinates).trans placement.start_eq)
    ((congrArg Prod.snd coordinates).trans placement.finish_eq)
  rw [compared.sharedData_corners] at bounded
  exact bounded

/-- Sewing sees these very triangle-source values, including orientation,
root-sheet choice and the shared corner bank's paid ownership errors. -/
theorem triangle_bound (bounded : Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison.NewtonReference compared
  band tolerance)
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} (aligned :
      compared.domains = domains.atRoute placement.location)
    {index : Nat} (later : bounded.reference.budget.grid.index ≤ index) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values) ≤ 3 * tolerance + 4 *
      target := by
  rw [readings.route_increment]
  exact bounded.corner_bound aligned later shared

end NewtonReference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPrimitiveComparison
