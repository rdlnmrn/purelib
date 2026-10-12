module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-! The actual root-closed exterior component consumes the paired boundary
comparison. No terminal radial term or caller root-return proof remains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Integration
open Purelib.Riemann

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} (prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program)

set_option genInjectivity false in
/-- The actual closed exterior comparison with original paired sources and the full joined chart loop.

Its root-closing certificate retains both source and chart area bounds, component totals and all connector
contributions. -/
structure OddClosedBoundaryComparison (other : Hyperelliptic.Differentials.Basic.Differential genus) (requested :
  Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original paired parent request on the complete exterior program cache. -/ original :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other program.cache.parents (requested /
    128) minimum
  /-- The first original covers are exactly the surface preparation's source covers. -/ original_left : original.left =
    prepared.sourceCovers
  /-- The allocated paired boundary request on the original parent plan. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest original (requested / 128)
  /-- The actual closing-root request on that same boundary request. -/ closed :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary.ClosedRequest request (requested / 128)
  /-- The retained successful closed-boundary certificate. -/ certified : closed.Certificate
  /-- The original source primitives retained by the certified boundary evaluation. -/ sources :
    Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Sources certified.retained.boundary
  /-- The comparison of those exact retained sources with their chart paths. -/ charts : sources.ChartComparison
    certified.retained.boundary
  /-- The cached total and area of the complete closed chart trace increments. -/ chartLoop :
    Path.PairedIncrementArea.Summary ((Path.JoinedTraceIncrements.VertexTrace.increments
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace
    certified.retained.boundary) id))
  /-- The cached chart-loop area equals all original chart areas, internal connectors, parent connectors and the closing
    connector. -/ chartLoop_area : chartLoop.areaValue = FiniteSum.Fin.sumFin (fun i =>
    (certified.retained.boundary.entries.get i).chartArea) +
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors
      certified.retained.boundary) +
    FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector
      certified.retained.boundary) +
    certified.closing.connector
  /-- The complete cached chart-loop area meets the requested tolerance. -/ chartLoop_bounded :
    Data.Gaussian.Norm.Basic.normSq chartLoop.areaValue < requested
  /-- The retained complete source-path area meets the requested tolerance. -/ source_bounded :
    Data.Gaussian.Norm.Basic.normSq sources.path.areaValue < requested
  /-- Both retained source-path totals meet the requested component bound. -/ source_total_bounded :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded sources.path.totalValue requested
  /-- The certified closed boundary area meets the requested tolerance. -/ bounded : Data.Gaussian.Norm.Basic.normSq
    certified.area < requested

constructive_injectivity OddClosedBoundaryComparison

/-- Reuse the surface's first-differential covers and the original period
cache. Recasting the second numerator preserves that cache's root geometry.
The original program supplies its own root return, including both odd laps. -/
@[expose] def oddClosedBoundaryComparison (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge other)))
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested)
    (minimum : Nat) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    prepared.OddClosedBoundaryComparison other requested minimum := by
  have localPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 128)
  let original := Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.build regular other
    prepared.sourceCovers right program.cache.proper
    (requested / 128) localPositive minimum
  let request := Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest.build original
    (requested / 128) localPositive
  let closed := Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary.ClosedRequest.build request (requested / 128)
    localPositive
    (Nonempty.map (fun chain => chain.toDirectPathChain) program.cache.chain)
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain program.cache) rfl (by
      change Gaussian.Equivalence.NamedEquivalent
        (Paths.OwnerTraceReadings.ownerName
          (Paths.PreparedPathGluing.finishOwner program.period.closed.traced.prepared))
        (Paths.OwnerTraceReadings.ownerName (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner
          lifted program.sheet))
      rw [← program.period.closed.traced.finishOwner_eq]
      exact program.period.closed.rootReturn)
  let certified := closed.acquire branch
  have paid : 2 * (2 * (requested / 128 + requested / 128) + requested / 128) ≤ requested := by
    calc
      _ = 10 * (requested / 128) := by ring1
      _ ≤ 128 * (requested / 128) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        localPositive.le
      _ = requested := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  let sources := Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.sources certified.retained.boundary
  let boundary := certified.retained.boundary
  let discrepancy := FiniteSum.Fin.sumFin (fun i => (boundary.entries.get i).sourceArea -
    (boundary.entries.get i).chartArea - (boundary.entries.get i).correction)
  have discrepancyBound : Data.Gaussian.Norm.Basic.normSq discrepancy < requested / 128 := by
    have each (i : Fin original.plans.length) : Data.Gaussian.Norm.Basic.normSq ((boundary.entries.get i).sourceArea
      -
        (boundary.entries.get i).chartArea - (boundary.entries.get i).correction) ≤ request.allowance := by
      have smaller : (request.plans.get i).allowance ≤ request.allowance := by
        calc
          _ ≤ request.allowance / 32 := (request.plans.get i).allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _
            _)
          _ = 1 * (request.allowance / 32) := (Fraction.Field.one_mul _).symm
          _ ≤ 32 * (request.allowance / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide +kernel)
            (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide +kernel))
          _ = request.allowance := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by
            decide +kernel)
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (boundary.entries.get i).bounded.le.trans smaller
    have aggregate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ request.allowance each
    have paid := request.paid
    rw [show (original.plans.length : Normalization.InverseRootPolynomial.Coordinate) * ((original.plans.length :
      Normalization.InverseRootPolynomial.Coordinate) * request.allowance) =
      (original.plans.length : Normalization.InverseRootPolynomial.Coordinate)^2 * request.allowance by ring1] at paid
    exact aggregate.trans_lt paid
  let chartBoundary := certified.area - discrepancy
  have chartEq : chartBoundary = FiniteSum.Fin.sumFin (fun i => (boundary.entries.get i).chartArea) +
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors boundary) +
        FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector
        boundary) + certified.closing.connector := by
    dsimp only [chartBoundary, discrepancy, -eq_self, -iff_self]
    rw [certified.boundary_eq, certified.closing.connector_eq]
    unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary.ClosedRequest.Boundary
    rw [boundary.sourceArea_eq, boundary.correction_eq, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub]
    ring1
  have chartBound := (Gaussian.Norm.Bounds.normSq_sub_le_two certified.area discrepancy).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct certified.bounded discrepancyBound))
  have chartPaid : 2 * (2 * (2 * (requested / 128 + requested / 128) + requested / 128) + requested / 128) ≤ requested
    := by
    calc
      _ = 22 * (requested / 128) := by ring1
      _ ≤ 128 * (requested / 128) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        localPositive.le
      _ = requested := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  have loopArea : chartBoundary = Path.PairedIncrementArea.area ((Path.JoinedTraceIncrements.VertexTrace.increments
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace boundary)
    id)) := by
    rw
      [Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace_increment_area
      boundary,
      Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.ClosingPlan.closedChartTrace_area
        boundary closed.closing branch,
      chartEq, certified.closing.connector_eq]
  let chartLoop : Path.PairedIncrementArea.Summary ((Path.JoinedTraceIncrements.VertexTrace.increments
    (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace boundary)
    id)) :=
    ⟨Topology.Polygon.Stokes.PrimitivePoint.zero,
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.closedChartTrace_total
        boundary).symm,
      chartBoundary, loopArea⟩
  let charts := Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Sources.compareCharts boundary sources
  have inserted :=
    Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Sources.ChartComparison.insertion_accurate
    certified.retained sources charts
  rw [Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace_closing_area
    boundary, ← loopArea] at inserted
  have sourceLoop := (Gaussian.Norm.Bounds.normSq_sub_le_via sources.path.areaValue charts.chart.areaValue
    chartBoundary).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 :
      Normalization.InverseRootPolynomial.Coordinate) < 2) (Fraction.Order.Arithmetic.add_lt_add_direct charts.accurate
      inserted))
  have sourceSum := (Gaussian.Norm.Bounds.normSq_add_le_two
    (sources.path.areaValue - chartBoundary) chartBoundary).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 :
      Normalization.InverseRootPolynomial.Coordinate) < 2) (Fraction.Order.Arithmetic.add_lt_add_direct sourceLoop
      chartBound))
  rw [sub_add_cancel] at sourceSum
  have sourcePaid : 2 * (2 * (requested / 128 + requested / 128) +
      2 * (2 * (2 * (requested / 128 + requested / 128) + requested / 128) + requested / 128)) ≤ requested := by
    calc
      _ = 52 * (requested / 128) := by ring1
      _ ≤ 128 * (requested / 128) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        localPositive.le
      _ = requested := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  have insertedTotal :=
    Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Sources.ChartComparison.insertion_total_accurate
    certified.retained sources charts
  have closingTotal :=
    Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.ClosingPlan.trace_total_bounded boundary
    closed.closing
    ((Data.Nat.Order.le_max_right _ _).trans_eq closed.index_eq.symm) localPositive.le branch
  have scalar (a b c : Normalization.InverseRootPolynomial.Gaussian) (source : Gaussian.Basic.Canonical.normSq (a - b) ≤
    requested / 128)
      (inserted : Gaussian.Basic.Canonical.normSq (b - c) ≤ requested / 128) (closing : Gaussian.Basic.Canonical.normSq
        c ≤ requested / 128) :
      Gaussian.Basic.Canonical.normSq a ≤ requested := by
    have first := Gaussian.Norm.Bounds.normSq_sub_le_via a b c
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at first
    have difference := first.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct source
        inserted) (by decide))
    have second := Gaussian.Norm.Bounds.normSq_add_le_two (a - c) c
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at second
    have total := second.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        difference closing) (by decide))
    rw [sub_add_cancel] at total
    exact total.trans paid
  have sourceTotal : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded sources.path.totalValue requested :=
    ⟨scalar _ _ _ charts.total_accurate.1 insertedTotal.1 closingTotal.1,
      scalar _ _ _ charts.total_accurate.2 insertedTotal.2 closingTotal.2⟩
  exact ⟨original, rfl, request, closed, certified, sources,
    charts, chartLoop, chartEq, chartBound.trans_le chartPaid, sourceSum.trans_le sourcePaid,
    sourceTotal, certified.bounded.trans_le paid⟩

/-- The constructed closed comparison's slope is the maximum of the two original retained cover maxima. -/
theorem oddClosedBoundaryComparison_slope (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge other)))
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) (minimum : Nat)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (prepared.oddClosedBoundaryComparison other right requested positive minimum branch).original.slope =
      max (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum prepared.sourceCovers)
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum right) := by
  let comparison := prepared.oddClosedBoundaryComparison other right requested positive minimum branch
  have slope := comparison.original.slope_eq
  rw [comparison.original_left] at slope
  exact slope

/-- The actual exterior source path is compared with the joined parent chart
paths, paying both levels of polygons of totals. -/
theorem OddClosedBoundaryComparison.chart_path_bounded {other : Hyperelliptic.Differentials.Basic.Differential genus}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths
      comparison.certified.retained.boundary).flatten -
      Path.PairedIncrementArea.area (Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.chartPaths
        comparison.certified.retained.boundary).flatten) < requested / 128 := by
  rw [← comparison.sources.path.area_eq, ← comparison.charts.chart.area_eq]
  exact comparison.charts.accurate

/-- The joined chart path already has the bounded full increment area;
adding its closing edge changes neither that area nor the retained excursions. -/
theorem OddClosedBoundaryComparison.joined_chart_path_bounded {other : Hyperelliptic.Differentials.Basic.Differential
  genus} {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      ((Path.JoinedTraceIncrements.VertexTrace.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace
      comparison.certified.retained.boundary) id))) < requested := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.BoundaryBankRequest.Evaluation.chartTrace_closing_area
    comparison.certified.retained.boundary, ← comparison.chartLoop.area_eq]
  exact comparison.chartLoop_bounded

/-- Each original parent now pays insertion of all its common-cover
junctions in the full source-to-chart path area comparison. -/
theorem OddClosedBoundaryComparison.parent_joined_chart_path_bounded {other :
  Hyperelliptic.Differentials.Basic.Differential genus} {requested : Normalization.InverseRootPolynomial.Coordinate}
  {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) (i : Fin
      comparison.original.plans.length) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (comparison.certified.retained.boundary.entries.get i).sourceBlocks.flatten -
      Path.PairedIncrementArea.area (Path.JoinedTraceIncrements.VertexTrace.increments
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.chartTrace
          (comparison.certified.retained.boundary.entries.get i)) id)) <
      comparison.request.allowance := by
  let planned := comparison.request.plans.get i
  have small : planned.allowance ≤ 1 := by
    have divided : comparison.request.allowance / 32 ≤ comparison.request.allowance := by
      calc
        _ = 1 * (comparison.request.allowance / 32) := (Fraction.Field.one_mul _).symm
        _ ≤ 32 * (comparison.request.allowance / 32) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
          decide +kernel)
          (Fraction.Order.Field.div_nonneg_direct comparison.request.positive.le (by decide +kernel))
        _ = comparison.request.allowance := by
          rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
    exact (planned.allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _)).trans (divided.trans
      comparison.request.small)
  rw [← (comparison.certified.retained.boundary.certificates.get i).blocks.source.area_eq]
  exact Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation.joined_source_accurate planned
    (comparison.certified.retained.boundary.entries.get i) (comparison.certified.retained.boundary.certificates.get i)
      small

/-- Requested bound on the full actual source increment path. All interval
and parent junctions have been paid; no origin or chord correction remains. -/
theorem OddClosedBoundaryComparison.path_bounded {other : Hyperelliptic.Differentials.Basic.Differential genus}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths
      comparison.certified.retained.boundary).flatten) < requested :=
  comparison.sources.path.area_eq ▸ comparison.source_bounded

/-- Extract one original controlled source pair with its retained combined depth and paid dyadic reference error. -/
@[expose] def OddClosedBoundaryComparison.sourceEntry {other : Hyperelliptic.Differentials.Basic.Differential genus}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) (i : Fin
      comparison.original.plans.length) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.SourceReferenceEntry comparison.original i := by
  let entry := comparison.certified.retained.boundary.entries.get i
  let controlled := comparison.sources.entries.get i
  let planned := comparison.request.plans.get i
  let depth := (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).common.depth
    + planned.depth
  have rate : 16 * (max (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
    i).data.sourceSlope
      (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
        i).otherData.sourceSlope)^2 *
      ((1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^depth)^2 ≤ planned.allowance := by
    have decreasing := quarterRadius_antitone
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        16) (Fraction.Order.Arithmetic.sq_nonneg_direct
        (max (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
          i).data.sourceSlope
          (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
            i).otherData.sourceSlope)))
      (Nat.le_add_left planned.depth
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).common.depth)
    rw [← pow_mul, Nat.mul_comm depth 2, pow_mul,
      show (1 / 2 : Normalization.InverseRootPolynomial.Coordinate)^2 = 1 / 4 by decide, ←
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact decreasing.trans planned.source_accurate.le
  exact ⟨comparison.request.index, entry.samples.source, entry.samples.otherSource,
    controlled.first, controlled.second, controlled.first_eq, controlled.second_eq, depth, planned.allowance, rate⟩

/-- Keep the odd proof's source samples and cached path while exposing only
the data needed by the parity-independent physical-source comparison. -/
@[expose] def OddClosedBoundaryComparison.toSourceComparison {other : Hyperelliptic.Differentials.Basic.Differential
  genus} {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    (comparison : prepared.OddClosedBoundaryComparison other requested minimum) :
    prepared.ClosedBoundaryComparison other requested minimum := by
  let entries := Data.Vector.DependentVector.ofFn (comparison.sourceEntry prepared)
  have paths : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths entries =
    (Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Evaluation.sourcePaths
    comparison.certified.retained.boundary) := by
    apply Data.List.OfFn.Basic.ofFn_congr
    intro i
    dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths, entries, -eq_self,
      -iff_self]
    rw [Data.Vector.DependentVector.ofFn_get]
    rfl
  let old := comparison.sources.path
  let path : Path.PairedIncrementArea.Summary
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths entries).flatten :=
    ⟨old.totalValue, old.total_eq.trans (congrArg (fun paths => Path.PairedIncrementArea.total paths.flatten)
      paths.symm),
      old.areaValue, old.area_eq.trans (congrArg (fun paths => Path.PairedIncrementArea.area paths.flatten) paths.symm)⟩
  refine ⟨comparison.original, comparison.original_left, entries, comparison.request.allowance,
    comparison.request.positive, ?_, comparison.request.paid, path, comparison.source_bounded,
      comparison.source_total_bounded⟩
  intro i
  dsimp only [entries, -eq_self, -iff_self]
  rw [Data.Vector.DependentVector.ofFn_get]
  change (comparison.request.plans.get i).allowance ≤ comparison.request.allowance
  have divided : comparison.request.allowance / 32 ≤ comparison.request.allowance := by
    apply (Fraction.Order.Field.div_le_iff_pos (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 32)).mpr
    exact (show comparison.request.allowance = comparison.request.allowance * 1 by ring1).le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) comparison.request.positive.le)
  exact ((comparison.request.plans.get i).allowance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _)).trans divided

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
