module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Integration.Path

@[expose] public section

/-!
# Full retained chart paths in the shared grid boundary comparison

The original face reference consumes the exact controlled source request
used by the chart acquisition. All parent connectors and chart corrections
are retained. Total preservation transfers the actual triangle-edge bound;
the extra chart area budget is paid independently.
-/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment
    curve.polynomial (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Purelib.Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
    placement piece differential parentSheet}

set_option genInjectivity false in
/-- The original ramified cap comparison paired with an independent chart-area request.

Both use the same retained source request, each with one quarter of the original area allowance. -/
structure RamifiedChartRequest (prepared : SegmentComparison.CapPreparation regular compared) (target areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original ramified cap request with the retained total target and quarter-area allowance. -/ original :
    SegmentComparison.RamifiedCapRequest prepared target (areaTarget / 4) floor
  /-- The actual connected-chart request on the original ramified cap source request. -/ charts :
    ConnectedCharts.ChartRequest original.request (areaTarget / 4)

constructive_injectivity RamifiedChartRequest

namespace RamifiedChartRequest

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation
  regular compared} {target areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare the original ramified cap request and its connected charts with matching positive quarter-area allowances.
-/
def build (prepared : SegmentComparison.CapPreparation regular compared) (target areaTarget :
  InverseRootPolynomial.Coordinate)
    (positive : 0 < target) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
      prepared target areaTarget floor :=
  have quarterPositive := Fraction.Order.Field.div_pos_direct areaPositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let original := RamifiedCapRequest.build prepared target (areaTarget / 4) positive quarterPositive floor
  ⟨original, ConnectedCharts.ChartRequest.build original.request (areaTarget / 4) quarterPositive⟩

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  in
/-- The common maximum stage paying both the original cap comparison and chart acquisition. -/
def index (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  prepared target areaTarget floor) : Nat := max request.original.index request.charts.index

variable {index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request :
    SegmentComparison.RamifiedChartRequest
    prepared target areaTarget floor}

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  in
set_option genInjectivity false in
/-- The retained chart plan on the exact supplied original cap primitive sample. -/
structure Plan (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) where
  /-- The retained chart plan on the exact original ramified source request. -/ chart :
    ConnectedCharts.ChartRequest.Plan request.charts sample

constructive_injectivity Plan

namespace Plan

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  in
/-- Prepare the connected chart plan for the supplied original retained cap sample. -/
def build (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  prepared target areaTarget floor)
    (sample : Primitives.Sample cap differential index box) :
      RamifiedChartRequest.Plan
      request sample :=
  ⟨ConnectedCharts.ChartRequest.Plan.build request.charts sample⟩

set_option genInjectivity false in
/-- The original ramified cap and connected-chart evaluations sharing exactly the same source sample.

The retained equality binds their cap data, and the combined area error satisfies the original target. -/
structure Evaluation (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest.Plan
  request sample) (depth readingIndex : Nat) where
  /-- The actual connected chart evaluation at the supplied subdivision and reading stages. -/ chart :
    ConnectedCharts.ChartRequest.Plan.Evaluation plan.chart depth readingIndex
  /-- The original ramified comparison using the same retained cap evaluation. -/ original :
    RamifiedCapRequest.Evaluation request.original sample depth readingIndex
  /-- The original cap evaluation reuses exactly the chart evaluation's original cap sample. -/ cap_eq : original.cap =
    chart.original
  /-- The original source area and complete connected-chart area differ by less than the retained whole area target. -/
    area_close : Data.Gaussian.Norm.Basic.normSq (chart.original.separated.left.area -
    chart.connected.summary.area) < areaTarget

constructive_injectivity Evaluation

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  in
/-- Evaluate the chart path and reuse its exact original cap data for the ramified comparison. -/
def evaluate (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest.Plan
  request sample) (depth readingIndex : Nat)
    (later : request.index ≤ index) (fineLater : request.charts.depth ≤ depth) (readingLater : plan.chart.stage ≤
      readingIndex) :

      Evaluation
      plan depth readingIndex :=
  let chart := plan.chart.evaluate depth readingIndex ((Nat.Order.le_max_right _ _).trans later) fineLater readingLater
  let original := request.original.evaluateWithCap chart.original
  ⟨chart, original, rfl, chart.area_close.trans_eq (by
    rw [show 2 * (areaTarget / 4 + areaTarget / 4) = areaTarget / 4 * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))⟩

namespace Evaluation

variable {plan :
  RamifiedChartRequest.Plan
  request sample}

/-- The original shared triangle-edge increment and complete chart-path total satisfy the original integral target. -/
theorem triangle_error (evaluated :
  Plan.Evaluation
  plan depth readingIndex)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} (aligned : compared.domains = domains.atRoute
      placement.location)
    {faceIndex : Nat} (later : request.original.budget.grid.index ≤ faceIndex) {shared : PrimitiveData.FacePrimitiveBank
      differential faceIndex domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values -
      evaluated.chart.connected.summary.total) < target := by
  rw [evaluated.chart.total_eq, ← evaluated.cap_eq]
  exact evaluated.original.triangle_error aligned later readings

/-- The chart's full internal area remains in the triangle-to-path formula. The finite primitive origin can include the
original sewing offsets. -/
theorem triangle_area_error (evaluated :
  Plan.Evaluation
  plan depth readingIndex)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} (aligned : compared.domains = domains.atRoute
      placement.location)
    {faceIndex : Nat} (later : request.original.budget.grid.index ≤ faceIndex) {shared : PrimitiveData.FacePrimitiveBank
      differential faceIndex domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) (anchor : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area anchor (anchor +
      placement.location.sourceEdge.increment readings.values) +
      evaluated.chart.connected.summary.area - IncrementArea.traceArea anchor evaluated.chart.connected.paths.flatten) ≤
        4 * Data.Gaussian.Norm.Basic.normSq anchor * target := by
  rw [IncrementArea.traceArea_eq, ← evaluated.chart.connected.summary.area_eq, ←
    evaluated.chart.connected.summary.total_eq]
  have identity : BoundaryRibbon.area anchor (anchor + placement.location.sourceEdge.increment readings.values) +
      evaluated.chart.connected.summary.area - (evaluated.chart.connected.summary.area +
        BoundaryRibbon.area anchor evaluated.chart.connected.summary.total) =
      BoundaryRibbon.area anchor (placement.location.sourceEdge.increment readings.values -
        evaluated.chart.connected.summary.total) := by
    apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
  rw [identity]
  exact (BoundaryRibbon.area_bound _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (evaluated.triangle_error aligned later readings).le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg anchor)))

end Evaluation
end Plan

set_option genInjectivity false in
/-- The cached cap sample and connected-chart evaluation at the retained source, reading and depth stages. -/
structure Acquisition (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  prepared target areaTarget floor) (depthFloor : Nat) where
  /-- The original cap polynomial sample at the common retained request stage. -/ sample : Primitives.Sample cap
    differential request.index collar.box
  /-- The retained chart plan for that exact cached cap sample. -/ plan :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest.Plan
    request sample
  /-- The cached subdivision depth paying the supplied floor and actual chart request. -/ depth : Nat
  /-- The actual depth is the maximum of the supplied floor and original chart depth. -/ depth_eq : depth = max
    depthFloor request.charts.depth
  /-- The connected-chart evaluation cached at that same retained depth and chart reading stage. -/ evaluated :
    Plan.Evaluation
    plan depth plan.chart.stage

constructive_injectivity Acquisition

/-- Cache the original cap sample, chart plan and evaluated replacement path at their retained common stages. -/
def acquire (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.RamifiedChartRequest
  prepared target areaTarget floor) (depthFloor : Nat) :
  Acquisition
  request depthFloor :=
  let sample := Primitives.Sample.build cap differential request.index collar.box
  let plan :=
    Plan.build
    request sample
  let depth := max depthFloor request.charts.depth
  ⟨sample, plan, depth, rfl, plan.evaluate depth plan.chart.stage le_rfl (Nat.Order.le_max_right _ _) le_rfl⟩

end RamifiedChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
