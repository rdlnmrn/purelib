module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes

public section

/-! Prepare both pullback-to-endpoint requests before selecting the shared
polynomial stage. Their later evaluation consumes the paired chart readings
without rereading any root or changing its owner. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths (ChartGeometry ChartRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus count otherCount depth : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {interval : CommonInterval cover
    otherCover}
  (regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
  (geometry : ChartGeometry (cap := cap) interval
    depth)

set_option genInjectivity false in
/-- Both original pullback-to-endpoint comparison requests at one actual retained common-chart vertex. -/
structure SourceVertexRequest (target : InverseRootPolynomial.Coordinate) (floor : Nat)
    (i : Fin (geometry.tail.length + 1)) where
  /-- The retained endpoint comparison bounds for the actual first-differential cap point. -/ firstBounds :
    EndpointComparison.Data regular (geometry.vertices.get i).first
  /-- The retained endpoint comparison bounds for the actual second-differential cap point. -/ secondBounds :
    EndpointComparison.Data regular (geometry.vertices.get i).second
  /-- The original first-differential endpoint accuracy request. -/ first : EndpointComparison.Request firstBounds
    target floor
  /-- The original second-differential endpoint accuracy request. -/ second : EndpointComparison.Request secondBounds
    target floor

constructive_injectivity SourceVertexRequest

/-- Read the sufficient common model stage of both original vertex requests. -/
@[expose] def sourceModelWeight {target : InverseRootPolynomial.Coordinate} {floor : Nat} (i : Fin (geometry.tail.length
  + 1))
    (request : SourceVertexRequest regular geometry
      target floor i) : Nat := max request.first.index request.second.index

/-- Read the sufficient common endpoint-reading stage of both original vertex requests. -/
@[expose] def sourceReadingWeight {target : InverseRootPolynomial.Coordinate} {floor : Nat} (i : Fin
  (geometry.tail.length + 1))
    (request : SourceVertexRequest regular geometry
      target floor i) : Nat :=
  max request.first.coordinate.rightIndex request.second.coordinate.rightIndex

set_option genInjectivity false in
/-- The complete retained paired source request bank on the actual common-chart geometry.

Exact finite maxima select model and reading stages before choosing the shared polynomial sample. -/
structure SourceChartRequest (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached requests on every actual retained dyadic chart vertex. -/ vertices : Data.Vector.DependentVector
    (SourceVertexRequest regular geometry target floor)
  /-- The cached sufficient common source-model stage. -/ index : Nat
  /-- The model stage is exactly the maximum of both retained requests at every vertex. -/ index_eq : index =
    vertices.maximum (sourceModelWeight regular geometry)
  /-- The cached sufficient common source endpoint-reading stage. -/ readingIndex : Nat
  /-- The reading stage is exactly the maximum of both original endpoint-reading requirements. -/ readingIndex_eq :
    readingIndex = vertices.maximum (sourceReadingWeight
    regular geometry)

constructive_injectivity SourceChartRequest

namespace SourceChartRequest

/-- Cache both original endpoint comparison requests at every actual chart vertex and retain their exact common stage
maxima. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor :=
  let vertices := DependentVector.ofFn (fun i =>
    let firstBounds := EndpointComparison.Data.build regular (geometry.vertices.get i).first
    let secondBounds := EndpointComparison.Data.build regular (geometry.vertices.get i).second
    (⟨firstBounds, secondBounds,
      EndpointComparison.Request.build firstBounds target positive floor,
      EndpointComparison.Request.build secondBounds target positive floor⟩ :
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceVertexRequest regular geometry target floor
        i))
  ⟨vertices, vertices.maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceModelWeight regular
    geometry), rfl,
    vertices.maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceReadingWeight regular
      geometry), rfl⟩

variable {regular geometry} {target : Coordinate} {floor index :
  Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {firstComparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell}

/-- Read the actual indexed parameter of the retained common-chart geometry. -/
@[expose] def Parameter (i : Fin (geometry.tail.length + 1)) : Coordinate :=
  DyadicTrace.indexed interval.edge.left.parameter geometry.tail i

set_option genInjectivity false in
/-- Both exact original pullback values compared with the same retained paired chart reading.

Each original endpoint reading remains unchanged; the paired bound includes both source and chart tolerances. -/
structure PullbackReading (first : ArcSamples.Sample firstComparison sample)
    (second : ArcSamples.Sample secondComparison otherSample)
    {chartTarget : InverseRootPolynomial.Coordinate} {chartFloor stage : Nat}
    {request : CommonChartPaths.ChartRequest interval sample otherSample geometry chartTarget chartFloor}
    (i : Fin (geometry.tail.length + 1))
    (reading : PairedChartRequest.Evaluation (request.entries.get i) stage) (target : InverseRootPolynomial.Coordinate)
      where
  /-- The cached first original pullback polynomial value at this actual chart parameter. -/ firstValue :
    InverseRootPolynomial.Gaussian
  /-- The first cache is exactly the original first pullback evaluated at the inverse source point. -/ first_eq :
    firstValue = first.pullback.value.eval (parent.edge.point
    (Parameter (geometry := geometry)
    i))⁻¹
  /-- The cached second original pullback polynomial value at this actual chart parameter. -/ secondValue :
    InverseRootPolynomial.Gaussian
  /-- The second cache is exactly the original second pullback evaluated at the same inverse source point. -/ second_eq
    : secondValue = second.pullback.value.eval (parent.edge.point
    (Parameter (geometry := geometry)
    i))⁻¹
  /-- The actual first pullback value satisfies its original retained endpoint target. -/ first_close :
    Data.Gaussian.Norm.Basic.normSq (firstValue - reading.first.value) < target
  /-- The actual second pullback value satisfies its original retained endpoint target. -/ second_close :
    Data.Gaussian.Norm.Basic.normSq (secondValue - reading.originalOther.value) < target
  /-- Both exact pullback-to-chart differences satisfy the combined retained source and chart budget. -/ chart_bound :
    PrimitivePoint.Bounded
    (PrimitivePoint.sub ⟨firstValue, secondValue⟩ reading.chartPoint)
    (2 * (target + 4 * chartTarget))

constructive_injectivity PullbackReading

/-- Certify the actual pullback polynomials at every retained parameter. The chart values and both original root
readings are consumed unchanged. -/
@[expose] def read (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor)
    (first : ArcSamples.Sample firstComparison sample)
    (second : ArcSamples.Sample secondComparison otherSample)
    (modelLater : prepared.index ≤ index)
    {chartTarget : InverseRootPolynomial.Coordinate} {chartFloor stage : Nat}
    {request : CommonChartPaths.ChartRequest interval sample otherSample geometry chartTarget chartFloor}
    (readingLater : prepared.readingIndex ≤ stage)
    (i : Fin (geometry.tail.length + 1))
    (reading : PairedChartRequest.Evaluation (request.entries.get i) stage) :
    PullbackReading (request :=
      request) first second i reading target := by
  let vertex := prepared.vertices.get i
  have modelBound : max vertex.first.index vertex.second.index ≤ index :=
    (DependentVector.get_le_maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceModelWeight
      regular geometry) prepared.vertices i).trans
      (prepared.index_eq.symm.trans_le modelLater)
  have readingBound : max vertex.first.coordinate.rightIndex vertex.second.coordinate.rightIndex ≤ stage :=
    (DependentVector.get_le_maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceReadingWeight
      regular geometry) prepared.vertices i).trans
      (prepared.readingIndex_eq.symm.trans_le readingLater)
  let firstValue := first.pullback.value.eval (parent.edge.point
    (Parameter (geometry := geometry)
    i))⁻¹
  let secondValue := second.pullback.value.eval (parent.edge.point
    (Parameter (geometry := geometry)
    i))⁻¹
  have firstClose : Data.Gaussian.Norm.Basic.normSq (firstValue - reading.first.value) < target := by
    rw [reading.first.sample_eq]
    exact vertex.first.accurate first (request.entries.get i).first
      ((Data.Nat.Order.le_max_left _ _).trans modelBound) ((Data.Nat.Order.le_max_left _ _).trans readingBound)
  have secondClose : Data.Gaussian.Norm.Basic.normSq (secondValue - reading.originalOther.value) < target := by
    rw [reading.originalOther.sample_eq]
    exact vertex.second.accurate second (request.entries.get i).originalOther
      ((Data.Nat.Order.le_max_right _ _).trans modelBound) ((Data.Nat.Order.le_max_right _ _).trans readingBound)
  have error := Evaluation.point_error reading
  have firstError := error.1
  have secondError := error.2
  change Data.Gaussian.Basic.Canonical.normSq (reading.first.value - reading.chartPoint.left) ≤
    4 * chartTarget at firstError
  change Data.Gaussian.Basic.Canonical.normSq (reading.originalOther.value - reading.chartPoint.right) ≤
    4 * chartTarget at secondError
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstError secondError
  refine ⟨firstValue, rfl, secondValue, rfl, firstClose, secondClose, ?_, ?_⟩
  · change Data.Gaussian.Basic.Canonical.normSq (firstValue - reading.chartPoint.left) ≤ _
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via firstValue reading.first.value
      reading.chartPoint.left).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct firstClose.le firstError) (by decide))
  · change Data.Gaussian.Basic.Canonical.normSq (secondValue - reading.chartPoint.right) ≤ _
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via secondValue reading.originalOther.value
      reading.chartPoint.right).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct secondClose.le secondError) (by decide))

/-- The dependent vector of actual paired pullback readings on the exact retained chart reading bank. -/
@[expose] def PullbackReadings (first : ArcSamples.Sample firstComparison sample)
    (second : ArcSamples.Sample secondComparison otherSample)
    {chartTarget : InverseRootPolynomial.Coordinate} {chartFloor : Nat}
    {request : CommonChartPaths.ChartRequest interval sample otherSample geometry chartTarget chartFloor}
    (readings : request.Readings) (target : InverseRootPolynomial.Coordinate) :=
  Data.Vector.DependentVector (fun i =>
    PullbackReading (request :=
    request) first second i (readings.get i) target)

set_option genInjectivity false in
/-- The retained paired chart-area acquisition with every exact original source pullback comparison. -/
structure Evaluation (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor)
    (first : ArcSamples.Sample firstComparison sample)
    (second : ArcSamples.Sample secondComparison otherSample) (requested : InverseRootPolynomial.Coordinate) where
  /-- The retained caller-supplied lower endpoint-reading stage. -/ readingFloor : Nat
  /-- The actual chart request above both the original source reading index and retained caller floor. -/ request :
    CommonChartPaths.ChartRequest interval sample otherSample geometry requested (max prepared.readingIndex
    readingFloor)
  /-- The cached complete paid paired chart-area evaluation. -/ area : ChartPathRequest.RequestedArea request requested
  /-- The actual original pullback comparisons against these exact cached chart readings. -/ pullbacks :
    PullbackReadings first second
    area.evaluated.readings target

constructive_injectivity Evaluation

/-- The reading floor comes from the pre-sample source requests; the paired area allocator may refine it further,
retaining all cached endpoints. -/
@[expose] def evaluate (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor)
    (first : ArcSamples.Sample firstComparison sample)
    (second : ArcSamples.Sample secondComparison otherSample)
    (modelLater : prepared.index ≤ index) (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested)
      (readingFloor : Nat) :
    Evaluation prepared first second
      requested := by
  let request := ChartPathRequest.build geometry.joins sample otherSample requested positive (max prepared.readingIndex
    readingFloor)
  let area := request.acquireRequestedArea requested positive
  have readingLater : prepared.readingIndex ≤ area.refined.stage := (Data.Nat.Order.le_max_left _ _).trans
    area.refined.floor_le
  let pullbacks := DependentVector.ofFn (fun i => prepared.read first second modelLater readingLater i
    (area.evaluated.readings.get i))
  exact ⟨readingFloor, request, area, pullbacks⟩

/-- The paid chart evaluation's actual reading stage meets its retained caller floor. -/
theorem Evaluation.readingFloor_le {prepared :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor}
    {first : ArcSamples.Sample firstComparison sample}
    {second : ArcSamples.Sample secondComparison otherSample} {requested : InverseRootPolynomial.Coordinate}
    (evaluated : Evaluation prepared
      first second requested) : evaluated.readingFloor ≤ evaluated.area.refined.stage :=
  (Data.Nat.Order.le_max_right _ _).trans evaluated.area.refined.floor_le

end SourceChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
