module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Nat.Order
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
public import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
public import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-! Original source primitives compare with the paired reciprocal chart on
the actual common interval. Both cell-origin corrections remain explicit;
the cached open ribbon endpoint term is paid by the geometric request. -/
namespace Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon (dyadicArea)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear (dyadicArea_sub_origin)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Integration.Path.PairedIncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon (PairedPullbackRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths (ChartGeometry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources (SourceChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas (SourceAreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (sourceValues)
variable {genus count otherCount depth : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch (recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {interval : CommonInterval cover
    otherCover}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {geometry : ChartGeometry (cap := cap) interval
    depth}
  {target : Coordinate} {floor : Nat}

/-- Allocate one sixty-fourth of the requested error to the source ribbon. -/
@[expose] def sourceRibbonTarget (requested : Coordinate) : Coordinate := ((requested / 4) / 4) / 4

open Purelib.Curves in
open Purelib.Approximation in
set_option genInjectivity false in
/-- Retain a common-stage comparison of two source primitives with one prepared chart.

The original sample owners, ribbon and chart requests are retained together. The chosen stage also pays the endpoint
drift needed to restore the source increment exactly. -/
structure SourceComparisonRequest (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor) (requested : Coordinate) where
  /-- The original first source sample data. -/ first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular
    interval.first.cell
  /-- The original second source sample data. -/ second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular
    interval.second.cell
  /-- The paired source-to-pullback ribbon request at the allocated ribbon target. -/ ribbon :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest first second (sourceRibbonTarget
    requested) floor
  /-- The retained prepared chart request at one quarter of the requested target. -/ chart :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest prepared (requested / 4)
  /-- The cached sum of the two source sample scales. -/ driftScale : Coordinate
  /-- The drift scale is exactly the sum of the original sample scales. -/ driftScale_eq : driftScale = first.scale +
    second.scale
  /-- The retained first permitted index paying the endpoint drift. -/ driftIndex : Nat
  /-- The drift index is the explicit quarter-radius search from the retained floor. -/ driftIndex_eq : driftIndex =
    Rational.Geometric.Search.firstQuarterBelow driftScale floor (sourceRibbonTarget requested)
  /-- The cached quarter-radius error at the drift index. -/ driftError : Coordinate
  /-- The cached drift error is the quarter radius of the retained scale and index. -/ driftError_eq : driftError =
    Rational.Geometric.Basic.quarterRadius driftScale driftIndex
  /-- The chosen drift error is strictly below the source ribbon target. -/ drift_accurate : driftError <
    sourceRibbonTarget requested
  /-- The common stage floor for ribbon, chart and endpoint drift. -/ index : Nat
  /-- The stage floor is exactly the maximum of the three retained indices. -/ index_eq : index = max (max ribbon.index
    chart.refined.index) driftIndex

constructive_injectivity SourceComparisonRequest

namespace SourceComparisonRequest

open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Prepare the source ribbon, chart comparison and endpoint drift at one stage.

For a positive target, the maximum of their retained indices pays all three requests while preserving the supplied
prepared chart and both original sample owners. -/
@[expose] def build (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular
  geometry target floor)
    (first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell)
    (second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell)
    (requested : Coordinate) (positive : 0 < requested) : SourceComparisonRequest prepared requested :=
  let ribbon := Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest.build first second
    (sourceRibbonTarget requested)
    (Rat.Fraction.Order.Field.div_pos_direct (Rat.Fraction.Order.Field.div_pos_direct
      (Rat.Fraction.Order.Field.div_pos_direct positive (by decide)) (by decide)) (by decide)) floor
  let chart := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.build prepared (requested / 4)
    (Rat.Fraction.Order.Field.div_pos_direct positive (by decide))
  let driftScale := first.scale + second.scale
  let driftIndex := Rational.Geometric.Search.firstQuarterBelow driftScale floor (sourceRibbonTarget requested)
  let driftError := Rational.Geometric.Basic.quarterRadius driftScale driftIndex
  ⟨first, second, ribbon, chart, driftScale, rfl, driftIndex, rfl, driftError, rfl,
    Rational.Geometric.Search.firstQuarterBelow_accurate driftScale (add_nonneg first.scale_nonnegative
      second.scale_nonnegative)
      floor (sourceRibbonTarget requested)
      (Rat.Fraction.Order.Field.div_pos_direct (Rat.Fraction.Order.Field.div_pos_direct
        (Rat.Fraction.Order.Field.div_pos_direct positive (by decide)) (by decide)) (by decide)),
    max (max ribbon.index chart.refined.index) driftIndex, rfl⟩

variable {prepared : SourceChartRequest regular
  geometry target floor} {requested : Coordinate}
  {index : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  (request : SourceComparisonRequest prepared requested)
  (source : SourcePrimitive data index)
    (otherSource : SourcePrimitive otherData
    index)
  (first : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample request.first sample)
  (second : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample request.second otherSample)

open Purelib.Curves in
/-- The retained paired ribbon evaluation on the actual common interval at a supplied trace depth. -/
@[expose] def RibbonAt (traceDepth : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedPullbackRibbon.PairedPullbackRequest.Evaluation request.ribbon source
  otherSource first second
  interval.edge.left.parameter interval.edge.right.parameter traceDepth

/-- The retained paired ribbon evaluation at the geometry depth. -/
@[expose] def RibbonEvaluation := RibbonAt request source otherSource first second depth

open Purelib.Curves in
/-- The retained chart request evaluated at the supplied polynomial stage. -/
@[expose] def ChartEvaluation := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation
  request.chart first second

/-- Pair the two source primitive values at their respective original cell origins. -/
@[expose] def sourceOrigin : PrimitivePoint :=
  ⟨source.primitive.value.eval (parent.edge.point interval.first.owner.left.parameter),
    otherSource.primitive.value.eval (parent.edge.point interval.second.owner.left.parameter)⟩

/-- Pair the two retained pullback primitive origin values. -/
@[expose] def capOrigin : PrimitivePoint := ⟨first.firstValue, second.firstValue⟩

section
open Purelib.Curves
/-- The paired area contribution of a source origin against the actual source endpoint increment. -/
@[expose] def SourceOriginTerm (origin : PrimitivePoint) : Gaussian :=
  edgeArea origin ((Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source
    otherSource interval.edge.right.parameter).sub
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
      interval.edge.left.parameter))

/-- The paired area contribution of a pullback origin against the actual polynomial endpoint increment. -/
@[expose] def CapOriginTerm (origin : PrimitivePoint) : Gaussian :=
  edgeArea origin ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues
    first second interval.edge.right.parameter).sub
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
      interval.edge.left.parameter))

/-- Restore the unanchored dyadic source area by adding its exact origin contribution. -/
theorem source_unanchored {traceDepth : Nat} (ribbon : RibbonAt request source otherSource first second traceDepth) :
    ribbon.sourceArea + SourceOriginTerm (interval := interval) source otherSource
      (sourceOrigin (interval := interval) source otherSource) =
      dyadicArea (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source
        otherSource) traceDepth interval.edge.left.parameter interval.edge.right.parameter := by
  rw [ribbon.sourceArea_eq]
  change dyadicArea (fun parameter =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
    parameter).sub
    (sourceOrigin (interval := interval) source otherSource)) traceDepth _ _ + _ = _
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicArea_sub_origin]
  dsimp only [SourceOriginTerm, -eq_self, -iff_self]
  ring1

/-- Restore the unanchored dyadic pullback area by adding its exact origin contribution. -/
theorem cap_unanchored {traceDepth : Nat} (ribbon : RibbonAt request source otherSource first second traceDepth) :
    ribbon.capArea + CapOriginTerm request first second (capOrigin request first second) =
      dyadicArea (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues
        first second)
        traceDepth interval.edge.left.parameter interval.edge.right.parameter := by
  rw [ribbon.capArea_eq]
  change dyadicArea (fun parameter =>
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
    parameter).sub
    (capOrigin request first second)) traceDepth _ _ + _ = _
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicArea_sub_origin]
  dsimp only [CapOriginTerm, -eq_self, -iff_self]
  ring1

/-- The dyadic paired source area centered at the actual common interval's left endpoint. -/
@[expose] def SourceCenteredValue : Gaussian := dyadicArea
  (fun parameter => (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source
    otherSource parameter).sub (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues
    source otherSource interval.edge.left.parameter))
  depth interval.edge.left.parameter interval.edge.right.parameter

/-- The dyadic paired pullback area centered at the actual common interval's left endpoint. -/
@[expose] def CapCenteredValue : Gaussian := dyadicArea
  (fun parameter => (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues
    first second parameter).sub
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
      interval.edge.left.parameter))
  depth interval.edge.left.parameter interval.edge.right.parameter

end

section
open Purelib.Riemann
open Purelib.Curves
/-- Centering a dyadic paired path subtracts exactly its one-edge chord area. -/
private theorem centered_area (values : Coordinate → PrimitivePoint) (depth : Nat) (lower upper : Coordinate) :
    dyadicArea (fun parameter => (values parameter).sub (values lower)) depth lower upper =
      dyadicArea values depth lower upper - dyadicArea values 0 lower upper := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicArea_sub_origin,
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero]
  simp only [edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
  ring1

/-- Centering a dyadic paired path subtracts exactly its one-edge chord area. -/
theorem centered_area_for_evaluate (values : Coordinate → PrimitivePoint) (depth : Nat) (lower upper : Coordinate) :
    dyadicArea (fun parameter => (values parameter).sub (values lower)) depth lower upper =
      dyadicArea values depth lower upper - dyadicArea values 0 lower upper := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins.Bilinear.dyadicArea_sub_origin,
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero]
  simp only [edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
  ring1

end

open Purelib.Data in
/-- Compare centered source and pullback areas with sixteen times the ribbon target.

Subtracting the one-edge chord from the fine path removes the starting-value contributions for each path without an
equality between their original anchors. -/
theorem centered_ribbon (ribbon : RibbonEvaluation request source otherSource first second) :
    Data.Gaussian.Norm.Basic.normSq (SourceCenteredValue (interval := interval) (depth := depth) source otherSource
      -
      CapCenteredValue request first second) < 16 * sourceRibbonTarget requested := by
  let coarse := request.ribbon.evaluate source otherSource first second ribbon.later
    interval.edge.left.parameter interval.edge.right.parameter
    ribbon.leftLower ribbon.leftUpper ribbon.rightLower ribbon.rightUpper ribbon.ordered 0
  have sourceEq : SourceCenteredValue (interval := interval) (depth := depth) source otherSource =
      ribbon.sourceArea - coarse.sourceArea := by
    unfold SourceCenteredValue
    rw [centered_area, ← source_unanchored request source otherSource first second ribbon,
      ← source_unanchored request source otherSource first second coarse]
    ring1
  have capEq : CapCenteredValue request first second = ribbon.capArea - coarse.capArea := by
    unfold CapCenteredValue
    rw [centered_area, ← cap_unanchored request source otherSource first second ribbon,
      ← cap_unanchored request source otherSource first second coarse]
    ring1
  rw [sourceEq, capEq, show (ribbon.sourceArea - coarse.sourceArea) - (ribbon.capArea - coarse.capArea) =
    (ribbon.sourceArea - ribbon.capArea) - (coarse.sourceArea - coarse.capArea) by ring1]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct ribbon.full_accurate coarse.full_accurate)).trans_eq (by ring1))

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Cache the source and chart comparisons at the same permitted stage.

The original anchors, their area contributions and the unanchored and centered source areas are retained with exact
readbacks. Both chart comparisons satisfy the requested squared-error target. -/
structure Evaluation where
  /-- The supplied polynomial stage is no earlier than the retained common floor. -/ later : request.index ≤ index
  /-- The actual retained ribbon evaluation at this stage. -/ ribbon : RibbonEvaluation request source otherSource first
    second
  /-- The actual retained prepared-chart evaluation at this stage. -/ chart : ChartEvaluation request first second
  /-- The cached pair of original source anchors. -/ sourceAnchor : PrimitivePoint
  /-- The cached source anchor equals the original source-origin pair. -/ sourceAnchor_eq : sourceAnchor = sourceOrigin
    (interval := interval) source otherSource
  /-- The cached pair of pullback anchors. -/ capAnchor : PrimitivePoint
  /-- The cached pullback anchor equals the retained pullback-origin pair. -/ capAnchor_eq : capAnchor = capOrigin
    request first second
  /-- The cached source-origin area contribution. -/ sourceOriginTerm : Gaussian
  /-- The cached source contribution uses its retained source anchor. -/ sourceOriginTerm_eq : sourceOriginTerm =
    SourceOriginTerm (interval := interval) source otherSource sourceAnchor
  /-- The cached pullback-origin area contribution. -/ capOriginTerm : Gaussian
  /-- The cached pullback contribution uses its retained pullback anchor. -/ capOriginTerm_eq : capOriginTerm =
    CapOriginTerm request first second capAnchor
  /-- The cached unanchored dyadic source area. -/ sourceArea : Gaussian
  /-- The cached source area is the actual dyadic reading on the common interval. -/ sourceArea_eq : sourceArea =
    dyadicArea (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source
    otherSource)
    depth interval.edge.left.parameter interval.edge.right.parameter
  /-- The cached difference between source and pullback origin contributions. -/ correction : Gaussian
  /-- The correction is exactly the source contribution minus the pullback contribution. -/ correction_eq : correction =
    sourceOriginTerm - capOriginTerm
  /-- The origin-corrected source and original chart areas differ by less than the requested squared-error target. -/
    bounded : Data.Gaussian.Norm.Basic.normSq (sourceArea - chart.retained.area.evaluated.chart.originalArea -
    correction) < requested
  /-- The cached source area centered at the common interval's left endpoint. -/ sourceCenteredArea : Gaussian
  /-- The cached centered area equals the actual centered source reading. -/ sourceCenteredArea_eq : sourceCenteredArea
    = SourceCenteredValue (interval := interval) (depth := depth) source otherSource
  /-- The centered source and chart areas differ by less than the requested squared-error target. -/ centered_bounded :
    Data.Gaussian.Norm.Basic.normSq (sourceCenteredArea - chart.retained.area.evaluated.chart.centeredArea) <
    requested

constructive_injectivity Evaluation

open Purelib.Curves in
/-- The cached centered source area is its unanchored area minus the one-edge source area. -/
theorem Evaluation.source_centered_decomposition
    (evaluated : Evaluation request source otherSource first second) :
    evaluated.sourceCenteredArea = evaluated.sourceArea - dyadicArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
      0 interval.edge.left.parameter interval.edge.right.parameter := by
  rw [evaluated.sourceCenteredArea_eq, evaluated.sourceArea_eq]
  exact centered_area _ _ _ _

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Acquire and retain both comparisons at the supplied common polynomial stage.

The request pays the two quarter-budgets and retains the exact origin correction and centered source area; the reading
floor and later-stage evidence are sufficient. -/
@[expose] def evaluate (later : request.index ≤ index) (readingFloor : Nat) : Evaluation request source otherSource
  first second := by
  have indices := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq.symm.trans_le later)
  let ribbon := request.ribbon.evaluate source otherSource first second ((Data.Nat.Order.le_max_left _ _).trans indices)
    interval.edge.left.parameter interval.edge.right.parameter
    interval.first.lower interval.first.upper interval.second.lower interval.second.upper interval.ordered depth
  let chart := request.chart.evaluate first second ((Data.Nat.Order.le_max_right _ _).trans indices) readingFloor
  let sourceAnchor := sourceOrigin (interval := interval) source otherSource
  let capAnchor := capOrigin request first second
  let sourceOriginTerm := SourceOriginTerm (interval := interval) source otherSource sourceAnchor
  let capOriginTerm := CapOriginTerm request first second capAnchor
  let sourceArea := ribbon.sourceArea + sourceOriginTerm
  let correction := sourceOriginTerm - capOriginTerm
  have capEq : ribbon.capArea + capOriginTerm = chart.pullback.originalArea :=
    (cap_unanchored request source otherSource first second ribbon).trans
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_area_eq
        chart.retained chart.pullback).symm
  have identity : sourceArea - chart.retained.area.evaluated.chart.originalArea - correction =
      (ribbon.sourceArea - ribbon.capArea) + (chart.pullback.originalArea -
        chart.retained.area.evaluated.chart.originalArea) := by
    rw [← capEq]
    dsimp only [sourceArea, correction, -eq_self, -iff_self]
    ring1
  have ribbonPaid : 16 * sourceRibbonTarget requested = requested / 4 := by
    change 16 * (((requested / 4) / 4) / 4) = _
    rw [show 16 * (((requested / 4) / 4) / 4) = ((((requested / 4) / 4) / 4) * 4) * 4 by ring1,
      Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide), Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
  have ribbonPositive : 0 < sourceRibbonTarget requested :=
    Rat.Fraction.Order.Field.div_pos_direct (Rat.Fraction.Order.Field.div_pos_direct request.chart.positive (by decide))
      (by decide)
  have sourceFull := ribbon.full_accurate.trans_le
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel : (4 : Coordinate) ≤ 16)
      ribbonPositive.le).trans_eq ribbonPaid)
  have close := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct sourceFull chart.bounded))
  have paid : 2 * (requested / 4 + requested / 4) = requested :=
    (by ring1 : 2 * (requested / 4 + requested / 4) = requested / 4 * 4).trans
      (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  let sourceCenteredArea := sourceArea - edgeArea
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
    interval.edge.left.parameter)
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
      interval.edge.right.parameter)
  have sourceCenteredEq : sourceCenteredArea = SourceCenteredValue (interval := interval) (depth := depth) source
    otherSource := by
    dsimp only [sourceCenteredArea, sourceArea, SourceCenteredValue, -eq_self, -iff_self]
    rw [source_unanchored request source otherSource first second ribbon, centered_area_for_evaluate,
      Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero]
  have centeredSource : Data.Gaussian.Norm.Basic.normSq (sourceCenteredArea - chart.pullback.centeredArea) <
    requested / 4 := by
    rw [sourceCenteredEq,
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.Evaluation.pullback_centered_eq
      chart.retained chart.pullback]
    exact (centered_ribbon request source otherSource first second ribbon).trans_eq ribbonPaid
  have centeredClose := (Gaussian.Norm.Bounds.normSq_sub_le_via sourceCenteredArea chart.pullback.centeredArea
    chart.retained.area.evaluated.chart.centeredArea).trans_lt
      (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
        (Rat.Fraction.Order.Arithmetic.add_lt_add_direct centeredSource chart.centered_bounded))
  exact ⟨later, ribbon, chart, sourceAnchor, rfl, capAnchor, rfl, sourceOriginTerm, rfl, capOriginTerm, rfl,
    sourceArea, source_unanchored request source otherSource first second ribbon, correction, rfl,
    (congrArg Data.Gaussian.Norm.Basic.normSq identity).trans_lt (close.trans_eq paid), sourceCenteredArea,
      sourceCenteredEq, centeredClose.trans_eq paid⟩

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain the chart increment path with one edge restoring its pullback total.

The cached summary records the exact endpoint correction and its area contribution, together with a bound against the
centered source area. -/
structure Evaluation.RestoredChart (evaluated : Evaluation request source otherSource first second) where
  /-- The retained evaluated chart increments and their endpoint connector. -/ increments : evaluated.chart.Increments
  /-- The actual chart increment list with its endpoint-restoring edge. -/ path : List PrimitivePoint
  /-- The path is exactly the cached centered chart vector followed by its connector. -/ path_eq : path =
    (Path.CenteredPathIncrements.Sample.increments evaluated.chart.retained.area.evaluated.chart) ++
    [increments.connector]
  /-- The cached total and cumulative-area summary of this actual path. -/ summary : Path.PairedIncrementArea.Summary
    path
  /-- The summary total is the retained pullback increment. -/ total_eq : summary.totalValue = increments.pullback
  /-- The summary area is the centered chart area plus the connector contribution. -/ area_eq : summary.areaValue =
    evaluated.chart.retained.area.evaluated.chart.centeredArea + increments.connectorArea
  /-- The retained squared-error bound against the centered source area. -/ bound : Coordinate
  /-- The bound is the explicit sum of requested area error and paid connector error, multiplied by two. -/ bound_eq :
    bound = 2 * (requested +
    4 * (8 * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude request.chart.refined +
      1)) * (40 * (((requested / 4) / 4) / 2)))
  /-- The centered source area and retained summary area satisfy the cached bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceCenteredArea - summary.areaValue) ≤ bound

constructive_injectivity Evaluation.RestoredChart

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- Append the retained chart connector and reuse the cached area summary.

The resulting path has the exact pullback increment total and a paid source-area comparison, using the retained chart
vector without new root readings. -/
@[expose] def Evaluation.restoreChart (evaluated : Evaluation request source otherSource first second) :
  evaluated.RestoredChart := by
  let increments := evaluated.chart.increments
  let chart := evaluated.chart.retained.area.evaluated.chart
  have totalEq : increments.chart = Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments chart)
    := by
    rw [increments.chart_eq, Path.CenteredPathIncrements.Sample.increments_total chart, chart.centered_eq]
  let chartSummary : Path.PairedIncrementArea.Summary (Path.CenteredPathIncrements.Sample.increments chart) :=
    ⟨increments.chart, totalEq, chart.centeredArea, (Path.CenteredPathIncrements.Sample.increments_area chart).symm⟩
  let connector := Path.PairedIncrementArea.Summary.build [increments.connector]
  let summary := Path.PairedAreaBlocks.Summary.append chartSummary connector
  have connectorTotal : connector.totalValue = increments.connector := by
    apply congrArg₂ PrimitivePoint.mk <;> change _ + 0 = _ <;> exact add_zero _
  have connectorArea : connector.areaValue = 0 := by
    change edgeArea increments.connector PrimitivePoint.zero + 0 = 0
    simp only [edgeArea, PrimitivePoint.zero, mul_zero, zero_mul, sub_self, add_zero, -eq_self, -iff_self]
    rfl
  have total : summary.totalValue = increments.pullback := by
    change increments.chart.add connector.totalValue = _
    rw [connectorTotal]
    exact increments.restored
  have area : summary.areaValue = chart.centeredArea + increments.connectorArea := by
    change chart.centeredArea + connector.areaValue + edgeArea increments.chart connector.totalValue = _
    rw [connectorArea, connectorTotal, add_zero]
    unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation.Increments.connectorArea
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation.Increments.connector
    simp only [edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
    ring1
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.sourceCenteredArea - chart.centeredArea) increments.connectorArea).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
        evaluated.centered_bounded.le

          (CommonChartAreas.SourceAreaRequest.Evaluation.Increments.connectorArea_prepared
          evaluated.chart increments)) (by decide))
  have bounded : Data.Gaussian.Norm.Basic.normSq (evaluated.sourceCenteredArea - summary.areaValue) ≤
      2 * (requested + 4 * (8 * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
        request.chart.refined + 1)) * (40 * (((requested / 4) / 4) / 2))) := by
    rw [area, show evaluated.sourceCenteredArea - (chart.centeredArea + increments.connectorArea) =
      (evaluated.sourceCenteredArea - chart.centeredArea) - increments.connectorArea by ring1]
    exact estimate
  exact ⟨increments, (Path.CenteredPathIncrements.Sample.increments chart) ++ [increments.connector], rfl, summary,
    total, area,
    2 * (requested + 4 * (8 * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
      request.chart.refined + 1)) * (40 * (((requested / 4) / 4) / 2))), rfl, bounded⟩

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- The actual dyadic source increment area satisfies the restored chart's retained comparison bound. -/
theorem Evaluation.RestoredChart.source_bounded
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.RestoredChart) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
        depth interval.edge.left.parameter interval.edge.right.parameter) -
      restored.summary.areaValue) ≤ restored.bound := by
  rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area,
    ← Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero, ← evaluated.sourceArea_eq,
    ← evaluated.source_centered_decomposition]
  exact restored.bounded

open Purelib.Curves in
open Purelib.Integration in
/-- The restored chart total equals the actual dyadic pullback increment total. -/
theorem Evaluation.RestoredChart.pullback_total
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.RestoredChart) :
    restored.summary.totalValue = Path.PairedIncrementArea.total (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second)
        depth
      interval.edge.left.parameter interval.edge.right.parameter) := by
  rw [restored.total_eq, Path.Dyadic.DyadicPairedPrimitivePaths.increments_total]
  exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation.Increments.pullback_readback
    evaluated.chart restored.increments

open Purelib.Curves in
/-- Pair the two source endpoint differences on the actual common interval. -/
@[expose] def sourceIncrement : PrimitivePoint :=
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
    interval.edge.right.parameter).sub
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource
      interval.edge.left.parameter)

open Purelib.Approximation in
/-- Bound endpoint drift by the sum of the two quarter radii times the actual interval width squared. -/
@[expose] def incrementError : Coordinate :=
  (Rational.Geometric.Basic.quarterRadius request.first.scale index +
    Rational.Geometric.Basic.quarterRadius request.second.scale index) *
      (interval.edge.right.parameter - interval.edge.left.parameter)^2

open Purelib.Approximation in
open Purelib.Data in
/-- Every permitted stage pays the endpoint drift strictly within the source ribbon target. -/
theorem incrementError_paid (later : request.index ≤ index) :
    incrementError (index := index) request < sourceRibbonTarget requested := by
  have nonnegative : 0 ≤ request.driftScale := by
    rw [request.driftScale_eq]
    exact add_nonneg request.first.scale_nonnegative request.second.scale_nonnegative
  have after : request.driftIndex ≤ index :=
    (Data.Nat.Order.le_max_right _ _).trans (request.index_eq.symm.trans_le later)
  have drift := (quarterRadius_antitone nonnegative after).trans_lt
    (request.driftError_eq.symm.trans_lt request.drift_accurate)
  have width : (interval.edge.right.parameter - interval.edge.left.parameter)^2 ≤ 1 := by
    have upper := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2
      interval.edge.left.inside.1
    rw [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1)] at upper
    exact (Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct
      interval.ordered) upper 2).trans_eq (by decide)
  have scaleEq : Rational.Geometric.Basic.quarterRadius request.first.scale index +
      Rational.Geometric.Basic.quarterRadius request.second.scale index = Rational.Geometric.Basic.quarterRadius
        request.driftScale index := by
    rw [request.driftScale_eq]
    simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
    ring1
  unfold incrementError
  rw [scaleEq]
  exact ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width
    (Rational.Geometric.Basic.quarterRadius_nonneg nonnegative index)).trans_eq (mul_one _)).trans_lt drift

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound each component of source-to-pullback endpoint drift.

The original primitive origins cancel in endpoint differences; the estimate retains the actual common interval width and
both sample scales. -/
theorem Evaluation.source_increment_error
    (evaluated : Evaluation request source otherSource first second) (increments : evaluated.chart.Increments) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (((sourceIncrement (interval := interval) source
      otherSource).sub increments.pullback))
      (incrementError (index := index) request) := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation.Increments.pullback_readback
    evaluated.chart increments]
  have left := Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.drift_bound source first
    ⟨interval.first.lower, interval.ordered.trans interval.first.upper⟩
    ⟨interval.first.lower.trans interval.ordered, interval.first.upper⟩
  have right := Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.drift_bound otherSource second
    ⟨interval.second.lower, interval.ordered.trans interval.second.upper⟩
    ⟨interval.second.lower.trans interval.ordered, interval.second.upper⟩
  have firstNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg request.first.scale_nonnegative index
  have secondNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg request.second.scale_nonnegative index
  have leftPaid := left.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (le_add_of_nonneg_right secondNonnegative) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have rightPaid := right.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (le_add_of_nonneg_left firstNonnegative) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at leftPaid rightPaid
  constructor
  · have equal : ((sourceIncrement (interval := interval) source otherSource).sub
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
          interval.edge.right.parameter).sub
          (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first
            second interval.edge.left.parameter))).left =
        (Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue source
          interval.first.owner interval.edge.right.parameter -
          Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue first interval.edge.right.parameter) -
          (Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue source
            interval.first.owner interval.edge.left.parameter -
            Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue first interval.edge.left.parameter) := by
      dsimp only [sourceIncrement,
        Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues,
        PrimitivePoint.sub,
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue,
          Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue, recastCenteredEdge,
        Integration.PreparedConstantModels.PreparedEdge.point,
          Integration.PreparedConstantModels.PreparedEdge.localSegment,
        Integration.PreparedEdgeRecasting.recastPreparedEdge, -eq_self, -iff_self]
      ring1
    rw [equal]
    exact leftPaid
  · have equal : ((sourceIncrement (interval := interval) source otherSource).sub
        ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first second
          interval.edge.right.parameter).sub
          (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues first
            second interval.edge.left.parameter))).right =
        (Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue otherSource
          interval.second.owner interval.edge.right.parameter -
          Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue second interval.edge.right.parameter) -
          (Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue otherSource
            interval.second.owner interval.edge.left.parameter -
            Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue second interval.edge.left.parameter) := by
      dsimp only [sourceIncrement,
        Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.pullbackPolynomialValues,
        PrimitivePoint.sub,
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.sourceValue,
          Hyperelliptic.Charts.Reciprocal.Disk.ArcArea.Sample.capValue, recastCenteredEdge,
        Integration.PreparedConstantModels.PreparedEdge.point,
          Integration.PreparedConstantModels.PreparedEdge.localSegment,
        Integration.PreparedEdgeRecasting.recastPreparedEdge, -eq_self, -iff_self]
      ring1
    rw [equal]
    exact rightPaid

/-- A preparation-only bound on the pullback total from both source slopes and the ribbon target. -/
@[expose] def sourceTotalMagnitude : Coordinate :=
  2 * (data.sourceSlope + otherData.sourceSlope + 2 * sourceRibbonTarget requested)

section
open Purelib.Data
/-- The sum of the source increment's component squared norms is bounded by the two source slopes. -/
theorem sourceIncrement_magnitude :
    Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).left +
      Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).right ≤
        data.sourceSlope + otherData.sourceSlope := by
  have width : (interval.edge.right.parameter - interval.edge.left.parameter)^2 ≤ 1 := by
    have upper := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct interval.edge.right.inside.2
      interval.edge.left.inside.1
    rw [(show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1)] at upper
    exact (Rat.Fraction.Order.Arithmetic.pow_le_pow_direct (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct
      interval.ordered) upper 2).trans_eq (by decide)
  have left := (source.increment_bound interval.edge.left.inside interval.edge.right.inside).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width data.sourceSlope_nonnegative).trans_eq
      (mul_one _))
  have right := (otherSource.increment_bound interval.edge.left.inside interval.edge.right.inside).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width otherData.sourceSlope_nonnegative).trans_eq
      (mul_one _))
  exact Rat.Fraction.Order.Arithmetic.add_le_add_direct left right

/-- The restored pullback total satisfies the preparation-only component magnitude bound. -/
theorem Evaluation.RestoredChart.total_magnitude
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.RestoredChart) :
    Data.Gaussian.Norm.Basic.normSq restored.summary.totalValue.left + Data.Gaussian.Norm.Basic.normSq
      restored.summary.totalValue.right ≤
      sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) := by
  have error := Evaluation.source_increment_error request source otherSource first second evaluated restored.increments
  rw [← restored.total_eq] at error
  have paid := incrementError_paid request evaluated.later
  have scalar (a b : Gaussian) : Data.Gaussian.Norm.Basic.normSq b ≤ 2 * (Data.Gaussian.Norm.Basic.normSq a +
    Data.Gaussian.Norm.Basic.normSq (a - b)) := by
    have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two a (a - b)
    rw [show a - (a - b) = b by ring1] at estimate
    exact estimate
  have firstError := error.1
  have secondError := error.2
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at firstError secondError
  have first := (scalar (sourceIncrement (interval := interval) source otherSource).left
    restored.summary.totalValue.left).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      le_rfl (firstError.trans paid.le)) (by decide))
  have second := (scalar (sourceIncrement (interval := interval) source otherSource).right
    restored.summary.totalValue.right).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      le_rfl (secondError.trans paid.le)) (by decide))
  have sum := Rat.Fraction.Order.Arithmetic.add_le_add_direct first second
  have scale := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.add_le_add_direct (sourceIncrement_magnitude (interval := interval) source
      otherSource) (le_refl (2 * sourceRibbonTarget requested)))
    (by decide : (0 : Coordinate) ≤ 2)
  exact sum.trans ((by ring1 :
    2 * (Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).left +
      sourceRibbonTarget requested) +
      2 * (Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).right +
        sourceRibbonTarget requested) =
    2 * (Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).left +
      Data.Gaussian.Norm.Basic.normSq (sourceIncrement (interval := interval) source otherSource).right + 2 *
        sourceRibbonTarget requested)).trans_le scale)

end

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain a second endpoint correction restoring the exact source increment total.

The first restored chart, drift payment, appended connector and cached summary remain linked by exact equations. The new
area comparison includes the connector's contribution. -/
structure Evaluation.SourceRestoredChart (evaluated : Evaluation request source otherSource first second) where
  /-- The first restored chart with exact pullback total. -/ retained : evaluated.RestoredChart
  /-- The cached paired source endpoint increment. -/ sourceTotal : PrimitivePoint
  /-- The cached source total is the actual source endpoint increment. -/ sourceTotal_eq : sourceTotal = sourceIncrement
    (interval := interval) source otherSource
  /-- The retained edge correcting the pullback total to the source total. -/ connector : PrimitivePoint
  /-- The connector is the source total minus the retained pullback total. -/ connector_eq : connector = sourceTotal.sub
    retained.summary.totalValue
  /-- The cached endpoint drift bound. -/ error : Coordinate
  /-- The drift bound equals the request's actual increment error. -/ error_eq : error = incrementError (index := index)
    request
  /-- The endpoint drift is strictly below the source ribbon target. -/ error_paid : error < sourceRibbonTarget
    requested
  /-- Each connector component has squared norm at most the cached drift error. -/ connector_bounded :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (connector) error
  /-- The actual twice-restored chart increment list. -/ path : List PrimitivePoint
  /-- The path is the first restored path followed by the source connector. -/ path_eq : path = retained.path ++
    [connector]
  /-- The cached total and cumulative-area summary of the twice-restored path. -/ summary :
    Path.PairedIncrementArea.Summary path
  /-- The summary total is exactly the cached source total. -/ total_eq : summary.totalValue = sourceTotal
  /-- The cached area contribution of the source-restoring edge. -/ connectorArea : Gaussian
  /-- The connector area is the edge area from the retained pullback total to the source total. -/ connectorArea_eq :
    connectorArea = edgeArea retained.summary.totalValue sourceTotal
  /-- The new summary area is the retained chart area plus the cached connector area. -/ area_eq : summary.areaValue =
    retained.summary.areaValue + connectorArea
  /-- The retained complete source-area comparison bound. -/ bound : Coordinate
  /-- The bound is twice the retained chart bound plus the magnitude-weighted source-connector error. -/ bound_eq :
    bound = 2 * (retained.bound + 4 *
    sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) * error)
  /-- The centered source area and twice-restored summary area satisfy the retained bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceCenteredArea - summary.areaValue) ≤ bound

constructive_injectivity Evaluation.SourceRestoredChart

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Append a paid source-endpoint correction to the retained pullback chart.

The construction reuses its existing summary, computes the source drift once and retains the exact source total and the
enlarged area-error bound. -/
@[expose] def Evaluation.restoreSourceChart (evaluated : Evaluation request source otherSource first second) :
  evaluated.SourceRestoredChart := by
  let retained := evaluated.restoreChart
  let sourceTotal := sourceIncrement (interval := interval) source otherSource
  let connector := sourceTotal.sub retained.summary.totalValue
  let error := incrementError (index := index) request
  have connectorBound : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (connector) error := by
    change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (((sourceIncrement (interval := interval) source
      otherSource).sub retained.summary.totalValue)) _
    rw [retained.total_eq]
    exact Evaluation.source_increment_error request source otherSource first second evaluated retained.increments
  let connectorSummary := Path.PairedIncrementArea.Summary.build [connector]
  let summary := Path.PairedAreaBlocks.Summary.append retained.summary connectorSummary
  have connectorTotal : connectorSummary.totalValue = connector := by
    apply congrArg₂ PrimitivePoint.mk <;> change _ + 0 = _ <;> exact add_zero _
  have connectorZero : connectorSummary.areaValue = 0 := by
    change edgeArea connector PrimitivePoint.zero + 0 = 0
    simp only [edgeArea, PrimitivePoint.zero, mul_zero, zero_mul, sub_self, add_zero, -eq_self, -iff_self]
    rfl
  have total : summary.totalValue = sourceTotal := by
    change retained.summary.totalValue.add connectorSummary.totalValue = _
    rw [connectorTotal]
    apply congrArg₂ PrimitivePoint.mk <;> dsimp only [connector, sourceTotal, sourceIncrement, PrimitivePoint.add,
      PrimitivePoint.sub, -eq_self, -iff_self] <;> ring1
  let connectorArea := edgeArea retained.summary.totalValue sourceTotal
  have connectorAreaEq : connectorArea = edgeArea retained.summary.totalValue connector := by
    dsimp only [connectorArea, connector, edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
    ring1
  have area : summary.areaValue = retained.summary.areaValue + connectorArea := by
    change retained.summary.areaValue + connectorSummary.areaValue +
      edgeArea retained.summary.totalValue connectorSummary.totalValue = _
    rw [connectorZero, connectorTotal, add_zero, ← connectorAreaEq]
  have magnitudeBound := Evaluation.RestoredChart.total_magnitude request source otherSource first second evaluated
    retained
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at magnitudeBound
  have magnitude : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (retained.summary.totalValue)
      (sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested)) :=
    ⟨(le_add_of_nonneg_right (Gaussian.Basic.Canonical.normSq_nonneg _)).trans magnitudeBound,
      (le_add_of_nonneg_left (Gaussian.Basic.Canonical.normSq_nonneg _)).trans magnitudeBound⟩
  have connectorPaid := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound magnitude connectorBound
  rw [← connectorAreaEq, ← Gaussian.Norm.Basic.normSq_eq_canonical] at connectorPaid
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (evaluated.sourceCenteredArea - retained.summary.areaValue) connectorArea).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
        retained.bounded connectorPaid) (by decide))
  have bounded : Data.Gaussian.Norm.Basic.normSq (evaluated.sourceCenteredArea - summary.areaValue) ≤
      2 * (retained.bound + 4 * sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) *
        error) := by
    rw [area, show evaluated.sourceCenteredArea - (retained.summary.areaValue + connectorArea) =
      (evaluated.sourceCenteredArea - retained.summary.areaValue) - connectorArea by ring1]
    exact estimate
  exact ⟨retained, sourceTotal, rfl, connector, rfl, error, rfl, incrementError_paid request evaluated.later,
    connectorBound,
    retained.path ++ [connector], rfl, summary, total, connectorArea, rfl, area,
    2 * (retained.bound + 4 * sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) *
      error), rfl, bounded⟩

open Purelib.Curves in
open Purelib.Integration in
/-- The twice-restored chart total equals the actual dyadic source increment total. -/
theorem Evaluation.SourceRestoredChart.source_total
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.SourceRestoredChart) :
    restored.summary.totalValue = Path.PairedIncrementArea.total (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
        depth interval.edge.left.parameter interval.edge.right.parameter) := by
  rw [restored.total_eq, restored.sourceTotal_eq, Path.Dyadic.DyadicPairedPrimitivePaths.increments_total]
  rfl

open Purelib.Data in
/-- Replacing the actual drift by the ribbon target bounds the retained restoration error. -/
theorem Evaluation.SourceRestoredChart.bound_prepared
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.SourceRestoredChart) :
    restored.bound ≤ 2 * (restored.retained.bound + 4 *
      sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) * sourceRibbonTarget
        requested) := by
  have driftPositive : 0 < sourceRibbonTarget requested :=
    Rat.Fraction.Order.Field.div_pos_direct (Rat.Fraction.Order.Field.div_pos_direct request.chart.positive (by decide))
      (by decide)
  have magnitudeNonnegative : 0 ≤ sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested)
    :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg data.sourceSlope_nonnegative
      otherData.sourceSlope_nonnegative)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) driftPositive.le))
  rw [restored.bound_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.add_le_add_direct le_rfl
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct restored.error_paid.le
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative))) (by decide)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- The actual source increment area satisfies the twice-restored chart's cached bound. -/
theorem Evaluation.SourceRestoredChart.source_bounded
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.SourceRestoredChart) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
        depth interval.edge.left.parameter interval.edge.right.parameter) -
      restored.summary.areaValue) ≤ restored.bound := by
  rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area,
    ← Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero, ← evaluated.sourceArea_eq,
    ← evaluated.source_centered_decomposition]
  exact restored.bounded

open Purelib.Curves in
/-- The preparation-only coefficient paying both endpoint corrections linearly in the requested target. -/
@[expose] def restorationRate (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor) : Coordinate :=
  4 + 4 * (4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1))
    * 40) +
    16 * (data.sourceSlope + otherData.sourceSlope + 2)

open Purelib.Curves in
open Purelib.Data in
/-- The prepared restoration coefficient is nonnegative. -/
theorem restorationRate_nonnegative (prepared :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor) :
    0 ≤ restorationRate prepared := by
  exact add_nonneg (add_nonneg (by decide) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative
        prepared) (by decide)))) (by decide +kernel))))
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (add_nonneg (add_nonneg data.sourceSlope_nonnegative otherData.sourceSlope_nonnegative) (by decide)))

open Purelib.Data in
/-- Dividing a nonnegative rational by a divisor at least one cannot increase it. -/
private theorem divide_le_self {value divisor : Coordinate} (nonnegative : 0 ≤ value) (oneLe : 1 ≤ divisor) :
    value / divisor ≤ value := by
  have bound := Rat.Fraction.Order.Field.div_le_div_of_nonneg_left_direct nonnegative (by decide : (0 : Coordinate) < 1)
    oneLe
  exact bound.trans_eq (by change value * 1 = value; exact mul_one _)

open Purelib.Curves in
open Purelib.Data in
/-- Pay the complete restoration error linearly in a target at most one.

For a positive target bounded by one, the retained chart bound is at most the preparation-only restoration coefficient
times that target. -/
theorem Evaluation.SourceRestoredChart.bound_linear
    (evaluated : Evaluation request source otherSource first second) (restored : evaluated.SourceRestoredChart)
    (positive : 0 < requested) (small : requested ≤ 1) :
    restored.bound ≤ restorationRate prepared * requested := by
  have quarterPositive := Rat.Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Coordinate) < 4)
  have sixteenthPositive := Rat.Fraction.Order.Field.div_pos_direct quarterPositive (by decide : (0 : Coordinate) < 4)
  have firstLe := divide_le_self positive.le (by decide : (1 : Coordinate) ≤ 4)
  have secondLe := (divide_le_self quarterPositive.le (by decide : (1 : Coordinate) ≤ 4)).trans firstLe
  have sourceLe : sourceRibbonTarget requested ≤ requested :=
    (divide_le_self sixteenthPositive.le (by decide : (1 : Coordinate) ≤ 4)).trans secondLe
  have chartLe := (divide_le_self sixteenthPositive.le (by decide : (1 : Coordinate) ≤ 2)).trans secondLe
  have sourceNonnegative : 0 ≤ sourceRibbonTarget requested := (Rat.Fraction.Order.Field.div_pos_direct
    sixteenthPositive (by decide)).le
  have magnitudeEq : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
    request.chart.refined = (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
    prepared) := by
    rw [show request.chart.refined = Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget
      prepared request.chart.budget.tolerance request.chart.budget.positive
      from request.chart.refined_eq]
    exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget_magnitude prepared _ _
  have coefficientNonnegative : 0 ≤ 4 * (8 *
    ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1)) * 40 :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative
        prepared) (by decide)))) (by decide +kernel)
  have retained : restored.retained.bound ≤
      2 * (requested + (4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude
        prepared) + 1)) * 40) * requested) := by
    rw [restored.retained.bound_eq, magnitudeEq,
      show 4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1))
        * (40 * (((requested / 4) / 4) / 2)) =
        (4 * (8 * ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude prepared) + 1)) *
          40) * (((requested / 4) / 4) / 2) by ring1]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct chartLe coefficientNonnegative)) (by decide)
  have magnitudeLe : sourceTotalMagnitude (data := data) (otherData := otherData) (requested := requested) ≤
      2 * (data.sourceSlope + otherData.sourceSlope + 2) := by
    unfold sourceTotalMagnitude
    have inner := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (sourceLe.trans small) (by
        decide : (0 : Coordinate) ≤ 2)
    rw [mul_one] at inner
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct le_rfl inner) (by decide)
  have sourceCoefficient : 0 ≤ 4 * (2 * (data.sourceSlope + otherData.sourceSlope + 2)) :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide)
      (add_nonneg (add_nonneg data.sourceSlope_nonnegative otherData.sourceSlope_nonnegative) (by decide)))
  have sourceCost := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct magnitudeLe (by decide : (0 : Coordinate) ≤ 4))
      sourceNonnegative).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sourceLe sourceCoefficient)
  have bound := (Evaluation.SourceRestoredChart.bound_prepared request source otherSource first second evaluated
    restored).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      retained sourceCost) (by decide : (0 : Coordinate) ≤ 2))
  exact bound.trans_eq (by unfold restorationRate; ring1)

open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain a finite path replacement with the exact original increment total.

Both paths have cached summaries, and the retained bound compares their complete cumulative areas, including all
internal cross terms. -/
structure PathReplacement (original : List PrimitivePoint) where
  /-- The cached summary of the original increment list. -/ source : Path.PairedIncrementArea.Summary original
  /-- The actual replacement increment list. -/ path : List PrimitivePoint
  /-- The cached summary of the replacement increment list. -/ chart : Path.PairedIncrementArea.Summary path
  /-- The replacement and original cached summaries have exactly the same total. -/ total_eq : chart.totalValue =
    source.totalValue
  /-- The retained squared-error bound on complete cumulative areas. -/ bound : Coordinate
  /-- The two cached areas satisfy the retained squared-error bound. -/ bounded : Data.Gaussian.Norm.Basic.normSq
    (source.areaValue - chart.areaValue) ≤ bound

constructive_injectivity PathReplacement

open Purelib.Integration in
open Purelib.Data in
/-- Concatenate two retained path replacements and their cached summaries.

Exact equality of the two increment totals cancels the cross-area discrepancy. The combined squared-error bound is twice
the sum of the component bounds. -/
@[expose] def PathReplacement.append {left right : List PrimitivePoint}
    (first : PathReplacement left) (second : PathReplacement right) : PathReplacement (left ++ right) := by
  let source := Path.PairedAreaBlocks.Summary.append first.source second.source
  let chart := Path.PairedAreaBlocks.Summary.append first.chart second.chart
  have total : chart.totalValue = source.totalValue :=
    congrArg₂ PrimitivePoint.add first.total_eq second.total_eq
  have area : source.areaValue - chart.areaValue =
      (first.source.areaValue - first.chart.areaValue) + (second.source.areaValue - second.chart.areaValue) := by
    change first.source.areaValue + second.source.areaValue + edgeArea first.source.totalValue second.source.totalValue
      -
      (first.chart.areaValue + second.chart.areaValue + edgeArea first.chart.totalValue second.chart.totalValue) = _
    rw [first.total_eq, second.total_eq]
    ring1
  have bounded := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      first.bounded second.bounded) (by decide))
  exact ⟨source, first.path ++ second.path, chart, total, 2 * (first.bound + second.bound),
    (congrArg Data.Gaussian.Norm.Basic.normSq area).trans_le bounded⟩

open Purelib.Integration in
/-- Transport the original path along an exact list equality while retaining the replacement and its summary. -/
@[expose] def PathReplacement.readback {left right : List PrimitivePoint} (equal : left = right)
    (replacement : PathReplacement left) : PathReplacement right :=
  ⟨⟨replacement.source.totalValue, replacement.source.total_eq.trans (congrArg Path.PairedIncrementArea.total equal),
      replacement.source.areaValue, replacement.source.area_eq.trans (congrArg Path.PairedIncrementArea.area equal)⟩,
    replacement.path, replacement.chart, replacement.total_eq, replacement.bound, replacement.bounded⟩

open Purelib.Integration in
open Purelib.Data in
/-- Join an ordered finite bank of replacements by cached concatenation.

The empty bank gives the empty path; each successor preserves occurrence order and uses the same two-summand area bound
as append. -/
@[expose] def PathReplacement.join : {n : Nat} → (paths : Fin n → List PrimitivePoint) →
    ((i : Fin n) → PathReplacement (paths i)) → PathReplacement (List.ofFn paths).flatten
  | 0, _, _ => ⟨Path.PairedIncrementArea.Summary.build [], [], Path.PairedIncrementArea.Summary.build [],
      rfl, 0, by change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 0; decide⟩
  | n + 1, paths, entries => by
    exact PathReplacement.readback (by rw [List.OfFn.Basic.ofFn_succ, List.flatten_cons])
      ((entries 0).append (join (fun i : Fin n => paths i.succ) (fun i => entries i.succ)))

/-- The finite concatenation coefficient, zero for an empty bank and twice one plus the previous coefficient otherwise.
-/
@[expose] def PathReplacement.joinRate : Nat → Coordinate
  | 0 => 0
  | n + 1 => 2 * (1 + joinRate n)

section
open Purelib.Data
/-- The finite concatenation coefficient is nonnegative. -/
theorem PathReplacement.joinRate_nonnegative (n : Nat) : 0 ≤ joinRate n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide) ih)

/-- A common allowance bounds the joined replacement error by the concatenation coefficient times that allowance. -/
theorem PathReplacement.join_bound {n : Nat} (paths : Fin n → List PrimitivePoint)
    (entries : (i : Fin n) → PathReplacement (paths i)) {allowance : Coordinate}
    (bounded : ∀ i, (entries i).bound ≤ allowance) :
    (join paths entries).bound ≤ joinRate n * allowance := by
  induction n with
  | zero => change 0 ≤ 0 * allowance; rw [zero_mul]
  | succ n ih =>
    change 2 * ((entries 0).bound + (join (fun i : Fin n => paths i.succ) (fun i => entries i.succ)).bound) ≤ _
    exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct (bounded 0)
      (ih _ _ (fun i => bounded i.succ))) (by decide)).trans_eq (by
        change 2 * (allowance + joinRate n * allowance) = 2 * (1 + joinRate n) * allowance
        ring1)

end

open Purelib.Approximation in
set_option genInjectivity false in
/-- Retain a positive allowance paying both count and concatenation losses.

The allowance is the minimum of the per-term count payment and the weighted join payment, with strict certificates for
both products. -/
structure PathReplacement.JoinBudget (count : Nat) (target : Coordinate) where
  /-- The cached finite concatenation coefficient. -/ rate : Coordinate
  /-- The cached coefficient equals the recursive join rate for this count. -/ rate_eq : rate = joinRate count
  /-- The positive per-replacement allowance paying both finite losses. -/ allowance : Coordinate
  /-- The allowance is exactly the minimum of the count payment and weighted half-target payment. -/ allowance_eq :
    allowance = min (Rational.Budget.Aggregate.perTerm target count)
    (Rational.Budget.Weighted.allowance (target / 2) rate)
  /-- The retained allowance is strictly positive. -/ positive : 0 < allowance
  /-- The count squared times the allowance is strictly below the target. -/ count_paid : (count : Coordinate) * ((count
    : Coordinate) * allowance) < target
  /-- The concatenation coefficient times the allowance is strictly below the target. -/ join_paid : rate * allowance <
    target

constructive_injectivity PathReplacement.JoinBudget

open Purelib.Approximation in
open Purelib.Data in
/-- Compute a positive allowance paying both finite join losses.

The construction takes the minimum of explicit count and weighted allowances and also handles an empty bank. -/
@[expose] def PathReplacement.JoinBudget.build (count : Nat) (target : Coordinate) (positive : 0 < target) : JoinBudget
  count target := by
  let rate := joinRate count
  have nonnegative := joinRate_nonnegative count
  have halfPositive := Rat.Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Coordinate) < 2)
  let allowance := min (Rational.Budget.Aggregate.perTerm target count) (Rational.Budget.Weighted.allowance (target / 2)
    rate)
  have countNonnegative : (0 : Coordinate) ≤ (count : Coordinate) := Rat.Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le count)
  have countPaid := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left
      (Rational.Budget.Aggregate.perTerm target count)
      (Rational.Budget.Weighted.allowance (target / 2) rate)) countNonnegative) countNonnegative).trans_lt
      (Rational.Budget.Aggregate.count_mul_perTerm_lt positive count)
  have halfEq : target / 2 + target / 2 = target :=
    (by ring1 : target / 2 + target / 2 = target / 2 * 2).trans (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  exact ⟨rate, rfl, allowance, rfl,
    Fraction.Order.Basic.lt_min (Rational.Budget.Aggregate.perTerm_positive positive count)
      (Rational.Budget.Weighted.allowance_positive halfPositive nonnegative),
    countPaid, ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      nonnegative).trans
      (Rational.Budget.Weighted.mul_allowance_le halfPositive.le nonnegative)).trans_lt halfLess⟩

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
/-- Retain the actual dyadic source path and its twice-restored chart replacement.

The cached centered source area and exact source total supply the original summary, and the restored chart is
constructed once and reused. -/
@[expose] def Evaluation.sourceReplacement (evaluated : Evaluation request source otherSource first second) :
    PathReplacement (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
      depth interval.edge.left.parameter interval.edge.right.parameter) := by
  let restored := evaluated.restoreSourceChart
  let sourceSummary : Path.PairedIncrementArea.Summary (Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues source otherSource)
        depth interval.edge.left.parameter interval.edge.right.parameter) :=
    ⟨restored.sourceTotal, restored.total_eq.symm.trans
      (Evaluation.SourceRestoredChart.source_total request source otherSource first second evaluated restored),
      evaluated.sourceCenteredArea, by
        rw [Path.Dyadic.DyadicPairedPrimitivePaths.increments_area, ←
          Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero,
          ← evaluated.sourceArea_eq, ← evaluated.source_centered_decomposition]⟩
  exact ⟨sourceSummary, restored.path, restored.summary, restored.total_eq, restored.bound, restored.bounded⟩

/-- For a positive target at most one, the source replacement bound is at most the prepared restoration rate times that
target. -/
theorem Evaluation.sourceReplacement_bound
    (evaluated : Evaluation request source otherSource first second) (positive : 0 < requested) (small : requested ≤ 1)
      :
    evaluated.sourceReplacement.bound ≤ restorationRate prepared * requested :=
  Evaluation.SourceRestoredChart.bound_linear request source otherSource first second evaluated
    evaluated.restoreSourceChart positive small

end SourceComparisonRequest
end Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
