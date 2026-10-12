module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartPolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedPoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Tactic.Ring

public section

/-!
# Areas of the separate retained cap-side polygons

The intermediate request fixes all integration children, prepares their chart
vertices, and selects one common polynomial stage. Evaluation compares the
whole path of negative cap-primitive increments with the positive reciprocal
integrator. Both internal areas and the polygon of parent totals are paid.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests.Bank (Requests Samples)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea (PolynomialRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea.Bank (areaSlopeMaximum areaSlopeMaximum_nonnegative
  areaBlocks)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests (row_error_le)

/-- The original chart total is bounded by its paid source discrepancy and retained source slope. -/
private theorem chart_total_bound {chart source : InverseRootPolynomial.Gaussian} {target slope :
  InverseRootPolynomial.Coordinate}
    (targetNonnegative : 0 ≤ target) (slopeNonnegative : 0 ≤ slope)
    (error : Data.Gaussian.Norm.Basic.normSq (chart - source) ≤ target) (bounded :
      Data.Gaussian.Norm.Basic.normSq source ≤ 4 * (slope + 3 * target)) :
    Data.Gaussian.Norm.Basic.normSq chart ≤ 10 * (slope + 3 * target) := by
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two (chart - source) source
  rw [sub_add_cancel] at estimate
  apply estimate.trans
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add error bounded) (by decide)).trans
  exact (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
      slopeNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
      targetNonnegative))).trans_eq (by ring1)

/-- The original internal and cross-term area costs fit the retained finite parent-count budget. -/
public theorem area_cost (count target slope : InverseRootPolynomial.Coordinate) (countNonnegative : 0 ≤ count)
    (targetNonnegative : 0 ≤ target) (slopeNonnegative : 0 ≤ slope) :
    2 * (count ^ 2 * (target * (slope + 3 * target)) + 16 * count ^ 4 * target * (10 * (slope + 3 * target))) ≤
      512 * (count ^ 2 + count ^ 4) * target * (slope + 3 * target) := by
  have coefficients := add_le_add
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (2 : InverseRootPolynomial.Coordinate) ≤ 512)
      (Fraction.Order.Arithmetic.sq_nonneg_direct count))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide +kernel : (320 : InverseRootPolynomial.Coordinate) ≤ 512)
      (Fraction.Order.Arithmetic.pow_nonneg_direct countNonnegative 4))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficients targetNonnegative)
    (add_nonneg slopeNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3) targetNonnegative))
  calc
    _ = (2 * count ^ 2 + 320 * count ^ 4) * target * (slope + 3 * target) := by ring1
    _ ≤ (512 * count ^ 2 + 512 * count ^ 4) * target * (slope + 3 * target) := scaled
    _ = _ := by ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Bank

/-- Child-chart area requests indexed by the original retained cap-parent request bank. -/
@[expose] public def FineRequests : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → Bank.Requests bank target floor →
      InverseRootPolynomial.Coordinate → Type 3
  | _, .nil, _, _, _, _ => PUnit
  | _, .cons _ _, target, _, requests, slope =>
      FineCharts.AreaRequest requests.1 target (target * (slope + 3 * target)) ×
        FineRequests requests.2 slope

namespace FineRequests

/-- Request each original retained parent's child-chart total and area bounds using the common slope ceiling. -/
@[expose] public def build : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target : InverseRootPolynomial.Coordinate} → {floor : Nat} → (requests : Bank.Requests bank target floor) →
    (slope : InverseRootPolynomial.Coordinate) → 0 ≤ slope →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope
  | _, .nil, _, _, _, _, _ => ⟨⟩
  | _, .cons _ _, _, _, requests, slope, nonnegative =>
      ⟨AreaRequest.build requests.1 _ _ requests.1.positive
        (Fraction.Order.Arithmetic.mul_pos_direct requests.1.positive
          (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative
            (Fraction.Order.Arithmetic.mul_pos_direct (by decide) requests.1.positive))),
       build requests.2 slope
         nonnegative⟩

/-- Compute a common polynomial stage above every original retained fine chart request. -/
@[expose] public def stage : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope → Nat
  | _, .nil, _, _, floor, _, _ => floor
  | _, .cons _ _, _, _, _, _, requests => max requests.1.index
    (stage requests.2)

end FineRequests

/-- Cached original fine chart evaluations indexed by their actual parent samples and requests. -/
@[expose] public def FineSamples : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    (samples : Bank.Samples requests capSample) → FineRequests
      requests slope → Type 3
  | _, .nil, _, _, _, _, _, _ => PUnit
  | _, .cons _ _, _, _, _, _, samples, requests =>
      AreaRequest.Evaluation requests.1 samples.1 ×
        FineSamples samples.2 requests.2

namespace FineSamples

/-- Evaluate every original retained fine-chart request on its actual cached parent sample at the common polynomial
stage. -/
@[expose] public def build : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    (samples : Bank.Samples requests capSample) → (fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope) →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage fine ≤ index →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine
  | _, .nil, _, _, _, _, _, _, _ => ⟨⟩
  | _, .cons _ _, _, _, _, _, samples, fine, later =>
      ⟨fine.1.evaluate samples.1 ((Purelib.Data.Nat.Order.le_max_left _ _).trans later),
        build samples.2 fine.2
        ((Purelib.Data.Nat.Order.le_max_right _ _).trans later)⟩

/-- Operational coordinate joins between the actual retained endpoints of consecutive original fine polygons. -/
@[expose] public def EndpointJoinData : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank
  cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine → Type
  | [], .nil, _, _, _, _, _, _, _ => PUnit
  | [_], .cons _ .nil, _, _, _, _, _, _, _ => PUnit
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts =>
      RootCoordinates.Overlap.Join charts.1.last.request.prepared.coordinates
        charts.2.1.first.request.prepared.coordinates ×
        EndpointJoinData charts.2

set_option genInjectivity false in
/-- Operational joins belong to the actual retained endpoints of the fine polygons. The endpoint records certify their
positions in those polygons. -/
structure EndpointJoins {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap differential
  count parents}
    {target slope : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} (charts :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) where
  /-- The cached coordinate joins on these exact original fine polygon endpoints. -/ retained :
    EndpointJoinData charts

constructive_injectivity EndpointJoins

namespace EndpointJoins

/-- Transfer the original cached coarse-parent coordinate joins to the exact retained fine polygon endpoints. -/
@[expose] public def buildData : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential
  count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → Bank.CoordinateLinks
      bank → Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoinData charts
  | [], .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | [_], .cons _ .nil, _, _, _, _, _, _, _, _ => ⟨⟩
  | _ :: _ :: _, .cons _ (.cons _ _), _, _, _, _, _, _, charts, coarse =>
      ⟨ParentBoundary.join coarse.head charts.1.last.request charts.2.1.first.request rfl rfl,
        buildData charts.2
          coarse.tail⟩

/-- Package the transferred original coarse-parent joins on the exact retained fine polygon endpoints. -/
@[expose] public def build {parents : List (PathCover.Parent curve differential)} {bank : PathCover.Bank cap
  differential count parents}
    {target slope : InverseRootPolynomial.Coordinate} {floor : Nat} {requests : Bank.Requests bank target floor}
    {samples : Bank.Samples requests capSample} {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) (coarse :
      Bank.CoordinateLinks bank) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins
      charts :=
  ⟨buildData charts coarse⟩

/-- Read the first cached coordinate join between actual original fine polygon endpoints. -/
@[expose] public def head {parent next : PathCover.Parent curve differential} {parents : List (PathCover.Parent curve
  differential)}
    {data : PathCover.ParentData cap differential count parent} {nextData : PathCover.ParentData cap differential count
      next}
    {remaining : PathCover.Bank cap differential count parents} {target slope : InverseRootPolynomial.Coordinate} {floor
      : Nat}
    {requests : Bank.Requests (.cons data (.cons nextData remaining)) target floor}
    {samples : Bank.Samples requests capSample} {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    {charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine} (joins :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins charts) :
    RootCoordinates.Overlap.Join charts.1.last.request.prepared.coordinates
      charts.2.1.first.request.prepared.coordinates :=
  joins.retained.1

/-- Read the cached tail joins without rebuilding any original endpoint owner. -/
@[expose] public def tail {parent next : PathCover.Parent curve differential} {parents : List (PathCover.Parent curve
  differential)}
    {data : PathCover.ParentData cap differential count parent} {nextData : PathCover.ParentData cap differential count
      next}
    {remaining : PathCover.Bank cap differential count parents} {target slope : InverseRootPolynomial.Coordinate} {floor
      : Nat}
    {requests : Bank.Requests (.cons data (.cons nextData remaining)) target floor}
    {samples : Bank.Samples requests capSample} {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope}
    {charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine} (joins :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins charts) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins charts.2 :=
  ⟨joins.retained.2⟩

end EndpointJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples in
/-- Read the original chart and polynomial increment paths in their actual retained parent order. -/
@[expose] public def pairs : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine → List (List
      InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, .nil, _, _, _, _, _, _, _ => []
  | _, .cons _ _, _, _, _, _, _, _, samples =>
      (samples.1.pairs.map Prod.fst, samples.1.pairs.map Prod.snd) :: pairs samples.2

/-- Compose the retained parent summaries without replaying their increments. -/
@[expose] public def summary : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) →
      IncrementArea.Summary (charts.pairs.map Prod.fst).flatten
  | _, .nil, _, _, _, _, _, _, _ => IncrementArea.Summary.build []
  | _, .cons _ _, _, _, _, _, _, _, charts => charts.1.chart.append
    (summary charts.2)

/-- The retained path-pair list contains exactly one entry per original parent. -/
theorem pairs_length : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential
  count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → charts.pairs.length
      = parents.length
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, _, _, _, charts => congrArg Nat.succ
    (pairs_length charts.2)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
/-- The retained polynomial paths equal the exact original source projection of the prepared area blocks. -/
theorem pairs_source : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential
  count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → charts.pairs.map
      Prod.snd = (Bank.areaBlocks samples).map Prod.fst
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, _, _, _, charts => by
      rewrite [pairs, Bank.areaBlocks, List.map_cons, charts.1.source_eq,
        pairs_source charts.2,
        List.map_cons]
      exact Eq.refl _

/-- Read the cached original fine chart polygon of every retained parent. -/
@[expose] public def polygons : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine → List (FineCharts.Polygon
      capSample)
  | _, .nil, _, _, _, _, _, _, _ => []
  | _, .cons _ _, _, _, _, _, _, _, charts => charts.1.polygon :: polygons charts.2

end

/-- There is one actual retained fine chart polygon per original parent. -/
theorem polygons_length : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) →
      charts.polygons.length = parents.length
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, _, _, _, charts => congrArg Nat.succ
    (polygons_length charts.2)

/-- The retained polygon areas read back the actual original chart path areas. -/
theorem polygons_areas : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → charts.polygons.map
      Polygon.area = charts.pairs.map (fun pair => IncrementArea.pathArea pair.1)
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, _, _, _, charts => by
      change charts.1.chart.area :: _ = IncrementArea.pathArea (charts.1.pairs.map Prod.fst) :: _
      rw [charts.1.chart.area_eq]
      exact congrArg (List.cons _)
        (polygons_areas charts.2)

/-- The retained polygon totals read back the actual original chart increment sums. -/
theorem polygons_totals : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap
  differential count parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → charts.polygons.map
      Polygon.total = charts.pairs.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1)
  | _, .nil, _, _, _, _, _, _, _ => rfl
  | _, .cons _ _, _, _, _, _, _, _, charts => by
      change charts.1.chart.total :: _ = Data.Gaussian.Norm.Sum.Basic.gaussianSum (charts.1.pairs.map Prod.fst) ::
        _
      rw [charts.1.chart.total_eq]
      exact congrArg (List.cons _)
        (polygons_totals charts.2)

/-- Every original parent path pair satisfies the paid internal-area, total-error and both total-magnitude ceilings. -/
theorem bounds : {parents : List (PathCover.Parent curve differential)} → {bank : PathCover.Bank cap differential count
  parents} →
    {target slope : InverseRootPolynomial.Coordinate} → {floor : Nat} → {requests : Bank.Requests bank target floor} →
    {samples : Bank.Samples requests capSample} → {fine :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests requests slope} →
    (charts : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples samples fine) → Requests.index
      requests ≤ index → Bank.areaSlopeMaximum bank ≤ slope →
    ∀ pair ∈ charts.pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤ target
        * (slope + 3 * target) ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ target ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 10 * (slope + 3
        * target) ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 10 * (slope + 3
        * target)
  | _, .nil, _, _, _, _, _, _, _, _, _, _, member => by cases member
  | _, .cons _ _, target, slope, _, requests, samples, _, charts, later, upper, pair, member => by
      have slopeNonnegative := (Bank.areaSlopeMaximum_nonnegative _).trans upper
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · have sourceBound : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (charts.1.pairs.map Prod.snd)) ≤ 4 * (slope + 3 * target) := by
          rw [charts.1.source_eq]
          exact ((ReciprocalCapPreparedPrimitives.Sample.area_bounds samples.1) ((Purelib.Data.Nat.Order.le_max_left _
            _).trans later)).2.2.1.trans
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add ((Fraction.Order.Basic.le_max_left _ _).trans upper) le_rfl) (by decide))
        have areaBound := charts.1.area_close.le
        rw [charts.1.chart.area_eq, charts.1.polynomial.area_eq] at areaBound
        have totalBound := charts.1.total_close.le
        rw [charts.1.chart.total_eq, charts.1.polynomial.total_eq] at totalBound
        refine ⟨areaBound, totalBound, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.chart_total_bound
          requests.1.positive.le slopeNonnegative totalBound sourceBound, ?_⟩
        exact sourceBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
            decide : (4 : InverseRootPolynomial.Coordinate) ≤ 10)
          (add_nonneg slopeNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            requests.1.positive.le)))
      · exact bounds charts.2
          ((Purelib.Data.Nat.Order.le_max_right _ _).trans later) ((Fraction.Order.Basic.le_max_right _ _).trans upper)
          pair member

end FineSamples
end Bank

variable {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {path : Polynomial.Geometry.ClearPath
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) collar.box first last}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval first)}

set_option genInjectivity false in
/-- A shared polynomial-stage request for separate original cap-side chart polygons.

The retained parent and child requests pay both internal path areas and the polygon of parent totals, preserving the
original prepared integration blocks. -/
structure SeparatedAreaRequest (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original retained polynomial comparison request or evaluated cache. -/ polynomial : PathArea.PolynomialRequest
    data (totalTarget / 4) (areaTarget / 4) floor
  /-- The original retained fine child-chart requests or evaluated cache. -/ fine :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests polynomial.requests polynomial.slope
  /-- The cached common polynomial stage paying all original coarse and fine requests. -/ index : Nat
  /-- The common stage is the maximum of the original polynomial and fine-chart request stages. -/ index_eq : index =
    max polynomial.index (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage fine)

constructive_injectivity SeparatedAreaRequest

namespace SeparatedAreaRequest

/-- Cache the original polynomial and fine-chart requests with separate total and area quarter-budgets before selecting
their common stage. -/
@[expose] public def build (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.SeparatedAreaRequest data totalTarget areaTarget floor :=
  let polynomial := PolynomialRequest.build data (totalTarget / 4) (areaTarget / 4)
    (Fraction.Order.Field.div_pos_direct totalPositive (by decide))
    (Fraction.Order.Field.div_pos_direct areaPositive (by decide)) floor
  let fine := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.build polynomial.requests
    polynomial.slope (polynomial.slope_eq ▸ Bank.areaSlopeMaximum_nonnegative data.bank)
  ⟨polynomial, fine, max polynomial.index (Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineRequests.stage
    fine), rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Data cap path owner differential}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.SeparatedAreaRequest data totalTarget
    areaTarget floor}

/-- The retained original side-area request respects the caller's polynomial floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.SeparatedAreaRequest data totalTarget
  areaTarget floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact request.polynomial.floor_le.trans (Purelib.Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- Cached original fine polygons, endpoint joins and integration-path summaries.

Exact source and block readbacks retain the original computation, while the chart decomposition includes both internal
polygon areas and parent-total cross terms. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.SeparatedAreaRequest data
  totalTarget areaTarget floor)
    (capSample : Primitives.Sample cap differential index box) where
  /-- The original retained polynomial comparison request or evaluated cache. -/ polynomial :
    PolynomialRequest.PolynomialEvaluation request.polynomial capSample
  /-- The original retained fine child-chart requests or evaluated cache. -/ fine :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples polynomial.samples request.fine
  /-- The cached operational joins of actual original consecutive polygon endpoints. -/ joins :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins fine
  /-- The cached original chart and polynomial increment paths for every retained parent. -/ pairs : List (List
    InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The cached path pairs are exactly those retained by the original fine-chart bank. -/ pairs_eq : pairs = fine.pairs
  /-- The polynomial paths are exactly the original coarse comparison's source projection. -/ source_eq : pairs.map
    Prod.snd = polynomial.pairs.map Prod.fst
  /-- The cached original complete chart path summary including block cross terms. -/ chart : IncrementArea.Summary
    (pairs.map Prod.fst).flatten
  /-- The actual cached original fine chart polygons in retained parent order. -/ polygons : List (FineCharts.Polygon
    capSample)
  /-- The displayed polygons are exactly the original retained fine-chart polygons. -/ polygons_eq : polygons =
    fine.polygons
  /-- The retained polygon count equals the original prepared parent count. -/ polygon_count : polygons.length =
    data.parentCount
  /-- The chart area is the sum of actual original polygon areas plus the path area of their retained totals. -/
    chart_decomposition : chart.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (polygons.map Polygon.area) +
    IncrementArea.pathArea (polygons.map Polygon.total)
  /-- The cached original prepared integration-path summary. -/ right : IncrementArea.Summary (polynomial.pairs.map
    Prod.snd).flatten
  /-- The integration summary is exactly the original retained polynomial comparison's right summary. -/ right_eq :
    right = polynomial.right
  /-- The actual original direct refinement blocks on the retained parent cache. -/ blocks :
    PreparedDirectDyadicRefinements.DirectBlockRefinement data.cache.parents
  /-- The refinement blocks are exactly those of the original polynomial comparison. -/ blocks_eq : blocks =
    polynomial.blocks
  /-- The retained integration total equals the actual original child path-model sample. -/ right_total : right.total =
    (PathModel.mk (blocks.children.map CenteredEdge.model)).integralSample
  /-- The actual original chart and integration totals satisfy the requested total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (chart.total - right.total) < totalTarget
  /-- The actual original chart and integration areas satisfy the requested area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (chart.area - right.area) < areaTarget

constructive_injectivity Evaluation

/-- Reuse the original polynomial and fine-chart caches to certify the complete side-path total and area discrepancies.
-/
@[expose] public def evaluateReadings (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.SeparatedAreaRequest data totalTarget areaTarget floor)
    (capSample : Primitives.Sample cap differential index box) (later : request.index ≤ index)
    (polynomial : PolynomialRequest.PolynomialEvaluation request.polynomial capSample)
    (fine : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples polynomial.samples request.fine) :
      Evaluation request capSample := by
  have indices := request.index_eq ▸ later
  have polynomialLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
  let pairs := fine.pairs
  let chart := fine.summary
  let polygons := fine.polygons
  have chartDecomposition : chart.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (polygons.map Polygon.area) +
      IncrementArea.pathArea (polygons.map Polygon.total) := by
    rw [chart.area_eq, IncrementArea.pathArea_flatten,
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.polygons_areas,
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.polygons_totals]
    repeat' rewrite [Purelib.Data.List.Map.map_map]
    dsimp only [Function.comp_def]
  have source : pairs.map Prod.snd = polynomial.pairs.map Prod.fst := by
    rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.pairs_source, polynomial.pairs_eq]
  have countEq : pairs.length = data.parentCount := fine.pairs_length.trans data.parents_length
  have bounded := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.bounds fine
    (request.polynomial.index_eq ▸ polynomialLater) request.polynomial.slope_eq.ge
  have slopeNonnegative : 0 ≤ request.polynomial.slope := request.polynomial.slope_eq ▸
    Bank.areaSlopeMaximum_nonnegative data.bank
  have totalClose : Data.Gaussian.Norm.Basic.normSq (chart.total - polynomial.left.total) < totalTarget / 4 :=
    by
    rw [chart.total_eq, polynomial.left.total_eq, ← source, IncrementArea.sum_flatten, IncrementArea.sum_flatten]
    repeat' rewrite [Purelib.Data.List.Map.map_map]
    dsimp only [Function.comp_def]
    have estimate := PathRequests.row_error_le (pairs.map (fun pair => (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      pair.1, Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2))) request.polynomial.budget.tolerance (by
      intro pair member
      obtain ⟨original, inPairs, equal⟩ := Map.mem_map.mp member
      rw [← equal]; exact (bounded original inPairs).2.1)
    repeat' rewrite [Purelib.Data.List.Map.map_map] at estimate
    dsimp only [Function.comp_def] at estimate
    rewrite [Purelib.Data.List.Map.length_map, countEq] at estimate
    apply estimate.trans_lt
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct
      (data.parentCount : InverseRootPolynomial.Coordinate))
      request.polynomial.budget.positive.le
    exact ((Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3)
      nonnegative)).trans_eq
      (by ring1)).trans_lt request.polynomial.budget.total_paid
  have areaClose : Data.Gaussian.Norm.Basic.normSq (chart.area - polynomial.left.area) < areaTarget / 4 := by
    rw [chart.area_eq, polynomial.left.area_eq, ← source]
    have estimate := IncrementAreaComparison.blocks_area_difference_bound pairs request.polynomial.budget.positive.le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 10)
        (add_nonneg slopeNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          request.polynomial.budget.positive.le)))
      (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
      (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
    rw [countEq] at estimate
    have cost := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.area_cost (data.parentCount :
      InverseRootPolynomial.Coordinate) request.polynomial.budget.tolerance request.polynomial.slope
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) request.polynomial.budget.positive.le slopeNonnegative
    rw [← request.polynomial.budget.scale_eq] at cost
    exact (estimate.trans cost).trans_lt request.polynomial.budget.area_paid
  exact ⟨polynomial, fine, Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins.build
    fine data.coordinates,
    pairs, rfl, source, chart, polygons, rfl, fine.polygons_length.trans data.parents_length, chartDecomposition,
    polynomial.right, rfl, polynomial.blocks, rfl, polynomial.right_total,
    Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds totalClose polynomial.total_close,
      Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds areaClose polynomial.area_close⟩

end SeparatedAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
