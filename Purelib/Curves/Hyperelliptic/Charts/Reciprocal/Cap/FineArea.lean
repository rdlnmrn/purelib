module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
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

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartPolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ChartVertices
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CommonReadings
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathRequests
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Tactic.Ring

public section

/-!
# Requested chart area on every retained integration child

All child counts are known before the common polynomial stage is selected.
The endpoint budget pays the full finite area comparison, including internal
excursions, and keeps the literal local-polynomial and integration paths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedArea.ReciprocalCapPreparedPrimitives (areaSlope
  areaSlope_nonnegative)
open Purelib.Integration.Path.IncrementArea (pathArea Summary)

/-- Factor the original retained count-dependent area weight from its endpoint error allowance. -/
public theorem area_weight (count error bound : InverseRootPolynomial.Coordinate) :
    64 * count ^ 4 * error * (2 * (4 + bound)) = (64 * count ^ 4 * (2 * (4 + bound))) * error := by ring1

/-- Normalize the original finite path-area comparison coefficient using its actual child count. -/
public theorem area_count (count error bound : InverseRootPolynomial.Coordinate) :
    16 * count ^ 4 * (4 * error) * (2 * (4 + bound)) = 64 * count ^ 4 * error * (2 * (4 + bound)) := by ring1

/-- A positive original allowance below the target divided by weight plus one strictly pays a nonnegative weight. -/
public theorem allowance_paid {weight error target : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ weight)
    (positive : 0 < error) (selected : error ≤ target / (weight + 1)) : weight * error < target := by
  have larger : weight < weight + 1 := by
    simpa only [_root_.add_zero] using
      Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 1) weight
  have denominator : 0 < weight + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide)
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct larger positive).trans_le
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct selected denominator.le).trans_eq
  rw [Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'

set_option genInjectivity false in
/-- A shared endpoint-error allowance paying the original finite child-count total and area targets. -/
structure Budget (count : Nat) (bound totalTarget areaTarget : InverseRootPolynomial.Coordinate) where
  /-- The cached endpoint discrepancy allowance for the original finite child count. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The retained endpoint allowance is strictly positive. -/ positive : 0 < error
  /-- The original endpoint allowance is bounded by one. -/ at_most_one : error ≤ 1
  /-- The retained allowance pays the original count-squared total discrepancy target. -/ total_paid : 4 * (count :
    InverseRootPolynomial.Coordinate) ^ 2 * error < totalTarget
  /-- The retained allowance pays the original count-fourth-power area discrepancy target. -/ area_paid : 64 * (count :
    InverseRootPolynomial.Coordinate) ^ 4 * error * (2 * (4 + bound)) < areaTarget

constructive_injectivity Budget

/-- Cache the original finite child-count budget and shared chart requests before selecting the common polynomial stage.
-/
@[expose] public def Budget.build (count : Nat) (bound : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ bound)
    (totalTarget areaTarget : InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget) (areaPositive : 0 <
      areaTarget) :
    Budget count bound totalTarget areaTarget := by
  let totalWeight := 4 * (count : InverseRootPolynomial.Coordinate) ^ 2
  let areaWeight := 64 * (count : InverseRootPolynomial.Coordinate) ^ 4 * (2 * (4 + bound))
  have totalNonnegative : 0 ≤ totalWeight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have areaNonnegative : 0 ≤ areaWeight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide) nonnegative))
  let error := min 1 (min (totalTarget / (totalWeight + 1)) (areaTarget / (areaWeight + 1)))
  have positive : 0 < error := Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct totalPositive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      totalNonnegative (by decide)))
    (Fraction.Order.Field.div_pos_direct areaPositive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      areaNonnegative (by decide))))
  refine ⟨error, positive, Fraction.Order.Basic.min_le_left _ _,
    allowance_paid totalNonnegative positive
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)), ?_⟩
  have selected : error ≤ areaTarget / (areaWeight + 1) := (Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_right _ _)
  have paid : areaWeight * error < areaTarget :=
    allowance_paid areaNonnegative positive selected
  calc
    _ = areaWeight * error := area_weight (count :
      InverseRootPolynomial.Coordinate) error bound
    _ < areaTarget := paid

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}
  {parent : Parent curve differential} {data : ParentData cap differential count parent}
  {integrationTarget : Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- Cached chart endpoint requests for every actual child of an original prepared cap block.

The retained count and source bound pay separate total and area targets; shared child vertices and the common polynomial
floor remain explicit. -/
structure AreaRequest (base : PreparedPrimitives.Request data integrationTarget floor)
    (totalTarget areaTarget : InverseRootPolynomial.Coordinate) where
  /-- The cached original child polynomial magnitude ceiling. -/ bound : InverseRootPolynomial.Coordinate
  /-- The bound is four times the original parent area slope plus three integration targets. -/ bound_eq : bound = 4 *
    (ReciprocalCapPreparedPrimitives.areaSlope data + 3 * integrationTarget)
  /-- The paid endpoint allowance for the exact original child count and magnitude ceiling. -/ budget :
    Budget base.block.children.length bound totalTarget areaTarget
  /-- The cached chart requests on the actual original retained child chain. -/ children : FineCharts.Requests
    data.comparison budget.error floor base.block.children
  /-- Consecutive original children retain literally shared endpoint requests or evaluated chart vertices. -/ shared :
    Requests.Shared children
  /-- The cached common polynomial stage paying the original preparation and all child requests. -/ index : Nat
  /-- The common index is the maximum of the original base and child-request stages. -/ index_eq : index = max
    base.index children.index

constructive_injectivity AreaRequest

namespace AreaRequest

/-- Cache the original finite child-count budget and shared chart requests before selecting the common polynomial stage.
-/
@[expose] public def build (base : PreparedPrimitives.Request data integrationTarget floor)
    (totalTarget areaTarget : InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget) (areaPositive : 0 <
      areaTarget) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget areaTarget :=
  let bound := 4 * (ReciprocalCapPreparedPrimitives.areaSlope data + 3 * integrationTarget)
  let budget := Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.Budget.build base.block.children.length bound
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (ReciprocalCapPreparedPrimitives.areaSlope_nonnegative data)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) base.positive.le))) totalTarget areaTarget totalPositive
        areaPositive
  let children := Requests.build base budget.error budget.positive base.block.children (fun _ member => member)
  ⟨bound, rfl, budget, children,
    Requests.build_shared base budget.error budget.positive base.block.children (fun _ member => member)
      base.block.chain,
    max base.index children.index, rfl⟩

variable {base : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data integrationTarget
  floor}
  {totalTarget areaTarget : Coordinate} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The retained original chart-area request respects the caller's polynomial floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget
  areaTarget) : floor ≤ request.index := by
  rw [request.index_eq]
  exact base.floor_le.trans (Purelib.Data.Nat.Order.le_max_left _ _)

/-- The original prepared cap block's finite dyadic child chain is nonempty. -/
theorem children_nonempty (_request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget
  areaTarget) : base.block.children ≠ [] := by
  intro empty
  have length := base.block.childCount
  rw [empty] at length
  exact (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))).elim length.symm

set_option genInjectivity false in
/-- The actual original child readings, chart polygon and retained polynomial path summaries.

Exact endpoint and source readbacks tie the cached polygon to the original child chain, while separate total, area and
integration-area bounds retain their paid targets. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base totalTarget
  areaTarget)
    (retained : PreparedPrimitives.Sample base capSample) where
  /-- The cached evaluations of the exact original child chart requests. -/ charts : FineCharts.Samples
    retained.retained.retained.comparison request.children
  /-- Consecutive original children retain literally shared endpoint requests or evaluated chart vertices. -/ shared :
    charts.Shared
  /-- The retained original parent-start endpoint evaluation. -/ first : FineCharts.RetainedPoint data.comparison
    retained.retained.retained.comparison (parent.edge.point 0) request.budget.error floor
  /-- The retained original parent-finish endpoint evaluation. -/ last : FineCharts.RetainedPoint data.comparison
    retained.retained.retained.comparison (parent.edge.point 1) request.budget.error floor
  /-- The first endpoint is exactly the original child spine's retained first reading transported to the parent start.
  -/
  first_eq : first = (charts.firstPoint ⟨base.block.chain⟩ request.children_nonempty).cast
    parent.edge.point_zero.symm
  /-- The last endpoint is exactly the original child spine's retained last reading transported to the parent finish. -/
    last_eq : last = (charts.lastPoint ⟨base.block.chain⟩ request.children_nonempty).cast parent.edge.point_one.symm
  /-- The cached chart and original polynomial increment rows. -/ pairs : List (InverseRootPolynomial.Gaussian ×
    InverseRootPolynomial.Gaussian)
  /-- The cached rows are exactly the original evaluated child rows. -/ pairs_eq : pairs = charts.rows
  /-- The retained polynomial projection is exactly the original prepared source increment projection. -/ source_eq :
    pairs.map Prod.snd = (ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map Prod.fst
  /-- The cached literal chart polygon vertices in original child order. -/ vertices : List (FineCharts.Vertex capSample
    request.budget.error)
  /-- The vertices are exactly those read from the retained original child evaluations. -/ vertices_eq : vertices =
    charts.vertices
  /-- The retained polygon has one more actual vertex than original children. -/ vertex_count : vertices.length =
    base.block.children.length + 1
  /-- The retained vertex points are the original parent start followed by each actual child endpoint. -/ vertex_points
    : vertices.map Vertex.point = parent.edge.point 0 :: base.block.children.map (fun child => child.edge.point 1)
  /-- The first retained polygon vertex is the original first endpoint reading. -/ vertex_first : vertices.head? = some
    first.vertex
  /-- The last retained polygon vertex is the original last endpoint reading. -/ vertex_last : vertices.getLast? = some
    last.vertex
  /-- The actual retained vertex increments are exactly the cached chart row projection. -/ vertex_increments :
    Vertex.increments vertices = pairs.map Prod.fst
  /-- The cached total and area summary of the original chart increments. -/ chart : IncrementArea.Summary (pairs.map
    Prod.fst)
  /-- The cached chart area includes exactly the original polygon's explicit closing edge. -/ chart_polygon : chart.area
    = Vertex.closedArea vertices
  /-- The cached total and area summary of the original polynomial increments. -/ polynomial : IncrementArea.Summary
    (pairs.map Prod.snd)
  /-- The actual retained chart and polynomial totals satisfy the original total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (chart.total - polynomial.total) < totalTarget
  /-- The actual retained chart and polynomial areas satisfy the original area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (chart.area - polynomial.area) < areaTarget
  /-- The original chart area satisfies the combined paid polynomial and integration-area discrepancy bound. -/
    integral_area_close : Data.Gaussian.Norm.Basic.normSq (chart.area - IncrementArea.pathArea
    ((ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map Prod.snd)) <
    2 * (areaTarget + 256 * integrationTarget * (ReciprocalCapPreparedPrimitives.areaSlope data + 3 *
      integrationTarget))

constructive_injectivity Evaluation

/-- Expose the original evaluated chart polygon using its already cached vertices, total and closed area. -/
@[expose] public def Evaluation.polygon {request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest
  base totalTarget areaTarget}
    {retained : PreparedPrimitives.Sample base capSample} (evaluated :
      Evaluation request retained) :
      FineCharts.Polygon capSample :=
  ⟨request.budget.error, evaluated.vertices, evaluated.chart.total,
    evaluated.chart.total_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
      evaluated.vertex_increments.symm),
    evaluated.chart.area, evaluated.chart_polygon⟩

/-- Reuse the supplied original chart readings and polynomial summary, caching exact polygon readbacks and all paid
discrepancies. -/
@[expose] public def evaluateReadings (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base
  totalTarget areaTarget)
    (retained : PreparedPrimitives.Sample base capSample) (later : request.index ≤ index)
    (charts : FineCharts.Samples retained.retained.retained.comparison request.children) (shared : charts.Shared)
    (pairs : List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) (pairsEq : pairs = charts.rows)
      (polynomial : IncrementArea.Summary (pairs.map Prod.snd)) :
    Evaluation request retained := by
  have indices := request.index_eq ▸ later
  have baseLater : base.index ≤ index := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
  let vertices := charts.vertices
  have nonempty := request.children_nonempty
  let first := (charts.firstPoint ⟨base.block.chain⟩ nonempty).cast parent.edge.point_zero.symm
  let last := (charts.lastPoint ⟨base.block.chain⟩ nonempty).cast parent.edge.point_one.symm
  have vertexFirst : vertices.head? = some first.vertex :=
    (charts.vertices_first ⟨base.block.chain⟩ nonempty).trans
      (congrArg some (RetainedPoint.cast_vertex _ parent.edge.point_zero.symm).symm)
  have vertexLast : vertices.getLast? = some last.vertex :=
    (charts.vertices_last ⟨base.block.chain⟩ nonempty).trans
      (congrArg some (RetainedPoint.cast_vertex _ parent.edge.point_one.symm).symm)
  have vertexPoints : vertices.map Vertex.point = parent.edge.point 0 :: base.block.children.map (fun child =>
    child.edge.point 1) := by
    rw [Samples.vertices_points charts nonempty base.block.chain, parent.edge.point_zero]
  have source : pairs.map Prod.snd = (ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map Prod.fst := by
    rw [pairsEq, Samples.rows_source]
    rewrite [ReciprocalCapPreparedPrimitives.Sample.areaPairs, Purelib.Data.List.Map.map_map, retained.block_eq]
    exact Eq.refl _
  have countEq : pairs.length = base.block.children.length := pairsEq ▸ charts.rows_length
  have boundNonnegative : 0 ≤ request.bound := by
    rw [request.bound_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (ReciprocalCapPreparedPrimitives.areaSlope_nonnegative data)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) base.positive.le))
  have sourceBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq pair.2 ≤ request.bound := by
    intro pair member
    have inSource : pair.2 ∈ (ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map Prod.fst := source ▸
      Map.mem_map.mpr ⟨pair, member, rfl⟩
    rewrite [ReciprocalCapPreparedPrimitives.Sample.areaPairs, Purelib.Data.List.Map.map_map] at inSource
    dsimp only [Function.comp_def] at inSource
    obtain ⟨child, inChildren, equal⟩ := Map.mem_map.mp inSource
    rw [← equal, request.bound_eq]
    exact (ReciprocalCapPreparedPrimitives.Sample.polynomial_child_bound retained) baseLater inChildren
  have errorBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ 4 *
    request.budget.error := by
    rw [pairsEq]
    exact charts.rows_accurate
  have chartBound : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq pair.1 ≤ 2 * (4 + request.bound) := by
    intro pair member
    have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two (pair.1 - pair.2) pair.2
    rw [sub_add_cancel] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add ((errorBound pair member).trans (by
        simpa only [Fraction.Field.mul_one_direct] using
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.budget.at_most_one (by
              decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)))
        (sourceBound pair member)) (by decide))
  have commonBound : request.bound ≤ 2 * (4 + request.bound) :=
    (Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _ (add_nonneg (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 8) boundNonnegative)).trans_eq (by ring1)
  let chart := IncrementArea.Summary.build (pairs.map Prod.fst)
  have totalClose : Data.Gaussian.Norm.Basic.normSq (chart.total - polynomial.total) < totalTarget := by
    rw [chart.total_eq, polynomial.total_eq]
    have estimate := PathRequests.row_error_le pairs (4 * request.budget.error) errorBound
    rw [countEq] at estimate
    exact estimate.trans_lt ((by ring1 : (base.block.children.length : InverseRootPolynomial.Coordinate) ^ 2 * (4 *
      request.budget.error) =
      4 * (base.block.children.length : InverseRootPolynomial.Coordinate) ^ 2 * request.budget.error) ▸
        request.budget.total_paid)
  have areaClose : Data.Gaussian.Norm.Basic.normSq (chart.area - polynomial.area) < areaTarget := by
    rw [chart.area_eq, polynomial.area_eq]
    have estimate := IncrementAreaComparison.pathArea_difference_bound pairs
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
        request.budget.positive.le)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2) (add_nonneg
        (by decide) boundNonnegative))
      errorBound chartBound (fun pair member => (sourceBound pair member).trans commonBound)
    rw [countEq] at estimate
    exact (estimate.trans_eq (Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.area_count
      (base.block.children.length : InverseRootPolynomial.Coordinate) request.budget.error request.bound)).trans_lt
      request.budget.area_paid
  have chartPolygon : chart.area = Vertex.closedArea vertices :=
    chart.area_eq.trans ((congrArg (fun rows => IncrementArea.pathArea (rows.map Prod.fst)) pairsEq).trans
      (charts.polygon_area shared))
  refine ⟨charts, shared, first, last, rfl, rfl, pairs, pairsEq, source, vertices, rfl,
    charts.vertices_length_of_nonempty nonempty, vertexPoints,
    vertexFirst, vertexLast,
    (by rw [pairsEq]; exact charts.increments_eq shared), chart, chartPolygon, polynomial, totalClose, areaClose, ?_⟩
  have original := (ReciprocalCapPreparedPrimitives.Sample.area_error_lt retained) baseLater
  rw [← source, ← polynomial.area_eq] at original
  rw [show chart.area - IncrementArea.pathArea ((ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map
    Prod.snd) =
    (chart.area - polynomial.area) + (polynomial.area - IncrementArea.pathArea
      ((ReciprocalCapPreparedPrimitives.Sample.areaPairs retained).map Prod.snd)) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct areaClose original))

/-- Evaluate the original shared child requests once and cache their literal chart polygon and source path summary. -/
@[expose] public def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts.AreaRequest base
  totalTarget areaTarget)
    (retained : PreparedPrimitives.Sample base capSample) (later : request.index ≤ index) :
      Evaluation request retained :=
  let ready := (Purelib.Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let charts := Samples.build retained.retained.retained.comparison request.children ready
  let pairs := charts.rows
  request.evaluateReadings retained later charts
    (Samples.build_shared retained.retained.retained.comparison request.children request.shared base.block.chain ready)
    pairs rfl (IncrementArea.Summary.build (pairs.map Prod.snd))

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineCharts
