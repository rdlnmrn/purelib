module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSidePolygons
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
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-!
# Requested area of the joined cap-side path

The default side request refines every retained polygon at one common chart
index and inserts the actual endpoint differences between successive parents.
Both connector totals and their complete area cost are paid independently of
the number of children. Source polynomial calculations are retained throughout.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Rat.Bounds
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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples (Junction)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea (PolynomialRequest SideAreaBudget)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus}
  {capIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {path : Polynomial.Geometry.ClearPath
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve) collar.box first last}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval first)}

set_option genInjectivity false in
/-- A complete cap-side area request with retained fine polygons and paid junction connectors.

The original polynomial requests and finite parent-count budget pay separate total and area targets at a common
chart-reading stage. -/
structure AreaRequest (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained separated-polygon request or its exact evaluated cache. -/ separated : PathCover.SeparatedAreaRequest
    data (totalTarget / 4) (areaTarget / 4) floor
  /-- The cached uniform magnitude bound for each retained fine polygon. -/ bound : InverseRootPolynomial.Coordinate
  /-- The magnitude bound is exactly the retained slope and tolerance expression. -/ bound_eq : bound = 10 *
    (separated.polynomial.slope + 3 * separated.polynomial.budget.tolerance)
  /-- The retained polygon magnitude bound is nonnegative. -/ bound_nonnegative : 0 ≤ bound
  /-- The cached finite parent-count budget for all actual connector totals and area terms. -/ budget :
    PathArea.SideAreaBudget bound data.parentCount (totalTarget / 4) (areaTarget / 4)

constructive_injectivity AreaRequest

namespace AreaRequest

/-- Read the retained separated request's common polynomial stage. -/
@[expose] public def index {data : PathCover.Data cap path owner differential} {totalTarget areaTarget :
  InverseRootPolynomial.Coordinate} {floor : Nat}
    (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data totalTarget areaTarget floor) : Nat
      := request.separated.index

/-- Cache the original separated-polygon request and a finite budget for its actual parent connectors. -/
@[expose] public def build (data : PathCover.Data cap path owner differential) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data totalTarget areaTarget floor := by
  have totalQuarter := Quarter.quarter_pos totalPositive
  have areaQuarter := Quarter.quarter_pos areaPositive
  let separated := SeparatedAreaRequest.build data (totalTarget / 4) (areaTarget / 4) totalQuarter areaQuarter floor
  let bound := 10 * (separated.polynomial.slope + 3 * separated.polynomial.budget.tolerance)
  have nonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (separated.polynomial.slope_eq ▸ Bank.areaSlopeMaximum_nonnegative data.bank)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) separated.polynomial.budget.positive.le))
  exact ⟨separated, bound, rfl, nonnegative, SideAreaBudget.build bound nonnegative data.parentCount _ _ totalQuarter
    areaQuarter⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Data cap path owner differential}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The complete cap-side request retains the supplied polynomial-stage floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data totalTarget areaTarget
  floor) : floor ≤ request.index := request.separated.floor_le

set_option genInjectivity false in
/-- Cached original fine polygons with their actual connectors and complete paid path summary. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data totalTarget
  areaTarget floor)
    (capSample : Primitives.Sample cap differential capIndex box) where
  /-- The retained separated-polygon request or its exact evaluated cache. -/ separated :
    SeparatedAreaRequest.Evaluation request.separated capSample
  /-- The retained operational endpoint comparisons in actual parent-boundary order. -/ junctions : List
    (FineSamples.Junction request.budget.tolerance)
  /-- The cached common chart-reading stage for polygons and junction comparisons. -/ stage : Nat
  /-- Both indices of every retained endpoint comparison fit the common stage. -/ junction_indices : ∀ item ∈ junctions,
    item.comparison.leftIndex ≤ stage ∧ item.comparison.rightIndex ≤ stage
  /-- The actual retained polygon gaps are exactly the compared endpoint-stream differences. -/ junction_values :
    separated.fine.gaps = junctions.map (fun item => item.source.first.sample stage - item.source.last.sample stage)
  /-- The cached incoming connectors and complete retained fine polygon paths. -/ connections : List
    (InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The connection blocks are exactly those of the retained fine polygons with zero initial connector. -/
    connections_eq : connections = separated.fine.connectedBlocks 0
  /-- The connection-block count is exactly the original retained parent count. -/ connection_count : connections.length
    = data.parentCount
  /-- Every actual incoming connector satisfies the paid shared tolerance. -/ connections_small : ∀ block ∈ connections,
    Data.Gaussian.Norm.Basic.normSq block.1 ≤ request.budget.tolerance
  /-- The cached complete connected-chart path summary, including internal and cross terms. -/ chart :
    IncrementArea.Summary (connections.map (fun block => block.1 :: block.2)).flatten
  /-- The complete area splits into actual block areas plus the polygon of their retained totals. -/ chart_decomposition
    : chart.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (connections.map (fun block => IncrementArea.pathArea
    (block.1 :: block.2))) +
    IncrementArea.pathArea (connections.map (fun block => block.1 + Data.Gaussian.Norm.Sum.Basic.gaussianSum
      block.2))
  /-- The cached original integration-path summary. -/ right : IncrementArea.Summary (separated.polynomial.pairs.map
    Prod.snd).flatten
  /-- The integration summary is exactly the separated comparison's retained summary. -/ right_eq : right =
    separated.right
  /-- The original retained direct-refinement blocks. -/ blocks : PreparedDirectDyadicRefinements.DirectBlockRefinement
    data.cache.parents
  /-- The refinement blocks are exactly those retained by the separated comparison. -/ blocks_eq : blocks =
    separated.blocks
  /-- The integration total reads the exact original refined path-model sample. -/ right_total : right.total =
    (PathModel.mk (blocks.children.map CenteredEdge.model)).integralSample
  /-- The actual connected-chart and integration totals satisfy the requested target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (chart.total - right.total) < totalTarget
  /-- The actual connected-chart and integration areas satisfy the requested target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (chart.area - right.area) < areaTarget

constructive_injectivity Evaluation

/-- Assemble the comparison from retained polynomial samples and certified fine readings. Additional endpoint
comparisons may raise the common stage before this constructor, without repeating polynomial evaluation. -/
@[expose] public def evaluateReadings (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data
  totalTarget areaTarget floor)
    (capSample : Primitives.Sample cap differential capIndex box) (later : request.index ≤ capIndex)
    (polynomial : PolynomialRequest.PolynomialEvaluation request.separated.polynomial capSample)
    (fine : Bank.FineSamples polynomial.samples request.separated.fine)
    (junctions : List (FineSamples.Junction request.budget.tolerance)) (stage : Nat)
    (junctionIndices : ∀ item ∈ junctions, item.comparison.leftIndex ≤ stage ∧ item.comparison.rightIndex ≤ stage)
    (junctionValues : fine.gaps = junctions.map (fun item => item.source.first.sample stage - item.source.last.sample
      stage))
    (gapsSmall : ∀ gap ∈ fine.gaps, Data.Gaussian.Norm.Basic.normSq gap ≤ request.budget.tolerance) :
      Evaluation request capSample := by
  change request.separated.index ≤ capIndex at later
  have indices := request.separated.index_eq ▸ later
  have polynomialLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
  let separated := request.separated.evaluateReadings capSample later polynomial fine
  let connections := fine.connectedBlocks 0
  let chart := fine.connectedSummary 0
  have connectionCount : connections.length = data.parentCount := (fine.connectedBlocks_length 0).trans
    data.parents_length
  have source : connections.map Prod.snd = separated.pairs.map Prod.fst := fine.connectedBlocks_source 0
  have small : ∀ block ∈ connections, Data.Gaussian.Norm.Basic.normSq block.1 ≤ request.budget.tolerance :=
    fine.connectedBlocks_small 0 (by simpa only [Data.Gaussian.Norm.Basic.normSq_zero] using request.budget.positive.le)
      gapsSmall
  have fineBound := FineSamples.bounds fine (request.separated.polynomial.index_eq ▸ polynomialLater)
    request.separated.polynomial.slope_eq.ge
  have bounded : ∀ block ∈ connections, Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum block.2) ≤ request.bound := by
    intro block member
    have retained : block.2 ∈ separated.pairs.map Prod.fst := source ▸ Map.mem_map.mpr ⟨block, member, rfl⟩
    obtain ⟨pair, retained, equal⟩ := Map.mem_map.mp retained
    rw [← equal, request.bound_eq]
    exact (fineBound pair retained).2.2.1
  have totalClose : Data.Gaussian.Norm.Basic.normSq (chart.total - separated.chart.total) < totalTarget / 4 :=
    by
    rw [chart.total_eq, separated.chart.total_eq, ← source]
    have estimate := IncrementAreaJoins.joined_blocks_total_bound connections small
    rw [connectionCount] at estimate
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct
      (data.parentCount : InverseRootPolynomial.Coordinate))
      request.budget.positive.le
    exact estimate.trans_lt (((Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3)
        nonnegative)).trans_eq (by ring1)).trans_lt request.budget.total_paid)
  have areaClose : Data.Gaussian.Norm.Basic.normSq (chart.area - separated.chart.area) < areaTarget / 4 := by
    rw [chart.area_eq, separated.chart.area_eq, ← source]
    have estimate := IncrementAreaJoins.joined_blocks_area_bound connections request.budget.positive.le
      request.bound_nonnegative small bounded
    rw [connectionCount] at estimate
    have cost := IncrementAreaJoins.joined_blocks_cost (data.parentCount : InverseRootPolynomial.Coordinate)
      request.budget.tolerance request.bound
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) request.budget.positive.le request.bound_nonnegative
    rw [← request.budget.scale_eq] at cost
    exact (estimate.trans cost).trans_lt request.budget.area_paid
  have decomposition : chart.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (connections.map (fun block =>
    IncrementArea.pathArea (block.1 :: block.2))) +
      IncrementArea.pathArea (connections.map (fun block => block.1 + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        block.2)) := by
    rw [chart.area_eq, IncrementArea.pathArea_flatten]
    repeat' rewrite [Purelib.Data.List.Map.map_map]
    dsimp only [Function.comp_def, Data.Gaussian.Norm.Sum.Basic.gaussianSum]
  exact ⟨separated, junctions, stage, junctionIndices,
    junctionValues, connections, rfl, connectionCount, small, chart, decomposition,
    separated.right, rfl, separated.blocks, rfl, separated.right_total,
    Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds totalClose separated.total_close,
      Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds areaClose
      separated.area_close⟩

/-- Evaluate the original polynomial caches once, compare actual endpoint streams and refine all polygons to their
shared paid reading stage. -/
@[expose] public def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data
  totalTarget areaTarget floor)
    (capSample : Primitives.Sample cap differential capIndex box) (later : request.index ≤ capIndex) :
      Evaluation request capSample := by
  change request.separated.index ≤ capIndex at later
  have indices := request.separated.index_eq ▸ later
  have polynomialLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
  have fineLater := (Purelib.Data.Nat.Order.le_max_right _ _).trans indices
  let polynomial := request.separated.polynomial.evaluatePolynomial capSample polynomialLater
  let initial := FineSamples.build polynomial.samples request.separated.fine fineLater
  let joins := EndpointJoins.build initial data.coordinates
  let junctions := JunctionRequests.build initial joins request.budget.tolerance request.budget.positive
  let stage := max initial.stage junctions.stage
  let fine := initial.refine fineLater stage (Purelib.Data.Nat.Order.le_max_left _ _)
  have junctionValues : fine.gaps = junctions.items.map (fun item => item.source.first.sample stage -
    item.source.last.sample stage) := by
    rw [FineSamples.gaps_refine, ← junctions.sources_eq, Purelib.Data.List.Map.map_map]
    rfl
  exact request.evaluateReadings capSample later polynomial fine junctions.items stage
    (fun item member => let bounds := Junction.indices_le junctions.items item member
      ⟨bounds.1.trans (junctions.stage_eq ▸ Purelib.Data.Nat.Order.le_max_right initial.stage junctions.stage),
        bounds.2.trans (junctions.stage_eq ▸ Purelib.Data.Nat.Order.le_max_right initial.stage junctions.stage)⟩)
    junctionValues
    (fun gap member => (junctions.gaps_small fineLater stage (Purelib.Data.Nat.Order.le_max_left _ _)
      (Purelib.Data.Nat.Order.le_max_right _ _) gap member).le)

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
