module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.BoundaryReturn
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FineSideArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSidePolygons
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.JoinedSideReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.ClosingPolygons
public import Purelib.Integration.Path.IncrementAreaClosure
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Tactic.Ring

public section

/-!
# Closed cap boundary polygons with requested integration and area errors

One cap polynomial sample and one retained parent bank supply all readings.
The final common stage pays the internal junctions and the actual root-return
join. The closing edge is the cached endpoint discrepancy; it closes exactly,
preserves the signed polygon area, and is below the requested total budget.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary

open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples (Junction ClosingRequest)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {owner : Topology.SquareRootContinuationChain.Owner
    ((Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval collar.box.anchor)}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A joined cap comparison and closing request with separate total and area targets.

The total comparison receives one quarter of its target; closing retains the original endpoint requests. -/
structure AreaRequest (data : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data cap owner differential) (totalTarget
  areaTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original joined comparison with a quarter of the total target. -/ comparison :
    Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest data.covered (totalTarget / 4) areaTarget floor
  /-- The closing request on the original comparison's endpoint owners. -/ closing :
    Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.ClosingJoin data.covered.bank
  /-- The original total target is positive. -/ positive : 0 < totalTarget

constructive_injectivity AreaRequest

namespace AreaRequest

variable {data : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data cap owner differential} {totalTarget areaTarget :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Read the original comparison request's sufficient stage. -/
@[expose] public def index (request : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest data totalTarget
  areaTarget floor) : Nat := request.comparison.index

/-- Prepare the original quarter-target area comparison and its retained closing coordinates. -/
@[expose] public def build (data : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.Data cap owner differential)
  (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest data totalTarget areaTarget floor :=
  ⟨Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest.build data.covered (totalTarget / 4) areaTarget
    (Data.Rat.Bounds.Quarter.quarter_pos totalPositive) areaPositive floor,
      Hyperelliptic.Charts.Reciprocal.Cap.Boundary.closingCoordinates data, totalPositive⟩

/-- The retained comparison stage meets the requested floor. -/
theorem floor_le (request : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest data totalTarget areaTarget floor)
  : floor ≤ request.index := request.comparison.floor_le

set_option genInjectivity false in
/-- The actual joined comparison, retained closing readings and closed polygon.

The endpoint connector closes the literal flattened path, preserves its area and retains separate total and area error
bounds. -/
structure Evaluation (request : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest data totalTarget areaTarget
  floor)
    {capIndex : Nat} {box : Rational.Box} (sample :
      Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential capIndex box) where
  /-- The actual original joined comparison. -/ joined :
    Hyperelliptic.Charts.Reciprocal.Cap.PathCover.AreaRequest.Evaluation request.comparison sample
  /-- The retained closing readings. -/ closing : List (Junction (totalTarget / 4))
  /-- There are no closing readings for an empty parent family and one otherwise. -/ closing_count : closing.length = if
    data.covered.cache.parents = [] then 0 else 1
  /-- Both original closing indices meet the retained joined stage. -/ closing_indices : ∀ item ∈ closing,
    item.comparison.leftIndex ≤ joined.stage ∧ item.comparison.rightIndex ≤ joined.stage
  /-- The actual endpoint-closing increment. -/ connector : Normalization.InverseRootPolynomial.Gaussian
  /-- The connector is the negative of the original joined total. -/ connector_eq : connector = -joined.chart.total
  /-- The connector is the first endpoint minus the last endpoint. -/ connector_endpoints : connector =
    joined.separated.fine.firstValue - joined.separated.fine.lastValue
  /-- The connector is exactly the sum of the retained closing readings. -/ connector_readings : connector =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (closing.map (fun item =>
    item.source.first.sample joined.stage - item.source.last.sample joined.stage))
  /-- The actual connector magnitude is below one quarter of the total target. -/ connector_small :
    Data.Gaussian.Norm.Basic.normSq connector < totalTarget / 4
  /-- The literal flattened original connection followed by its connector. -/ polygon : Path.IncrementArea.Summary
    ((joined.connections.map (fun block => block.1 :: block.2)).flatten ++ [connector])
  /-- The retained polygon has total zero. -/ polygon_total : polygon.total = 0
  /-- Closing preserves the original joined path's area. -/ polygon_area : polygon.area = joined.chart.area
  /-- The original comparison and closed polygon totals differ by less than the total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (polygon.total - joined.right.total) < totalTarget
  /-- Their actual areas differ by less than the independently retained area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (polygon.area - joined.right.area) < areaTarget

constructive_injectivity Evaluation

/-- Refine the original comparison once to the common junction and closing stage, then close its cached path with the
retained endpoint connector. -/
@[expose] public def evaluate (request : Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest data totalTarget
  areaTarget floor)
    {capIndex : Nat} {box : Rational.Box}
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential capIndex box) (later :
      request.index ≤ capIndex) :
    Hyperelliptic.Charts.Reciprocal.Cap.Boundary.AreaRequest.Evaluation request sample := open Purelib.Polynomial in by
  change request.comparison.separated.index ≤ capIndex at later
  have indices := request.comparison.separated.index_eq ▸ later
  have polynomialLater := (Data.Nat.Order.le_max_left _ _).trans indices
  have fineLater := (Data.Nat.Order.le_max_right _ _).trans indices
  let polynomial := request.comparison.separated.polynomial.evaluatePolynomial sample polynomialLater
  let initial := Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.build polynomial.samples
    request.comparison.separated.fine fineLater
  let junctions := Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.JunctionRequests.build initial
    (Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.EndpointJoins.build initial
      data.covered.coordinates)
    request.comparison.budget.tolerance request.comparison.budget.positive
  let closing := ClosingRequest.build initial request.closing (totalTarget / 4) (Data.Rat.Bounds.Quarter.quarter_pos
    request.positive)
  let stage := max initial.stage (max junctions.stage closing.stage)
  have firstReady : initial.stage ≤ stage := Data.Nat.Order.le_max_left _ _
  have junctionReady : junctions.stage ≤ stage := (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _
    _)
  have closingReady : closing.stage ≤ stage := (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  let fine := initial.refine fineLater stage firstReady
  have junctionValues : fine.gaps = junctions.items.map (fun item => item.source.first.sample stage -
    item.source.last.sample stage) := by
    rw [Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank.FineSamples.gaps_refine, ← junctions.sources_eq,
      Purelib.Data.List.Map.map_map]
    rfl
  let joined := request.comparison.evaluateReadings sample later polynomial fine junctions.items stage
    (fun item member => let bounds := Junction.indices_le junctions.items item member
      ⟨bounds.1.trans (junctions.stage_eq ▸ junctionReady), bounds.2.trans (junctions.stage_eq ▸ junctionReady)⟩)
    junctionValues (fun gap member => (junctions.gaps_small fineLater stage firstReady junctionReady gap member).le)
  have totalEq : joined.chart.total = fine.lastValue - fine.firstValue := fine.connected_total_endpoints
  have connectorEq : -joined.chart.total = fine.firstValue - fine.lastValue := by rw [totalEq]; ring1
  have small : Data.Gaussian.Norm.Basic.normSq (-joined.chart.total) < totalTarget / 4 := by
    rw [connectorEq]
    exact closing.close fineLater stage firstReady closingReady
  let polygon := Path.IncrementAreaClosure.Summary.close joined.chart
  have totalClose : Data.Gaussian.Norm.Basic.normSq (polygon.total - joined.right.total) < totalTarget := by
    have estimate := Clearance.Box.Boundary.Basic.BoundaryClearance.normSq_add_lt_of_quarters small
      joined.total_close.le
    change Data.Gaussian.Norm.Basic.normSq (0 - joined.right.total) < totalTarget
    exact (congrArg Data.Gaussian.Norm.Basic.normSq (show (0 : Normalization.InverseRootPolynomial.Gaussian) -
      joined.right.total =
      -joined.chart.total + (joined.chart.total - joined.right.total) by ring1)).trans_lt estimate
  exact ⟨joined, closing.items, closing.count_eq,
    (fun item member => let bounds := Junction.indices_le closing.items item member
      ⟨bounds.1.trans (closing.stage_eq ▸ closingReady), bounds.2.trans (closing.stage_eq ▸ closingReady)⟩),
    -joined.chart.total, rfl, connectorEq, connectorEq.trans (closing.value_eq fineLater stage firstReady), small,
    polygon, rfl, rfl, totalClose, joined.area_close⟩

end AreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Boundary
