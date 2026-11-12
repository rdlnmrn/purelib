module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
open Purelib.Data.Rat
open Purelib.Riemann.Normalization

/-!
# Requested chart replacement of an existing connected exterior path

The supplied connected request and all its controlled source obligations
remain intact. Its actual parents, joins and endpoint readings are acquired
with the chart samples. The replacement has exactly its total, and its full
area differs by less than the additional requested budget.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide (ConnectedRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parents : List (Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {prepared : Preparation regular parents}
    {totalTarget areaTarget : Coordinate} {minimum : Nat}
  {request : ConnectedRequest prepared totalTarget
    areaTarget minimum}

set_option genInjectivity false in
/-- A paid chart replacement request preserving an original complete connected exterior path.

The actual parent requests retain their existing source obligations and determine shared model and depth floors. -/
structure ChartRequest (request : ConnectedRequest prepared totalTarget areaTarget minimum) (target :
  Coordinate) where
  /-- The additional original whole-path area target is strictly positive. -/ positive : 0 < target
  /-- The cached local area allowance for one actual original parent. -/ parentTarget : Coordinate
  /-- The local allowance is the original target allocated over the actual parent count. -/ parentTarget_eq :
    parentTarget = Aggregate.perTerm target parents.length
  /-- The retained chart requests on the exact original separated parent request bank. -/ requests :
    ChartRequests parentTarget request.separated.requests
  /-- The cached common model stage paying both original and chart requests. -/ index : Nat
  /-- The model stage is exactly the maximum of the original request and actual chart-request stages. -/ index_eq :
    index = max request.index requests.maximum
  /-- The cached maximum depth required by all original parent chart requests. -/ depth : Nat
  /-- The chart depth is exactly the complete parent-request depth maximum. -/ depth_eq : depth = requests.depthMaximum

constructive_injectivity ChartRequest

namespace ChartRequest

/-- Allocate the original additional target among actual parents and retain their complete chart requests and exact
common floors. -/
@[expose] def build (request : ConnectedRequest prepared totalTarget areaTarget minimum) (target :
  Coordinate) (positive : 0 < target) :
    ChartRequest request target :=
  let parentTarget := Aggregate.perTerm target parents.length
  let requests := ChartRequests.build parentTarget (Aggregate.perTerm_positive positive _) request.separated.requests
  ⟨positive, parentTarget, rfl, requests, max request.index requests.maximum, rfl, requests.depthMaximum, rfl⟩

variable {target : Coordinate} {index : Nat} {box :
  Geometry.Rational.Box}
  {sample : Primitives.Sample cap differential index box} {charts :
    ChartRequest request target}

set_option genInjectivity false in
/-- The actual chart plans consuming one retained cap sample and their shared reading floor. -/
structure Plan (charts : ChartRequest request target)
  (sample : Primitives.Sample cap differential index box) where
  /-- The retained complete parent chart plans on this exact original cap sample. -/ parents :
    ChartPlans sample charts.requests
  /-- The cached common reading stage paying the original request and all parent plans. -/ stage : Nat
  /-- The reading stage is exactly the maximum of the original reading floor and parent-plan stages. -/ stage_eq : stage
    = max request.readingIndex parents.maximum

constructive_injectivity Plan

namespace Plan

/-- Cache all original parent chart plans using the supplied cap sample and retain their exact common reading stage. -/
@[expose] def build (charts : ChartRequest request target)
  (sample : Primitives.Sample cap differential index box) :
  Plan charts sample :=
  let parents := ChartPlans.build sample charts.requests
  ⟨parents, max request.readingIndex parents.maximum, rfl⟩

variable {depth readingIndex : Nat} {plan :
  Plan charts sample}

set_option genInjectivity false in
/-- The actual connected chart replacement and its preserved original-path guarantees.

The original evaluation and parent replacements share their retained samples; exact total readback and separate area
budgets remain explicit. -/
structure Evaluation (plan : Plan charts
  sample) (depth readingIndex : Nat) where
  /-- The retained original connected-path evaluation on the same cap sample, depth and reading stage. -/ original :
    ConnectedRequest.Evaluation request sample depth readingIndex
  /-- The actual chart replacements on the original evaluated parent bank. -/ replacements :
    ChartReplacements charts.parentTarget original.separated.parents
  /-- The complete retained connected replacement with the original leading value and parent connectors. -/ connected :
    Connected original.separated.parents replacements original.firstValue
  /-- The replacement's full total equals the original connected cap-path total. -/ total_eq : connected.summary.total =
    original.cap.total
  /-- The actual replacement-versus-original cap area discrepancy satisfies the additional target. -/ area_error :
    Basic.normSq (connected.summary.area - original.cap.area) < target
  /-- The original source and retained replacement totals satisfy the original total target. -/ total_close :
    Basic.normSq (original.separated.left.total - connected.summary.total) < totalTarget
  /-- The original integral sample and retained replacement total satisfy that same original target. -/ integral_close :
    Basic.normSq (original.separated.compared.source.integralSample -
    connected.summary.total) < totalTarget
  /-- The original source and retained replacement areas satisfy the combined original and additional area budget. -/
    area_close : Basic.normSq (original.separated.left.area - connected.summary.area) < 2 *
    (areaTarget + target)

constructive_injectivity Evaluation

/-- Evaluate the original connected path and actual chart replacements from the same retained parent samples at the
supplied paid stages. -/
@[expose] def evaluate (plan : Plan charts
  sample) (depth readingIndex : Nat)
    (later : charts.index ≤ index) (fineLater : charts.depth ≤ depth) (readingLater : plan.stage ≤ readingIndex) :
    Evaluation plan depth readingIndex :=
      by
  have indices := charts.index_eq.ge.trans later
  have stages := plan.stage_eq.ge.trans readingLater
  have originalLater : request.separated.requests.maximum ≤ index :=
    request.separated.index_eq.ge.trans ((Data.Nat.Order.le_max_left _ _).trans indices)
  let sampled := ChartPlans.evaluate plan.parents prepared.proper originalLater ((Data.Nat.Order.le_max_right _ _).trans
    indices)
    (charts.depth_eq.ge.trans fineLater) ((Data.Nat.Order.le_max_right _ _).trans stages)
  let separated := request.separated.evaluateWithParents sampled.1
  let original := request.evaluateWithSeparated separated ((Data.Nat.Order.le_max_left _ _).trans stages)
  let connected := Connected.build sampled.1 sampled.2 original.firstValue
  have totalEq : connected.summary.total = original.cap.total := by
    rw [connected.total_eq, ((Evaluations.connectedSummary sampled.1 original.firstValue)).total_eq,
      original.cap.total_eq, original.blocks_eq]
    rfl
  have areaEq : ((Evaluations.connectedSummary sampled.1 original.firstValue)).area = original.cap.area := by
    rw [((Evaluations.connectedSummary sampled.1 original.firstValue)).area_eq, original.cap.area_eq,
      original.blocks_eq]
    rfl
  have areaError : Basic.normSq (connected.summary.area - original.cap.area) < target := by
    rw [← areaEq]
    have paid : (parents.length : Coordinate) ^ 2 * charts.parentTarget < target := by
      rw [charts.parentTarget_eq]
      simpa only [pow_two, Fraction.Field.mul_assoc, -eq_self, -iff_self] using Aggregate.count_mul_perTerm_lt
        charts.positive parents.length
    exact (Connected.area_error connected).trans_lt paid

  have reversed : Basic.normSq (original.cap.area - connected.summary.area) < target := by
    rw [show original.cap.area - connected.summary.area = -(connected.summary.area - original.cap.area) by ring1,
      Basic.normSq_neg]
    exact areaError
  refine ⟨original, sampled.2, connected, totalEq, areaError, ?_, ?_, ?_⟩
  · rw [totalEq]; exact original.total_close
  · rw [totalEq]; exact original.integral_close
  · exact (Bounds.normSq_sub_le_via original.separated.left.area original.cap.area
      connected.summary.area).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct original.area_close reversed))

end Plan

set_option genInjectivity false in
/-- The acquired cap sample, exact chart plan and complete connected replacement at retained sufficient stages. -/
structure Acquisition (charts : ChartRequest request target)
  (depthFloor : Nat) where
  /-- The actual cap sample cached once at the retained model stage on the original collar box. -/ sample :
    Primitives.Sample cap differential charts.index collar.box
  /-- The complete chart plan built on this exact retained cap sample. -/ plan :
    Plan charts sample
  /-- The actual selected depth meeting both the caller floor and retained chart requirement. -/ depth : Nat
  /-- The acquired depth is exactly the maximum of the original caller floor and chart depth. -/ depth_eq : depth = max
    depthFloor charts.depth
  /-- The actual replacement evaluation on the retained sample and selected depth and reading stages. -/ evaluated :
    Plan.Evaluation plan depth plan.stage

constructive_injectivity Acquisition

/-- Build the cap sample once, retain its complete chart plan and evaluate above both the original and supplied depth
floors. -/
@[expose] def acquire (charts : ChartRequest request target)
  (depthFloor : Nat) : Acquisition charts
  depthFloor :=
  let sample := Primitives.Sample.build cap differential charts.index collar.box
  let plan := Plan.build charts sample
  let depth := max depthFloor charts.depth
  ⟨sample, plan, depth, rfl, plan.evaluate depth plan.stage le_rfl (Data.Nat.Order.le_max_right _ _) le_rfl⟩

end ChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
