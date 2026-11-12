module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry
public import Purelib.Approximation.AccuracyRequest.Scaling
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Actual count-based requests before observing a retained whole path

The actual geometry and total child count are already retained. Their
finite integral weight selects a positive common request and source stage
before the original path is observed once. The source/old comparison and
its separate global payment proof must consume these same caches later;
an existing old Spine is never retagged to this newly selected request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Nonnegative retained counts bound the exact common-request charge by its integral cost. -/
private theorem common_charge_le (children requests : Nat) (allowance endpoint : Rational)
    (nonnegative : 0 ≤ allowance) (endpointBound : endpoint ≤ allowance) :
    (5 / 2 : Rational) * (requests : Rational) * allowance +
        (97 / 8 : Rational) * (children : Rational) * endpoint +
        4 * ((children : Rational) + (requests : Rational)) * allowance ≤
      (17 * (children : Rational) + 7 * (requests : Rational)) * allowance := by
  have childrenNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le children)
  have requestsNonnegative := Cast.Order.natCast_le_direct (Nat.zero_le requests)
  have oldBound := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (5 / 2 : Rational) ≤ 3) requestsNonnegative) nonnegative
  have sourceBound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct endpointBound
    (Order.Arithmetic.mul_nonneg_direct
      (by decide +kernel : (0 : Rational) ≤ 97 / 8) childrenNonnegative)
  have sourceCoefficient := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (97 / 8 : Rational) ≤ 13) childrenNonnegative) nonnegative
  have sameRequest := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.add_le_add_direct oldBound (sourceBound.trans sourceCoefficient))
    (Order.Basic.le_refl (4 * ((children : Rational) + (requests : Rational)) * allowance))
  exact sameRequest.trans_eq (by ring1)

/-- The binary coordinate of the actual finite cost has its exact scalar polynomial. -/
private theorem cost_coordinate (children requests : Nat) :
    Aggregate.countCoordinate (2 * ((2 * children + 3 * requests) * (17 * children + 7 * requests) + 1)) =
      2 * ((2 * (children : Rational) + 3 * (requests : Rational)) *
        (17 * (children : Rational) + 7 * (requests : Rational)) + 1) := by
  rewrite [Aggregate.countCoordinate_eq]
  simp only [Cast.natCast_add_direct, Cast.natCast_mul_direct, -eq_self, -iff_self]
  have two : ((2 : Nat) : Rational) = 2 := by decide +kernel
  have three : ((3 : Nat) : Rational) = 3 := by decide +kernel
  have seven : ((7 : Nat) : Rational) = 7 := by decide +kernel
  have seventeen : ((17 : Nat) : Rational) = 17 := by decide +kernel
  have one : ((1 : Nat) : Rational) = 1 := by decide +kernel
  rewrite [two, three, seven, seventeen, one]
  rfl

/-- The actual divided request pays its retained integer cost with a strict margin. -/
private theorem cost_request_lt (target request : AccuracyRequest) (cost : Nat) (divisor : Rational)
    (divisorPositive : 0 < divisor)
    (divisorEq : divisor = 2 * (Aggregate.countCoordinate cost + 1))
    (requestEq : request = target.divide divisor divisorPositive) :
    Aggregate.countCoordinate cost * request.tolerance < target.tolerance := by
  have costNonnegative : 0 ≤ Aggregate.countCoordinate cost :=
    Eq.mpr (congrArg (fun value : Rational => 0 ≤ value) (Aggregate.countCoordinate_eq cost))
      (Cast.Order.natCast_le_direct (Nat.zero_le cost))
  have extra : 0 < Aggregate.countCoordinate cost + 2 :=
    Order.Arithmetic.add_pos_of_nonneg_of_pos_direct costNonnegative (by decide +kernel)
  have less : Aggregate.countCoordinate cost < divisor := by
    apply Order.Arithmetic.lt_of_sub_pos_direct
    exact extra.trans_eq (by rewrite [divisorEq]; ring1)
  have toleranceEq : request.tolerance = target.tolerance / divisor :=
    (congrArg AccuracyRequest.tolerance requestEq).trans (target.divide_tolerance divisor divisorPositive)
  have paid : divisor * request.tolerance = target.tolerance :=
    (Field.mul_comm divisor request.tolerance).trans
      ((congrArg (fun value : Rational => value * divisor) toleranceEq).trans
        (Field.div_mul_cancel_of_ne _ divisor divisorPositive.ne'))
  exact (Order.Arithmetic.mul_lt_mul_of_pos_right_direct less request.positive).trans_eq paid

/-- The selected common request pays the exact finite refinement charge and original closing allowance.

The actual child and old-request counts determine the supplied cost and
divisor. The original old allowance and new join allowance are the same
request selected before observation; the source endpoint allocation is
bounded internally by the selected stage. No final error bound is assumed.
-/
theorem closedCharge_lt (children requests : Nat) (target request : AccuracyRequest)
    (cost : Nat)
    (costEq : cost = 2 * ((2 * children + 3 * requests) * (17 * children + 7 * requests) + 1))
    (divisor : Rational) (divisorPositive : 0 < divisor)
    (divisorEq : divisor = 2 * (Aggregate.countCoordinate cost + 1))
    (requestEq : request = target.divide divisor divisorPositive)
    (endpoint : Rational) (endpointBound : endpoint ≤ request.tolerance) :
    2 * ((2 * (children : Rational) + 3 * (requests : Rational)) *
      ((5 / 2 : Rational) * (requests : Rational) * request.tolerance +
        (97 / 8 : Rational) * (children : Rational) * endpoint +
        4 * ((children : Rational) + (requests : Rational)) * request.tolerance) +
      request.tolerance) < target.tolerance := by
  have chargeBound := common_charge_le children requests request.tolerance endpoint request.positive.le endpointBound
  have countNonnegative : 0 ≤ 2 * (children : Rational) + 3 * (requests : Rational) :=
    (Field.zero_add (0 : Rational)).symm.trans_le
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Cast.Order.natCast_le_direct (Nat.zero_le children)))
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Cast.Order.natCast_le_direct (Nat.zero_le requests))))
  have bounded := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct chargeBound countNonnegative)
      (Order.Basic.le_refl request.tolerance)) (by decide +kernel : (0 : Rational) ≤ 2)
  have actualCost := (congrArg Aggregate.countCoordinate costEq).trans (cost_coordinate children requests)
  have scalar : 2 * ((2 * (children : Rational) + 3 * (requests : Rational)) *
      ((17 * (children : Rational) + 7 * (requests : Rational)) * request.tolerance) + request.tolerance) =
      Aggregate.countCoordinate cost * request.tolerance := by
    rewrite [actualCost]
    ring1
  exact (bounded.trans_eq scalar).trans_lt
    (cost_request_lt target request cost divisor divisorPositive divisorEq requestEq)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
variable {diameter : Rational} {positive : 0 < diameter} {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)
variable {baseStart baseFinish : LiftedPoint 2} (original : LiftedPath 2 baseStart baseFinish)

/-- The original pre-observation request prefix with its exact dependent continuation type.

Geometry, actual counts, divided request, finite stage selection and
Targets precede the continuation. This exact function-type family keeps
the retained input and factory binders shared by different observers.
-/
@[expose] def RequestFamily (target : AccuracyRequest) (stageFloor : Nat)
    (afterTargets :
      (_geometry : {value : Materialized.Geometry (count := count)
        diameter positive lineage inputCenters materialized factory // value = retained}) →
      (request : AccuracyRequest) → (selection : Search.Selection 1 stageFloor request.tolerance) →
      CellEndpoints.Targets original selection.stage → Type u) :=
  (geometry : {value : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory // value = retained}) →
  (cost : Nat) → cost = 2 * ((2 * geometry.val.childCount + 3 * prepared.stepCount) *
    (17 * geometry.val.childCount + 7 * prepared.stepCount) + 1) →
  (divisor : Rational) → divisor = 2 * (Aggregate.countCoordinate cost + 1) →
  (divisorPositive : 0 < divisor) →
  (request : AccuracyRequest) → request = target.divide divisor divisorPositive →
  (selection : Search.Selection 1 stageFloor request.tolerance) →
  selection = Search.Selection.build 1 (of_decide_eq_true rfl) stageFloor request.tolerance request.positive →
  (targets : CellEndpoints.Targets original selection.stage) →
  targets = CellEndpoints.Targets.build original selection.stage →
  targets.endpoint < request.tolerance →
  afterTargets geometry request selection targets

/-- The complete actual pre-observation requests, source stage and Targets, with their original factories. -/
@[expose] def RequestConsumer (target : AccuracyRequest) (stageFloor : Nat) (Result : Type u) :=
  RequestFamily retained original target stageFloor (fun _geometry _request _selection _targets => Result)

/-- Actual whole geometry, count-based request, source-stage selection and one new old-path observation.

The final callback receives the same original observed Spine and complete
factory. Its applied type is the original telescope, specialized from the
shared request prefix without changing any retained binder or owner.
-/
@[expose] def ObservationConsumer (row : Row) (target : AccuracyRequest) (stageFloor : Nat) (Result : Type u) :=
  RequestFamily retained original target stageFloor (fun geometry request _selection _targets =>
    (observed : Primitive.Spine (row.expression parameter) request geometry.val.path) →
    observed = Primitive.Spine.build (expression := row.expression parameter) (accuracy := request)
      geometry.val.path (Trace.defined row geometry.val.path) → Result)

/-- Select the actual count-paid request and Targets before any primitive observation.

The original cost, positivity proof, request division, finite stage search
and target selection execute once in their original order. The supplied
whole geometry and its actual child count remain the same retained data.
-/
def withRequests (target : AccuracyRequest) (stageFloor : Nat) {Result : Type u}
    (consume : RequestConsumer retained original target stageFloor Result) : Result :=
  let geometry : {value : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory // value = retained} := ⟨retained, rfl⟩
  let cost := 2 * ((2 * geometry.val.childCount + 3 * prepared.stepCount) *
    (17 * geometry.val.childCount + 7 * prepared.stepCount) + 1)
  let divisor := 2 * (Aggregate.countCoordinate cost + 1)
  have costNonnegative : 0 ≤ Aggregate.countCoordinate cost :=
    Eq.mpr (congrArg (fun value : Rational => 0 ≤ value) (Aggregate.countCoordinate_eq cost))
      (Cast.Order.natCast_le_direct (Nat.zero_le cost))
  have divisorPositive : 0 < divisor := Order.Arithmetic.mul_pos_direct (of_decide_eq_true rfl)
    (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct costNonnegative (of_decide_eq_true rfl))
  let request := target.divide divisor divisorPositive
  let selection := Search.Selection.build 1 (of_decide_eq_true rfl)
    stageFloor request.tolerance request.positive
  let targets := CellEndpoints.Targets.build original selection.stage
  have endpoint : targets.endpoint < request.tolerance :=
    (targets.endpoint_eq.trans_le targets.localBound_le_quarterRadius).trans_lt
      (selection.allowance_eq.symm.trans_lt selection.accurate)
  consume geometry cost rfl divisor rfl divisorPositive request rfl selection rfl targets rfl endpoint

/-- Select actual count-based old/new requests before observing the same retained original path once.

The shared request prefix preserves its original order and all selected
caches. The same old Spine is observed only afterward; an independently
supplied old observation is never retagged to this request.
-/
def withObservation (row : Row) (target : AccuracyRequest) (stageFloor : Nat) {Result : Type u}
    (consume : ObservationConsumer retained original row target stageFloor Result) : Result :=
  withRequests retained original target stageFloor
    (fun geometry cost costEq divisor divisorEq divisorPositive request requestEq
        selection selectionEq targets targetsEq endpoint =>
      let observed := Primitive.Spine.build (expression := row.expression parameter) (accuracy := request)
        geometry.val.path (Trace.defined row geometry.val.path)
      consume geometry cost costEq divisor divisorEq divisorPositive request requestEq
        selection selectionEq targets targetsEq endpoint observed rfl)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
