module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Requests
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Comparison
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Primitive
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Charge
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Requested source-row payment on the same root-closed geometry

The actual given-geometry completion and genuine closing comparison retain
the same original old Spine and Owner endpoints. Pre-observation count and
request factories pay the exact source sum; no desired final inequality,
reading equality, period-model identification or matrix action is input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable {owner : Owner ((Paths.polynomial parameter).eval base)} (closed : RootClosedWalk grid base owner)
variable {diameter : Rational} {positive : 0 < diameter}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}

namespace Paid

/-- The actual same-bank completion and its complete given-geometry execution factory. -/
@[expose] def Completion
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (observed : Primitive.Spine (row.expression parameter) request geometry.path) :=
  {value : Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed //
    value = Cache.fromGeometry (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers
      geometry.path (geometry.path_eq.trans factory) geometry.cache observed}

/-- Read the actual source-row integral sum from the retained given-geometry completion. -/
@[expose] def integral
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (observed : Primitive.Spine (row.expression parameter) request geometry.path)
    (completed : Completion (floor := floor) closed geometry row request targets observed) : Canonical :=
  gaussianSum (Cache.integrals (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers completed.val.val)

/-- The original residual-count cast preserves both literal natural factors. -/
private theorem count_cast (children requests : Nat) :
    ((2 * children + 3 * requests : Nat) : Rational) = 2 * (children : Rational) + 3 * (requests : Rational) :=
  (Cast.natCast_add_direct (2 * children) (3 * requests)).trans
    (congrArg₂ (fun first last : Rational => first + last)
      (Cast.natCast_mul_direct 2 children) (Cast.natCast_mul_direct 3 requests))

/-- The SAME actual completion and genuine closing comparison pay a preselected request at their derived child count.

All source, old-observation and comparison allowances remain those of the
given completion. The actual M readback links this bank to its original
pre-observation allocation; no whole builder equality or desired final
inequality is required.
-/
theorem integral_lt_of_count
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest)
    (cost : Nat)
    (costEq : cost = 2 * ((2 * geometry.childCount + 3 * closed.traced.prepared.stepCount) *
      (17 * geometry.childCount + 7 * closed.traced.prepared.stepCount) + 1))
    (divisor : Rational) (divisorPositive : 0 < divisor)
    (divisorEq : divisor = 2 * (Approximation.Rational.Budget.Aggregate.countCoordinate cost + 1))
    (requestEq : request = target.divide divisor divisorPositive)
    (targets : CellEndpoints.Targets original stage) (endpointBound : targets.endpoint ≤ request.tolerance)
    (observed : Primitive.Spine (row.expression parameter) request geometry.path)
    (completed : Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed)
    (childrenEq : Cache.childCount (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers completed.val = geometry.childCount)
    {join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner}
    (closing : Primitive.Closing.Comparison observed join) :
    Norm.Basic.normSq (gaussianSum (Cache.integrals
      (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers completed.val)) <
      target.tolerance := by
  have chargeEq := (Cache.charge_eq (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers completed.val).trans
    (congrArg (fun children : Nat =>
      (5 / 2 : Rational) * (closed.traced.prepared.stepCount : Rational) * request.tolerance +
      (97 / 8 : Rational) * (children : Rational) * targets.endpoint +
      4 * ((children : Rational) + (closed.traced.prepared.stepCount : Rational)) * request.tolerance) childrenEq)
  have countEq := (Cache.residualCount_eq (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers completed.val).trans
    (congrArg₂ (fun children requests : Nat => 2 * children + 3 * requests) childrenEq
      (Trace.Materialized.Sources.requestCount_eq_stepCount closed.traced.lineage))
  have rationalCount := (congrArg (fun value : Nat => (value : Rational)) countEq).trans
    (count_cast geometry.childCount closed.traced.prepared.stepCount)
  have residual := Cache.Completion.integral_error_le (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := request)
    (row := row) (diameter := diameter) (positive := positive) (request := request)
    (lineage := closed.traced.lineage) (inputCenters := geometry.centers) (materialized := geometry.path)
    (observed := observed) completed
  have returned := closing.integral_le_return_residual
    (gaussianSum (Cache.integrals (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers completed.val))
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct residual (Order.Basic.le_refl request.tolerance))
    (of_decide_eq_true rfl : (0 : Rational) ≤ 2)
  have exactCharge := congrArg₂ (fun length charge : Rational => 2 * (length * charge + request.tolerance))
    rationalCount chargeEq
  have requested := Materialized.Geometry.closedCharge_lt geometry.childCount closed.traced.prepared.stepCount
    target request cost costEq divisor divisorPositive divisorEq requestEq targets.endpoint endpointBound
  exact ((returned.trans paid).trans_eq exactCharge).trans_lt requested

/-- The actual completion and closing comparison meet the request selected before the same old observations.

Count preservation, exact old/source/join charges and the original return
residual inequality are composed internally. Both old and new comparison
allowances are the same actual request from the supplied cost/divisor
factory; the source endpoint bound is the original selected-stage payment.
-/
theorem integral_lt
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest)
    (cost : Nat)
    (costEq : cost = 2 * ((2 * geometry.childCount + 3 * closed.traced.prepared.stepCount) *
      (17 * geometry.childCount + 7 * closed.traced.prepared.stepCount) + 1))
    (divisor : Rational) (divisorPositive : 0 < divisor)
    (divisorEq : divisor = 2 * (Approximation.Rational.Budget.Aggregate.countCoordinate cost + 1))
    (requestEq : request = target.divide divisor divisorPositive)
    (targets : CellEndpoints.Targets original stage) (endpointBound : targets.endpoint ≤ request.tolerance)
    (observed : Primitive.Spine (row.expression parameter) request geometry.path)
    (completed : Completion (floor := floor) closed geometry row request targets observed)
    {join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner}
    (closing : Primitive.Closing.Comparison observed join) :
    Norm.Basic.normSq (integral (floor := floor) closed geometry row request targets observed completed) <
      target.tolerance := by
  let actualChildren := Cache.childCount (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers completed.val.val
  have executionCount := congrArg (fun actual : Cache.Completion (count := count) (floor := floor)
      (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed =>
    Cache.childCount (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers actual.val) completed.property
  have givenCount := Cache.fromGeometry_childCount (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers
    geometry.path (geometry.path_eq.trans factory) geometry.cache observed
  have childrenEq : actualChildren = geometry.childCount :=
    executionCount.trans (givenCount.trans geometry.childCount_eq.symm)
  exact integral_lt_of_count (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) closed geometry row target request cost costEq
    divisor divisorPositive divisorEq requestEq targets endpointBound observed completed.val childrenEq closing

end Paid

/-- The actual closed source-row construction with its pre-observation allocation and strict requested payment.

The same initial Owner, closed walk, target, whole geometry, stage targets,
old Spine and completed numerical source bank are retained as data. The
closing joins and comparison preserve their complete original factories.
Old observations and joins use the actual count-selected request; no old
reading or source cache is retagged. The final invariant pays this source integral sum.
-/
@[expose] def Paid
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish)
    (row : Row) (target : AccuracyRequest) (stageFloor : Nat) :=
  {value : Owner ((Paths.polynomial parameter).eval base) // value = owner} ×
  {value : RootClosedWalk grid base owner // value = closed} ×
  {value : AccuracyRequest // value = target} ×
  {value : LiftedPath 2 baseStart baseFinish // value = source} ×
  Σ geometry : {value : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory // value = retained},
  Σ cost : {value : Nat // value = 2 * ((2 * geometry.val.childCount + 3 * closed.traced.prepared.stepCount) *
      (17 * geometry.val.childCount + 7 * closed.traced.prepared.stepCount) + 1)},
  Σ divisor : {value : Rational //
      value = 2 * (Approximation.Rational.Budget.Aggregate.countCoordinate cost.val + 1) ∧ 0 < value},
  Σ request : {value : AccuracyRequest // value = target.divide divisor.val divisor.property.2},
  Σ selection : {value : Search.Selection 1 stageFloor request.val.tolerance //
      value = Search.Selection.build 1 (of_decide_eq_true rfl)
        stageFloor request.val.tolerance request.val.positive},
  Σ targets : {value : CellEndpoints.Targets source selection.val.stage //
      value = CellEndpoints.Targets.build source selection.val.stage ∧ value.endpoint < request.val.tolerance},
  Σ observed : {value : Primitive.Spine (row.expression parameter) request.val geometry.val.path //
      value = Primitive.Spine.build (expression := row.expression parameter) (accuracy := request.val)
        geometry.val.path (Trace.defined row geometry.val.path)},
  Σ completed : Paid.Completion (floor := floor) closed geometry.val row request.val targets.val observed.val,
  Σ returning : {value : OwnerJoin closed.traced.finishOwner owner //
      value = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn},
  Σ join : {value : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner //
      value = Eq.mp (congrArg (fun terminal : Owner ((Paths.polynomial parameter).eval base) =>
        OwnerJoin terminal owner) closed.traced.finishOwner_eq) returning.val},
  (_closing : {value : Primitive.Closing.Comparison observed.val join.val //
      value = Primitive.Closing.Comparison.build observed.val join.val}) ×
    PLift (Norm.Basic.normSq
      (Paid.integral (floor := floor) closed geometry.val row request.val targets.val observed.val completed) <
        target.tolerance)

namespace Paid

/-- Consume one original whole-path observation, compare its given geometry and acquire its genuine closing comparison.

The existing ObservationConsumer owns the callback telescope. Every
certified cache is bound before its dependent continuation or payload;
the given-geometry source fold and original closing producer each execute
once. Count and charge laws derive the requested bound internally.
-/
private def attach
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish)
    (row : Row) (target : AccuracyRequest) (stageFloor : Nat) :
    ObservationConsumer retained source row target stageFloor
      (Paid (floor := floor) closed retained source row target stageFloor) :=
  fun geometry cost costEq divisor divisorEq divisorPositive request requestEq
      selection selectionEq targets targetsEq endpoint observed observedEq =>
    let keptCost : {value : Nat // value = 2 * ((2 * geometry.val.childCount +
        3 * closed.traced.prepared.stepCount) *
        (17 * geometry.val.childCount + 7 * closed.traced.prepared.stepCount) + 1)} := ⟨cost, costEq⟩
    let keptDivisor : {value : Rational //
        value = 2 * (Approximation.Rational.Budget.Aggregate.countCoordinate keptCost.val + 1) ∧ 0 < value} :=
      ⟨divisor, divisorEq, divisorPositive⟩
    let keptRequest : {value : AccuracyRequest // value = target.divide keptDivisor.val keptDivisor.property.2} :=
      ⟨request, requestEq⟩
    let keptSelection : {value : Search.Selection 1 stageFloor keptRequest.val.tolerance //
        value = Search.Selection.build 1 (of_decide_eq_true rfl)
          stageFloor keptRequest.val.tolerance keptRequest.val.positive} := ⟨selection, selectionEq⟩
    let keptTargets : {value : CellEndpoints.Targets source keptSelection.val.stage //
        value = CellEndpoints.Targets.build source keptSelection.val.stage ∧
          value.endpoint < keptRequest.val.tolerance} := ⟨targets, targetsEq, endpoint⟩
    let keptObserved : {value : Primitive.Spine (row.expression parameter) keptRequest.val geometry.val.path //
        value = Primitive.Spine.build (expression := row.expression parameter) (accuracy := keptRequest.val)
          geometry.val.path (Trace.defined row geometry.val.path)} := ⟨observed, observedEq⟩
    let completed : Completion (floor := floor) closed geometry.val row keptRequest.val
        keptTargets.val keptObserved.val :=
      ⟨Cache.fromGeometry (frame := frame) (basis := basis) (sheet := sheet)
        (count := count) (floor := floor) (targets := keptTargets.val) (accuracy := keptRequest.val)
        row diameter positive keptRequest.val closed.traced.lineage geometry.val.centers
        geometry.val.path (geometry.val.path_eq.trans factory) geometry.val.cache keptObserved.val, rfl⟩
    closed.withClosing geometry.val.path keptObserved.val
      (fun returning returningEq join joinEq closing closingEq =>
        let keptReturning : {value : OwnerJoin closed.traced.finishOwner owner //
            value = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn} := ⟨returning, returningEq⟩
        let keptJoin : {value : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner //
            value = Eq.mp (congrArg (fun terminal : Owner ((Paths.polynomial parameter).eval base) =>
              OwnerJoin terminal owner) closed.traced.finishOwner_eq) keptReturning.val} := ⟨join, joinEq⟩
        let keptClosing : {value : Primitive.Closing.Comparison keptObserved.val keptJoin.val //
            value = Primitive.Closing.Comparison.build keptObserved.val keptJoin.val} := ⟨closing, closingEq⟩
        have paid := integral_lt (frame := frame) (basis := basis) (sheet := sheet)
          (count := count) (floor := floor) closed geometry.val row target keptRequest.val
          keptCost.val keptCost.property keptDivisor.val keptDivisor.property.2 keptDivisor.property.1
          keptRequest.property keptTargets.val keptTargets.property.2.le keptObserved.val completed keptClosing.val
        ⟨⟨owner, rfl⟩, ⟨closed, rfl⟩, ⟨target, rfl⟩, ⟨source, rfl⟩, geometry, keptCost, keptDivisor, keptRequest,
          keptSelection, keptTargets, keptObserved, completed, keptReturning, keptJoin, keptClosing, ⟨paid⟩⟩)

/-- Pay the actual closed source-row integral sum using requests chosen before the same path is observed.

The complete geometry already exists. Its stored count selects the source
stage and the shared old/new allowance through the original observer;
the supplied original closed walk then supplies the genuine return join.
No materialized path, geometry bank, source query or old observation is
rebuilt to recover an owner or a count.
-/
def build
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish)
    (row : Row) (target : AccuracyRequest) (stageFloor : Nat) :
    Paid (floor := floor) closed retained source row target stageFloor :=
  retained.withObservation source row target stageFloor
    (attach (floor := floor) closed retained source row target stageFloor)

/-- Read the actual selected source integral sum whose retained closed comparison pays the request. -/
@[expose] def value
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {row : Row} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Paid (floor := floor) closed retained source row target stageFloor) : Canonical :=
  let geometryData := retainedPaid.2.2.2.2
  let geometry := geometryData.1
  let costData := geometryData.2
  let divisorData := costData.2
  let requestData := divisorData.2
  let request := requestData.1
  let selectionData := requestData.2
  let targetsData := selectionData.2
  let targets := targetsData.1
  let observedData := targetsData.2
  let observed := observedData.1
  let completed := observedData.2.1
  integral (floor := floor) closed geometry.val row request.val targets.val observed.val completed

/-- The retained complete construction pays its literal source integral sum by the original requested tolerance. -/
theorem value_lt
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {row : Row} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Paid (floor := floor) closed retained source row target stageFloor) :
    Norm.Basic.normSq (value (floor := floor) closed retainedPaid) < target.tolerance := by
  exact retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.down

end Paid

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry

end
