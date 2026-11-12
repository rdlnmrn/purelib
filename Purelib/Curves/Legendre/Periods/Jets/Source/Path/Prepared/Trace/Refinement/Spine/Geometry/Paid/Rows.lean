module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Paid
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Integrals
import Purelib.Data.Fin.Two

/-! # Three requested closed rows on ONE actual retained six-channel source bank

The original request prefix chooses common Targets before this whole bank
is prepared. Only afterward are the three independent original Spines
observed. Their given-bank completions and genuine return comparisons
pay all three literal source-row sums without a Stage/jet equality premise.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry.Paid

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive
open Materialized.Geometry renaming Sources -> MaterializedSources
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
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

namespace Rows

/-- One actual original row observation and its complete request/path factory on the SAME retained old path. -/
@[expose] def Observation
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (request : AccuracyRequest) :=
  {value : Primitive.Spine (row.expression parameter) request geometry.path //
    value = Primitive.Spine.build (expression := row.expression parameter) (accuracy := request)
      geometry.path (Trace.defined row geometry.path)}

namespace Observation

/-- Observe one original row on the retained path with its complete construction factory. -/
def build
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (request : AccuracyRequest) : Observation closed geometry row request :=
  ⟨Primitive.Spine.build (expression := row.expression parameter) (accuracy := request)
    geometry.path (Trace.defined row geometry.path), rfl⟩

end Observation

/-- One existing whole Completion and its actual GIVEN-bank execution factory on the same original row observation. -/
@[expose] def Completion
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (sourceBank : MaterializedSources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : Observation closed geometry row request) :=
  {value : Cache.Completion (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed.val //
    value = Cache.fromSources (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers
      geometry.path (geometry.path_eq.trans factory) geometry.cache sourceBank observed.val}

/-- One given-bank row completion, its actual closing comparison and its strict requested source-sum payment. -/
@[expose] def Payment
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (sourceBank : MaterializedSources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : Observation closed geometry row request)
    (join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner) :=
  Σ completed : Completion (floor := floor) closed geometry row request targets sourceBank observed,
  (_closing : {value : Closing.Comparison observed.val join //
    value = Closing.Comparison.build observed.val join}) ×
  PLift (Norm.Basic.normSq (gaussianSum (Cache.integrals
    (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers completed.val.val)) < target.tolerance)

/-- Pay one actual row completion from its SAME bank count and genuine supplied closing comparison.

The count follows from the retained completion's whole execution factory
and the pre-observation geometry. The finite charge and closing comparison
pay the literal integral sum; no desired numerical inequality is input.
-/
private def pay
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest) (cost : Nat)
    (costEq : cost = 2 * ((2 * geometry.childCount + 3 * closed.traced.prepared.stepCount) *
      (17 * geometry.childCount + 7 * closed.traced.prepared.stepCount) + 1))
    (divisor : Rational) (divisorPositive : 0 < divisor)
    (divisorEq : divisor = 2 * (Approximation.Rational.Budget.Aggregate.countCoordinate cost + 1))
    (requestEq : request = target.divide divisor divisorPositive)
    (targets : CellEndpoints.Targets original stage) (endpointBound : targets.endpoint ≤ request.tolerance)
    (sourceBank : MaterializedSources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : Observation closed geometry row request)
    (completed : Completion (floor := floor) closed geometry row request targets sourceBank observed)
    {join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner}
    (closing : {value : Closing.Comparison observed.val join //
      value = Closing.Comparison.build observed.val join}) :
    Payment (floor := floor) closed geometry row target request targets sourceBank observed join := by
  have executionCount := congrArg (fun actual : Cache.Completion
      (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed.val =>
    Cache.childCount (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers actual.val) completed.property
  have sourceCount := Materialized.Geometry.fromSources_childCount
    (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor)
    (targets := targets) (accuracy := request) geometry row request sourceBank observed.val
  have bound := Paid.integral_lt_of_count (frame := frame) (basis := basis) (sheet := sheet)
    (count := count) (floor := floor) closed geometry row target request cost costEq
    divisor divisorPositive divisorEq requestEq targets endpointBound observed.val
    completed.val (executionCount.trans sourceCount) closing.val
  exact ⟨completed, closing, ⟨bound⟩⟩

namespace Payment

/-- Read the literal integral sum stored in this paid row's retained completion. -/
@[expose] def value
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (sourceBank : MaterializedSources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : Observation closed geometry row request)
    (join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner)
    (payment : Payment (floor := floor) closed geometry row target request targets sourceBank observed join) :
    Canonical :=
  gaussianSum (Cache.integrals (count := count) (floor := floor) (targets := targets) (accuracy := request)
    row diameter positive request closed.traced.lineage geometry.centers payment.1.val.val)

/-- The SAME paid completion reads the exact original linear combination of its own six numerical models.

Only the whole retained completion factory, original same-bank list
readback and exact ordered source algebra are used. No period model,
jet attachment or desired numerical comparison is an input.
-/
theorem combine_eq
    (geometry : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (row : Row) (target request : AccuracyRequest) (targets : CellEndpoints.Targets original stage)
    (sourceBank : MaterializedSources (count := count) (floor := floor) (targets := targets) geometry)
    (observed : Observation closed geometry row request)
    (join : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner)
    (payment : Payment (floor := floor) closed geometry row target request targets sourceBank observed join) :
    gaussianSum (Cache.integrals (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers payment.1.val.val) =
      Row.combine parameter row (fun channel =>
        (MaterializedSources.model (count := count) (floor := floor) (targets := targets)
          geometry sourceBank channel).integralSample) := by
  have execution := congrArg (fun actual : Cache.Completion
      (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers geometry.path observed.val =>
    gaussianSum (Cache.integrals (count := count) (floor := floor) (targets := targets) (accuracy := request)
      row diameter positive request closed.traced.lineage geometry.centers actual.val)) payment.1.property
  have read := congrArg gaussianSum (Cache.fromSources_integrals
    (frame := frame) (basis := basis) (sheet := sheet) (count := count) (floor := floor)
    (targets := targets) (accuracy := request) row diameter positive request
    closed.traced.lineage geometry.centers geometry.path (geometry.path_eq.trans factory)
    geometry.cache sourceBank observed.val)
  have combined := MaterializedSources.combine_eq
    (count := count) (floor := floor) (targets := targets) geometry sourceBank row
  exact execution.trans (read.trans combined)

end Payment

end Rows

/-- All three strictly paid closed source rows share ONE actual complete six-channel numerical bank.

The original inputs, pre-observation request factories, original whole
geometry, actual source bank and three independent old Spine observations
are retained as data. One genuine original return join supplies the three
separate closing comparisons; no old-reading equality is asserted.
-/
@[expose] def Rows
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish) (target : AccuracyRequest) (stageFloor : Nat) :=
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
  Σ sourceBank : {value : MaterializedSources
      (count := count) (floor := floor) (targets := targets.val) geometry.val //
    value = MaterializedSources.build
      (count := count) (floor := floor) (targets := targets.val) geometry.val},
  Σ zero : Rows.Observation closed geometry.val (Row.connection 0) request.val,
  Σ one : Rows.Observation closed geometry.val (Row.connection 1) request.val,
  Σ scalar : Rows.Observation closed geometry.val Row.scalar request.val,
  Σ returning : {value : OwnerJoin closed.traced.finishOwner owner //
      value = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn},
  Σ join : {value : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner //
      value = Eq.mp (congrArg (fun terminal : Owner ((Paths.polynomial parameter).eval base) =>
        OwnerJoin terminal owner) closed.traced.finishOwner_eq) returning.val},
  Rows.Payment (floor := floor) closed geometry.val (Row.connection 0) target request.val targets.val
      sourceBank.val zero join.val ×
    Rows.Payment (floor := floor) closed geometry.val (Row.connection 1) target request.val targets.val
      sourceBank.val one join.val ×
    Rows.Payment (floor := floor) closed geometry.val Row.scalar target request.val targets.val
      sourceBank.val scalar join.val

namespace Rows

/-- Retain the common pre-observation prefix, one bank, three old Spines and their actual paid completions.

The existing RequestConsumer owns the complete callback telescope. Whole
certified caches are bound before dependent computations, preserving the
same cached inputs and every original factory.
-/
private def attach
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish) (target : AccuracyRequest) (stageFloor : Nat) :
    RequestConsumer retained source target stageFloor
      (Rows (floor := floor) closed retained source target stageFloor) :=
  fun geometry cost costEq divisor divisorEq divisorPositive request requestEq
      selection selectionEq targets targetsEq endpoint =>
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
    let sourceBank : {value : MaterializedSources
        (count := count) (floor := floor) (targets := keptTargets.val) geometry.val //
      value = MaterializedSources.build
        (count := count) (floor := floor) (targets := keptTargets.val) geometry.val} :=
      ⟨MaterializedSources.build
        (count := count) (floor := floor) (targets := keptTargets.val) geometry.val, rfl⟩
    let zero := Observation.build closed geometry.val (Row.connection 0) keptRequest.val
    let one := Observation.build closed geometry.val (Row.connection 1) keptRequest.val
    let scalar := Observation.build closed geometry.val Row.scalar keptRequest.val
    let observations : (row : Row) → Primitive.Spine (row.expression parameter) keptRequest.val geometry.val.path :=
      fun row => match row with
        | .inl coordinate => Fin.cases zero.val (fun _ => one.val) coordinate
        | .inr _ => scalar.val
    let completed := Materialized.Geometry.rowsFromSources
      (count := count) (floor := floor) (targets := keptTargets.val) (accuracy := keptRequest.val)
      geometry.val keptRequest.val sourceBank.val observations
    have completedFactory := Materialized.Geometry.rowsFromSources_eq
      (count := count) (floor := floor) (targets := keptTargets.val) (accuracy := keptRequest.val)
      geometry.val keptRequest.val sourceBank.val observations
    let zeroCompleted : Completion (floor := floor) closed geometry.val (Row.connection 0) keptRequest.val
        keptTargets.val sourceBank.val zero := ⟨completed.1, congrArg Prod.fst completedFactory⟩
    let oneCompleted : Completion (floor := floor) closed geometry.val (Row.connection 1) keptRequest.val
        keptTargets.val sourceBank.val one :=
      ⟨completed.2.1, congrArg Prod.fst (congrArg Prod.snd completedFactory)⟩
    let scalarCompleted : Completion (floor := floor) closed geometry.val Row.scalar keptRequest.val
        keptTargets.val sourceBank.val scalar :=
      ⟨completed.2.2, congrArg Prod.snd (congrArg Prod.snd completedFactory)⟩
    closed.withClosing geometry.val.path zero.val
      (fun returning returningEq join joinEq compared comparedEq =>
        let keptReturning : {value : OwnerJoin closed.traced.finishOwner owner //
            value = OwnerJoin.acquire closed.traced.finishOwner owner closed.rootReturn} := ⟨returning, returningEq⟩
        let keptJoin : {value : OwnerJoin (PreparedPathGluing.finishOwner closed.traced.prepared) owner //
            value = Eq.mp (congrArg (fun terminal : Owner ((Paths.polynomial parameter).eval base) =>
              OwnerJoin terminal owner) closed.traced.finishOwner_eq) keptReturning.val} := ⟨join, joinEq⟩
        let zeroClosing : {value : Closing.Comparison zero.val keptJoin.val //
            value = Closing.Comparison.build zero.val keptJoin.val} := ⟨compared, comparedEq⟩
        let oneClosing : {value : Closing.Comparison one.val keptJoin.val //
            value = Closing.Comparison.build one.val keptJoin.val} :=
          ⟨Closing.Comparison.build one.val keptJoin.val, rfl⟩
        let scalarClosing : {value : Closing.Comparison scalar.val keptJoin.val //
            value = Closing.Comparison.build scalar.val keptJoin.val} :=
          ⟨Closing.Comparison.build scalar.val keptJoin.val, rfl⟩
        let zeroPaid := pay (floor := floor) closed geometry.val (Row.connection 0) target keptRequest.val
          keptCost.val keptCost.property keptDivisor.val keptDivisor.property.2 keptDivisor.property.1
          keptRequest.property keptTargets.val keptTargets.property.2.le sourceBank.val zero zeroCompleted zeroClosing
        let onePaid := pay (floor := floor) closed geometry.val (Row.connection 1) target keptRequest.val
          keptCost.val keptCost.property keptDivisor.val keptDivisor.property.2 keptDivisor.property.1
          keptRequest.property keptTargets.val keptTargets.property.2.le sourceBank.val one oneCompleted oneClosing
        let scalarPaid := pay (floor := floor) closed geometry.val Row.scalar target keptRequest.val
          keptCost.val keptCost.property keptDivisor.val keptDivisor.property.2 keptDivisor.property.1
          keptRequest.property keptTargets.val keptTargets.property.2.le
          sourceBank.val scalar scalarCompleted scalarClosing
        ⟨⟨owner, rfl⟩, ⟨closed, rfl⟩, ⟨target, rfl⟩, ⟨source, rfl⟩, geometry,
          keptCost, keptDivisor, keptRequest, keptSelection, keptTargets, sourceBank,
          zero, one, scalar, keptReturning, keptJoin, zeroPaid, onePaid, scalarPaid⟩)

/-- Pay all three closed source-row sums on ONE bank, with common allocation before every observation.

The original request prefix executes once. The whole bank is prepared
once next; only then are three independent old Spines observed and their
same-bank completions built once. One genuine root-return OwnerJoin and
three actual closing comparisons pay all three retained integral sums.
-/
def build
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory)
    (source : LiftedPath 2 baseStart baseFinish) (target : AccuracyRequest) (stageFloor : Nat) :
    Rows (floor := floor) closed retained source target stageFloor :=
  retained.withRequests source target stageFloor
    (attach (floor := floor) closed retained source target stageFloor)

/-- Read the actual paid source-row integral sum from its retained completion on the SAME bank. -/
@[expose] def value
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Rows (floor := floor) closed retained source target stageFloor) (row : Row) : Canonical :=
  Sum.elim
    (fun coordinate => Fin.cases
      (Payment.value (floor := floor) closed
        retainedPaid.2.2.2.2.1.val (Row.connection 0) target retainedPaid.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.1.val retainedPaid.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.1 retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ => Payment.value (floor := floor) closed
        retainedPaid.2.2.2.2.1.val (Row.connection 1) target retainedPaid.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.1.val retainedPaid.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.1 retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) coordinate)
    (fun _ => Payment.value (floor := floor) closed
        retainedPaid.2.2.2.2.1.val Row.scalar target retainedPaid.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.1.val retainedPaid.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.1 retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val
        retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) row

/-- Every actual retained closed row integral sum meets the original requested tolerance. -/
theorem value_lt
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Rows (floor := floor) closed retained source target stageFloor) (row : Row) :
    Norm.Basic.normSq (value (floor := floor) closed retainedPaid row) < target.tolerance := by
  let payments := retainedPaid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  cases row with
  | inl coordinate => exact Fin.cases payments.1.2.2.down (fun _ => payments.2.1.2.2.down) coordinate
  | inr _ => exact payments.2.2.2.2.down

/-- Read one literal six-program source model from the SAME whole bank retained by all three paid rows. -/
@[expose] def model
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Rows (floor := floor) closed retained source target stageFloor) (channel : Fin 6) : PathModel :=
  let geometryData := retainedPaid.2.2.2.2
  let geometry := geometryData.1
  let targetsData := geometryData.2.2.2.2.2
  let targets := targetsData.1
  let sourceBank := targetsData.2.1
  MaterializedSources.model (count := count) (floor := floor) (targets := targets.val)
    geometry.val sourceBank.val channel

/-- Each actual paid row is the exact original coefficient combination of the SAME retained six source models.

Both original connection coordinates and the scalar row read their own
actual completion. No equality to an independent jet, cycle or existing
programme family is assumed by this numerical source-bank readback.
-/
theorem combine_eq
    {retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory}
    {source : LiftedPath 2 baseStart baseFinish} {target : AccuracyRequest} {stageFloor : Nat}
    (retainedPaid : Rows (floor := floor) closed retained source target stageFloor) (row : Row) :
    value (floor := floor) closed retainedPaid row =
      Row.combine parameter row (fun channel =>
        (model (floor := floor) closed retainedPaid channel).integralSample) := by
  let geometryData := retainedPaid.2.2.2.2
  let geometry := geometryData.1
  let requestData := geometryData.2.2.2
  let request := requestData.1
  let targetsData := requestData.2.2
  let targets := targetsData.1
  let sourceData := targetsData.2
  let sourceBank := sourceData.1
  let zeroData := sourceData.2
  let oneData := zeroData.2
  let scalarData := oneData.2
  let joinData := scalarData.2.2
  let payments := joinData.2
  cases row with
  | inl coordinate =>
      rcases Data.Fin.Two.finTwo_cases coordinate with zeroCase | oneCase
      · cases zeroCase
        exact Payment.combine_eq (floor := floor) closed geometry.val (Row.connection 0) target request.val
          targets.val sourceBank.val zeroData.1 joinData.1.val payments.1
      · cases oneCase
        exact Payment.combine_eq (floor := floor) closed geometry.val (Row.connection 1) target request.val
          targets.val sourceBank.val oneData.1 joinData.1.val payments.2.1
  | inr _ =>
      exact Payment.combine_eq (floor := floor) closed geometry.val Row.scalar target request.val
        targets.val sourceBank.val scalarData.1 joinData.1.val payments.2.2

end Rows

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized.Geometry.Paid

end
