module

import Purelib.Data.Sigma.Factories

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries.Preparation
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion

/-! # One completed common source and actual completed positive-node table

The same original fine Completion supplies both its actual Completed family
and genuine signed all-query agreement. One sufficient member becomes the
common numerical source without a second attempt. Signed original-parent
comparisons derive agreement on that member's own preparation before any
node or target completion. Original positive-node/table factories then
construct all literal outgoing target completions and their own families.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data.Gaussian

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Steps.Acquisition

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation

namespace Requested

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}

/-- The original sufficient Requested/completed-member result type on this SAME fine covered geometry. -/
@[expose] def CommonSource
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (commonCurrent : Nat) (commonAccuracy : AccuracyRequest) :=
  (paid : PreparedParents.StageAttempt.Requested requested.covered requested.chain
    (max commonCurrent (requested.requested.selected.stage + 1)) freshFloor rootStage commonAccuracy) ×
  { member : PreparedParents.StageAttempt.Completed requested.covered requested.chain paid.selected.stage
      freshFloor rootStage // member.1 = paid.attempt }

namespace FineCompletion

variable (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

/-- One original sufficient common source, its genuine queries, actual node table and literal target completions.

Existing Sigma/Subtype containers retain whole original factories and all
actual caches. The old fine observations are used only for signed agreement;
new numerical allowances/readings belong to the sufficient common member.
No target Completion, all-query callback or desired sample relation is an
input. Node zero and stationary/canonical attachments remain separate.
-/
@[expose] def PositiveTable
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    :=
  let commonAccuracy := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
    (Sampling.gridIncrement_nonzero intervals positive direction moving))
  (oldQueries : { value : PreparedParents.QueryAgreement requested.attempt.2.1 //
    value = completed.queries firstTen secondTen thirdTen fourthTen }) ×
  (common : { value : CommonSource (requested := requested) commonCurrent commonAccuracy //
    value = PreparedParents.StageAttempt.Completed.requested requested.covered requested.chain
      (⟨requested.attempt, completed.completion⟩ : PreparedParents.StageAttempt.Completed
        requested.covered requested.chain requested.requested.selected.stage freshFloor rootStage)
      requested.requested.attempt_eq commonCurrent commonAccuracy }) ×
  (queries : { value : PreparedParents.QueryAgreement common.val.1.prepared //
    value = PreparedParents.QueryAgreement.reprepare requested.attempt.2.1 common.val.1.prepared oldQueries.val }) ×
  (table : { value : PositiveGridNode.Table intervals positive direction moving spatial common.val.1 common.val.2
      ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage //
    value = PositiveGridNode.Table.build intervals positive direction moving spatial common.val.1 common.val.2
      ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage }) ×
  { completions : PositiveGridNode.Table.Completions table.val queries.val //
    completions = PositiveGridNode.Table.Completions.build table.val queries.val }

/-- Build one original common source/member, derive its query agreement and complete the SAME stored target table.

Exactly one sufficient source-family member executes. The original
Requested.ofRetained packages that same attempt. Each target node executes
once, then its original completion consumes its own old checks/Commons and
acquires only unpaid endpoint work. No incoming selected cache is replaced.
-/
def positiveTable
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction
    moving spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage :=
  let commonAccuracy := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
    (Sampling.gridIncrement_nonzero intervals positive direction moving))
  let oldQueries : PreparedParents.QueryAgreement requested.attempt.2.1 :=
    completed.queries firstTen secondTen thirdTen fourthTen
  ⟨⟨oldQueries, rfl⟩, Data.Sigma.ofSubtypeFactories
    (α := CommonSource (requested := requested) commonCurrent commonAccuracy)
    (β := fun common => PreparedParents.QueryAgreement common.1.prepared)
    (γ := fun common _ => PositiveGridNode.Table intervals positive direction moving spatial common.1 common.2
      ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage)
    (δ := fun _ queries table => PositiveGridNode.Table.Completions table queries)
    (fun _ => PreparedParents.StageAttempt.Completed.requested requested.covered requested.chain
      (⟨requested.attempt, completed.completion⟩ : PreparedParents.StageAttempt.Completed
        requested.covered requested.chain requested.requested.selected.stage freshFloor rootStage)
      requested.requested.attempt_eq commonCurrent commonAccuracy)
    (fun common => PreparedParents.QueryAgreement.reprepare
      requested.attempt.2.1 common.1.prepared oldQueries)
    (fun common _ => PositiveGridNode.Table.build intervals positive direction moving spatial common.1 common.2
      ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage)
    (fun _ queries table => PositiveGridNode.Table.Completions.build table queries)⟩

/-- The complete retained table equals the original five-let execution with all five factory invariants. -/
private theorem positiveTable_factory
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)
    : positiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction
    moving spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage =
    (let commonAccuracy := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
       (Sampling.gridIncrement_nonzero intervals positive direction moving))
     let oldQueries : PreparedParents.QueryAgreement requested.attempt.2.1 :=
       completed.queries firstTen secondTen thirdTen fourthTen
     let common : CommonSource (requested := requested) commonCurrent commonAccuracy :=
       PreparedParents.StageAttempt.Completed.requested requested.covered requested.chain
         (⟨requested.attempt, completed.completion⟩ : PreparedParents.StageAttempt.Completed
           requested.covered requested.chain requested.requested.selected.stage freshFloor rootStage)
         requested.requested.attempt_eq commonCurrent commonAccuracy
     let queries : PreparedParents.QueryAgreement common.1.prepared :=
       PreparedParents.QueryAgreement.reprepare requested.attempt.2.1 common.1.prepared oldQueries
     let table : PositiveGridNode.Table intervals positive direction moving spatial common.1 common.2
         ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage :=
       PositiveGridNode.Table.build intervals positive direction moving spatial common.1 common.2
         ranges allocation admitted widths completed.roots targetCurrent targetFloor targetRootStage
     let completions : PositiveGridNode.Table.Completions table queries :=
       PositiveGridNode.Table.Completions.build table queries
     ⟨⟨oldQueries, rfl⟩, ⟨common, rfl⟩, ⟨queries, rfl⟩, ⟨table, rfl⟩, ⟨completions, rfl⟩⟩) := rfl

namespace PositiveTable

variable {completed firstTen secondTen thirdTen fourthTen intervals positive direction moving spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

/-- Read the genuine old fine-query operation retained before the sufficient source selection. -/
@[expose, macro_inline] def oldQueries
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : PreparedParents.QueryAgreement requested.attempt.2.1 := retained.1.val

/-- Read the SAME original sufficient Requested value and its actual completed source member. -/
@[expose, macro_inline] def common
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : CommonSource (requested := requested) commonCurrent
    (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positive direction moving))) := retained.2.1.val

/-- Read the actual derived query operation on this exact sufficient common source's own preparation. -/
@[expose, macro_inline] def queries
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : PreparedParents.QueryAgreement retained.common.1.prepared := retained.2.2.1.val

/-- Read the SAME once-built positive node/programme/adjacent integral table on that common source/member. -/
@[expose, macro_inline] def table
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : PositiveGridNode.Table intervals positive direction moving spatial
    retained.common.1 retained.common.2 ranges allocation admitted widths completed.roots
    targetCurrent targetFloor targetRootStage := retained.2.2.2.1.val

/-- Read the actual original target completions/families for those SAME stored node values. -/
@[expose, macro_inline] def completions
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : PositiveGridNode.Table.Completions retained.table retained.queries :=
  retained.2.2.2.2.val

/-- The old query operation retains its exact original FineCompletion factory. -/
theorem oldQueries_eq
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : retained.oldQueries = completed.queries firstTen secondTen thirdTen fourthTen :=
  retained.1.property

/-- The whole common Requested/member pair is the original single-member retained-source factory. -/
theorem common_eq
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : retained.common = PreparedParents.StageAttempt.Completed.requested
    requested.covered requested.chain
      (⟨requested.attempt, completed.completion⟩ : PreparedParents.StageAttempt.Completed
        requested.covered requested.chain requested.requested.selected.stage freshFloor rootStage)
      requested.requested.attempt_eq commonCurrent
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))) := retained.2.1.property

/-- The exact sufficient-source query operation derives from the SAME stored old queries and original parent roots. -/
theorem queries_eq
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : retained.queries = PreparedParents.QueryAgreement.reprepare
    requested.attempt.2.1 retained.common.1.prepared retained.oldQueries := retained.2.2.1.property

/-- The whole stored table has the original finite factory on this SAME retained source/member and original roots. -/
theorem table_eq
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : retained.table = PositiveGridNode.Table.build intervals positive direction moving spatial
    retained.common.1 retained.common.2 ranges allocation admitted widths completed.roots
    targetCurrent targetFloor targetRootStage := retained.2.2.2.1.property

/-- The complete target cache vector has its original factory on those SAME stored nodes, Alignments and queries. -/
theorem completions_eq
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
      firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint
      firstFine.numerical.initial.source sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    {completed : FineCompletion requested}
    {firstTen : 10 ≤ firstFine.numerical.depth} {secondTen : 10 ≤ secondFine.numerical.depth}
    {thirdTen : 10 ≤ thirdFine.numerical.depth} {fourthTen : 10 ≤ fourthFine.numerical.depth}
    {intervals : Nat} {positive : 0 < intervals} {direction : Canonical} {moving : direction ≠ 0}
    {spatial : AccuracyRequest} {commonCurrent : Nat}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : PositiveTable completed firstTen secondTen thirdTen fourthTen intervals positive direction moving
      spatial commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)
    : retained.completions =
    PositiveGridNode.Table.Completions.build retained.table retained.queries := retained.2.2.2.2.property

end PositiveTable

end FineCompletion

end Requested

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
