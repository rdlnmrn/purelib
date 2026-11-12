module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Agreement
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Completion
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.List.DependentProduct

/-! # Completed all-fine source queries and actual parameter-window completion

The original fine Completion is materialized once from the same paid
execution and literal global Request. Its stored origins and completion
supply base query agreement. The actual successor occurrence/Step producer
then supplies its own query agreement and original endpoint admissions.
Both parameter owners, banks, source allocations and completed caches stay
distinct; no readiness, signed relation or final numerical bound is an input.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Steps.Acquisition
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)

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

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Requested

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    (requested : Requested sources current freshFloor rootStage accuracy)

namespace FineCompletion

variable {requested} (completed : FineCompletion requested)

/-- Derive all-query agreement from the SAME original completed attempt and retained fine-origin product.

The four actual depth payments derive the factor-window comparisons. The
old universal endpoint comparisons and own Found/Position caches come from
this exact FineCompletion, rather than a supplied desired all-query relation.
-/
def queries (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth) :
    PreparedParents.QueryAgreement requested.attempt.2.1 :=
  requested.queryAgreement completed.origins firstTen secondTen thirdTen fourthTen completed.completion

/-- Extend this SAME completed global source request through its own canonical stage family.

The selected branch retains the whole supplied Completed value. The original
Requested factory equation pays canonical preparation; other stages keep
their own numerical preparations/checks and reuse the selected geometrical
payment through the original Completed.family operation.
-/
def sourceFamily : requested.attempt.CompletedFamily :=
  PreparedParents.StageAttempt.Completed.family
    (parameter := parameter) (frame := frame) (basis := basis) (count := modelCount)
    (parent := requested.shape.val.1) (parents := requested.shape.val.2)
    requested.covered requested.chain
    (index := requested.requested.selected.stage) (floor := freshFloor) (rootStage := rootStage)
    ⟨requested.attempt, completed.completion⟩ requested.requested.attempt_eq

/-- The selected source-family member is the whole SAME original attempt/completion, including all acquisitions. -/
theorem sourceFamily_at :
    (completed.sourceFamily requested.requested.selected.stage).val =
      (⟨requested.attempt, completed.completion⟩ : PreparedParents.StageAttempt.Completed
        (parameter := parameter) (frame := frame) (basis := basis) (count := modelCount)
        requested.covered requested.chain requested.requested.selected.stage freshFloor rootStage) := by
  unfold sourceFamily
  exact PreparedParents.StageAttempt.Completed.family_at
    (parameter := parameter) (frame := frame) (basis := basis) (count := modelCount)
    (parent := requested.shape.val.1) (parents := requested.shape.val.2)
    requested.covered requested.chain
    (index := requested.requested.selected.stage) (floor := freshFloor) (rootStage := rootStage)
    ⟨requested.attempt, completed.completion⟩ requested.requested.attempt_eq

section Window

variable {increment : Canonical} {target : Paths.Frame (parameter + increment)}
    {ranges : PreparedParents.ParameterRange requested.covered}
    {allocation : PreparedParents.ParameterRange.StripAllocation ranges}
    {admitted : Data.Gaussian.Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest}
    {blocks : PreparedParents.ShiftedGeometry.Blocks (target := target)
      requested.attempt.2.1 ranges allocation admitted widths}
    {whole : let first := DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2) blocks 0
      PreparedParents.ShiftedGeometry (target := target) (basis := basis) (count := modelCount)
        (PreparedParent.startPoint requested.shape.val.1) (PreparedParent.startPoint requested.shape.val.1)
        first.first.root.value.name first.first.root.value.name}
    {requestIndex globalFloor nextRootStage : Nat}
    {outgoing : PreparedParents.ShiftedGeometry.Request whole requestIndex globalFloor nextRootStage}

/-- Complete the SAME actual successor request using internally derived base all-query agreement.

The outgoing Blocks, occurrence table, Alignments, endpoint Steps, global
Targets and bank are retained inputs. Their actual parameter comparison
constructs successor query agreement; original completeQueries consumes its
own old checks/Commons and acquires only genuinely unpaid endpoint work.
No successor Completion, Ready, Distinct or root relation is supplied.
-/
def completeWindow (firstTen : 10 ≤ firstFine.numerical.depth)
    (secondTen : 10 ≤ secondFine.numerical.depth) (thirdTen : 10 ≤ thirdFine.numerical.depth)
    (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (stored : PreparedParents.ShiftedGeometry.Occurrences blocks outgoing)
    (aligned : DependentProduct (requested.shape.val.1 :: requested.shape.val.2) (fun index =>
      RootComparisons.Alignment
          (DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2) blocks index).comparison.paths
          (DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2)
            blocks index).comparison.firstReference)) :
    PreparedParents.StageAttempt.Completion outgoing.attempt :=
  let oldQueries := completed.queries firstTen secondTen thirdTen fourthTen
  PreparedParents.ShiftedGeometry.Occurrences.complete stored aligned oldQueries

/-- Retain one actual completed successor and its original canonical CompletedFamily without replacing either cache.

The completion and family have their whole original factory equalities.
The selected outgoing family member therefore retains the exact completed
request returned here. Other stages are genuinely new original attempts;
there is no preparation-only callback labeled as a completed bank.
-/
def windowFamily (firstTen : 10 ≤ firstFine.numerical.depth)
    (secondTen : 10 ≤ secondFine.numerical.depth) (thirdTen : 10 ≤ thirdFine.numerical.depth)
    (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (stored : PreparedParents.ShiftedGeometry.Occurrences blocks outgoing)
    (aligned : DependentProduct (requested.shape.val.1 :: requested.shape.val.2) (fun index =>
      RootComparisons.Alignment
          (DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2) blocks index).comparison.paths
          (DependentProduct.get (requested.shape.val.1 :: requested.shape.val.2)
            blocks index).comparison.firstReference)) :
    (acquired : { value : PreparedParents.StageAttempt.Completion outgoing.attempt //
      value = completed.completeWindow firstTen secondTen thirdTen fourthTen stored aligned }) ×
    { family : outgoing.attempt.CompletedFamily // family = outgoing.completedFamily acquired.val } :=
  let acquired := completed.completeWindow firstTen secondTen thirdTen fourthTen stored aligned
  let family := outgoing.completedFamily acquired
  ⟨⟨acquired, rfl⟩, ⟨family, rfl⟩⟩

end Window

end FineCompletion

/-- Materialize one initial fine completion and its base query-agreement operation from original paid geometry only.

The same internally derived roots, one stored SourceOrigins product, actual
original check outcomes and additional unpaid acquisitions remain retained
in the FineCompletion cache. Four genuine depth payments are the only extra
fine-geometry admission; no external Completion or signed relation is used.
-/
def completeFineQueries (firstTen : 10 ≤ firstFine.numerical.depth)
    (secondTen : 10 ≤ secondFine.numerical.depth) (thirdTen : 10 ≤ thirdFine.numerical.depth)
    (fourthTen : 10 ≤ fourthFine.numerical.depth) :
    (completed : { value : FineCompletion requested //
      value = requested.completeFine firstTen secondTen thirdTen fourthTen }) ×
    { agreement : PreparedParents.QueryAgreement requested.attempt.2.1 //
      agreement = completed.val.queries firstTen secondTen thirdTen fourthTen } :=
  let completed := requested.completeFine firstTen secondTen thirdTen fourthTen
  let queries := completed.queries firstTen secondTen thirdTen fourthTen
  ⟨⟨completed, rfl⟩, ⟨queries, rfl⟩⟩

end Requested

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
