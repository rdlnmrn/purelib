module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy

/-! # Exact accuracy-index transport of original retained source requests

Equality of the WHOLE positive AccuracyRequest reindexes the original
Requested value. The complete Selection, attempt, Targets and preparation
remain the same actual data. A supplied actual completed member transports
with those same indices; no source, checking or completion factory executes.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {current floor rootStage : Nat} {first last : AccuracyRequest}

/-- Transport the SAME entire original sufficient source request along exact equality of its whole accuracy index.

The exposed body is only equality elimination on the original Requested
container. It never changes a tolerance, runs a stage search or constructs
an attempt. Original selected_eq, attempt_eq and prepared_eq remain the
same public factory contracts at the exactly equal request index.
-/
@[expose] def castAccuracy (equal : first = last)
    (retained : Requested covered chain current floor rootStage first) :
    Requested covered chain current floor rootStage last := by
  cases equal
  exact retained

variable (equal : first = last) (retained : Requested covered chain current floor rootStage first)

/-- Exact accuracy-index transport retains the complete original Requested value heterogeneously. -/
theorem castAccuracy_heq : HEq (retained.castAccuracy equal) retained := by
  cases equal
  rfl

/-- The SAME complete original finite selection retains its quotient, fuel, stage, allowance and factory data. -/
theorem castAccuracy_selected : HEq (retained.castAccuracy equal).selected retained.selected := by
  cases equal
  rfl

/-- The displayed original source stage is identical after whole-accuracy transport. -/
theorem castAccuracy_stage : (retained.castAccuracy equal).selected.stage = retained.selected.stage := by
  cases equal
  rfl

/-- The whole original attempt, bank, first-match lookups, checker decisions and both outcomes remain retained. -/
theorem castAccuracy_attempt : HEq (retained.castAccuracy equal).attempt retained.attempt := by
  cases equal
  rfl

/-- The SAME actual original global Targets allocation is retained without a new producer or relabelled allowance. -/
theorem castAccuracy_targets : HEq (retained.castAccuracy equal).targets retained.targets := by
  cases equal
  rfl

/-- The complete preparation product, six-cell models and original point/root owners remain the SAME cached values. -/
theorem castAccuracy_prepared : HEq (retained.castAccuracy equal).prepared retained.prepared := by
  cases equal
  rfl

/-- Exact accuracy transport preserves each complete original six-channel source-cell word.

The original Targets and preparation stay inside the same Requested value.
Only the equal accuracy index is eliminated; neither preparation nor source
assembly executes again.
-/
theorem castAccuracy_cells (channel : Fin 6) :
    (sources covered (retained.castAccuracy equal).prepared chain).cells channel =
      (sources covered retained.prepared chain).cells channel := by
  cases equal
  rfl

/-- Transport the SAME retained completed member with its original request, actual attempt and acquired Commons.

Only exact accuracy equality changes the dependent selected-stage display.
The original member and its whole attempt identity are consumed unchanged;
no all-stage family callback, readiness check or completion is executed.
-/
def castAccuracyCompleted
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    { value : Completed covered chain (retained.castAccuracy equal).selected.stage floor rootStage //
      value.1 = (retained.castAccuracy equal).attempt } := by
  cases equal
  exact member

/-- The transported completed-member subtype keeps the whole SAME original completion and actual attempt cache. -/
theorem castAccuracyCompleted_heq
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    HEq (retained.castAccuracyCompleted equal member) member := by
  cases equal
  rfl

/-- Reindex the same retained source and its whole completed member together at an equal accuracy.

The two original equality transports execute once and retain their original
order. The dependent pair keeps its source and member indices together;
no source selection, preparation, check or completion executes.
-/
@[expose] def castAccuracyMember
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    (paid : Requested covered chain current floor rootStage last) ×
    { value : Completed covered chain paid.selected.stage floor rootStage // value.1 = paid.attempt } :=
  let paid := retained.castAccuracy equal
  let completed := retained.castAccuracyCompleted equal member
  ⟨paid, completed⟩

/-- The entire transported pair has the original source-then-member equality-transport factory. -/
theorem castAccuracyMember_factory
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    retained.castAccuracyMember equal member =
      let paid := retained.castAccuracy equal
      let completed := retained.castAccuracyCompleted equal member
      ⟨paid, completed⟩ := rfl

/-- The transported pair reads the same original whole source at its equal accuracy. -/
theorem castAccuracyMember_source
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    (retained.castAccuracyMember equal member).1 = retained.castAccuracy equal := rfl

/-- The transported pair retains the same entire completed member and its actual attempt identity. -/
theorem castAccuracyMember_member_heq
    (member : { value : Completed covered chain retained.selected.stage floor rootStage //
      value.1 = retained.attempt }) :
    HEq (retained.castAccuracyMember equal member).2 member := by
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
