module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs

/-! # A genuine sufficient-stage source request on the same original covered cycle

The original covered parents and centered geometric chain precede the finite
stage selection. ONE new original StageAttempt allocates all old-parameter
Targets, source preparations, endpoint bank and finite checks at that selected
stage. Earlier requests stay separate. This pays actual new source-cell
allowances before any point query or parameter-Step callback is constructed.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

open Purelib.Approximation.Rational.Geometric

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))

/-- One sufficient-stage selection and the complete new actual original source attempt with both factory identities.

The original parameter, patches, parent occurrences and geometry stay
indices. Its actual global Targets and every six-channel preparation are
computed after the sufficient stage; no old source allowance is retagged.
-/
@[expose] def Requested (current floor rootStage : Nat) (accuracy : AccuracyRequest) :=
  (selected : { value : Search.Selection 1 current accuracy.tolerance //
    value = Search.Selection.build 1 (of_decide_eq_true rfl) current
      accuracy.tolerance accuracy.positive }) ×
  { attempt : StageAttempt covered chain selected.val.stage floor rootStage //
    attempt = fromCovered covered chain selected.val.stage floor rootStage }

namespace Requested

/-- Select a sufficient original stage, then execute the complete new covered-source request exactly once. -/
def build (current floor rootStage : Nat) (accuracy : AccuracyRequest) :
    Requested covered chain current floor rootStage accuracy :=
  let selected := Search.Selection.build 1 (of_decide_eq_true rfl) current
    accuracy.tolerance accuracy.positive
  let attempt := fromCovered covered chain selected.stage floor rootStage
  ⟨⟨selected, rfl⟩, ⟨attempt, rfl⟩⟩

/-- Retain an already computed sufficient selection and the same whole original covered-stage attempt.

The original factory equalities are required at both indices. This operation
only packages the supplied values in Requested's existing dependent pairs;
it performs no search, preparation, lookup, checking or completion. Its
body is exposed so the selected-stage index reduces in dependent results.
-/
@[expose] def ofRetained (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (selected : { value : Search.Selection 1 current accuracy.tolerance //
      value = Search.Selection.build 1 (of_decide_eq_true rfl) current
        accuracy.tolerance accuracy.positive })
    (attempt : StageAttempt covered chain selected.val.stage floor rootStage)
    (factory : attempt = fromCovered covered chain selected.val.stage floor rootStage) :
    Requested covered chain current floor rootStage accuracy :=
  ⟨selected, ⟨attempt, factory⟩⟩

/-- The retained constructor reads the entire supplied selection without repeating the bounded search. -/
theorem ofRetained_selected (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (selected : { value : Search.Selection 1 current accuracy.tolerance //
      value = Search.Selection.build 1 (of_decide_eq_true rfl) current
        accuracy.tolerance accuracy.positive })
    (attempt : StageAttempt covered chain selected.val.stage floor rootStage)
    (factory : attempt = fromCovered covered chain selected.val.stage floor rootStage) :
    (ofRetained covered chain current floor rootStage accuracy selected attempt factory).1.val = selected.val := by
  rfl

/-- The retained constructor reads the identical whole supplied attempt, including its actual original caches. -/
theorem ofRetained_attempt (current floor rootStage : Nat) (accuracy : AccuracyRequest)
    (selected : { value : Search.Selection 1 current accuracy.tolerance //
      value = Search.Selection.build 1 (of_decide_eq_true rfl) current
        accuracy.tolerance accuracy.positive })
    (attempt : StageAttempt covered chain selected.val.stage floor rootStage)
    (factory : attempt = fromCovered covered chain selected.val.stage floor rootStage) :
    (ofRetained covered chain current floor rootStage accuracy selected attempt factory).2.val = attempt := by
  rfl

variable {covered chain} {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (retained : Requested covered chain current floor rootStage accuracy)

/-- Read the SAME cached finite sufficient-stage selection. -/
@[expose] def selected : Search.Selection 1 current accuracy.tolerance := retained.1.val

/-- The whole selected stage retains the original search factory at the actual requested accuracy. -/
theorem selected_eq : retained.selected = Search.Selection.build 1 (of_decide_eq_true rfl) current
    accuracy.tolerance accuracy.positive := retained.1.property

/-- Read the entire new source request with its actual bank, Targets, preparations and finite checking outcomes. -/
@[expose] def attempt : StageAttempt covered chain retained.selected.stage floor rootStage := retained.2.val

/-- The complete retained attempt is the original factory on those SAME patches and geometry. -/
theorem attempt_eq : retained.attempt = fromCovered covered chain retained.selected.stage floor rootStage :=
  retained.2.property

/-- Read the actual new global Targets of this SAME old-parameter source request. -/
@[expose] def targets := retained.attempt.1.val

/-- Read the actual already materialized original preparation at every source parent occurrence. -/
@[expose] def prepared := retained.attempt.2.1

/-- The whole new source family retains its original prepareCovered factory on the SAME actual global Targets. -/
theorem prepared_eq : retained.prepared = prepareCovered covered floor retained.targets :=
  prepared_of_factory covered chain retained.attempt retained.attempt_eq

/-- The newly selected actual source allocation strictly pays the requested common accuracy. -/
theorem localBound_lt : retained.targets.localBound < accuracy.tolerance :=
  retained.targets.localBound_le_quarterRadius.trans_lt (retained.selected.later_accurate (Nat.le_refl _))

/-- Every actual six-channel old-parameter source cell pays that SAME common request before point callbacks occur. -/
theorem cell_allowance_lt (index : Fin (parent :: parents).length) (channel : Fin 6) :
    ((retained.prepared.entry index).preparation.cell.models.cell channel).localAllowance < accuracy.tolerance :=
  ((retained.prepared.entry index).cell_allowance channel).trans_lt retained.localBound_lt

/-- Both actual endpoint allocations of the new old-parameter source request pay the identical common accuracy. -/
theorem endpoint_lt : retained.targets.endpoint < accuracy.tolerance := by
  rewrite [retained.targets.endpoint_eq]
  exact retained.localBound_lt

/-- A complete original source member at the request's retained selected stage.

The subtype keeps the entire completed value and its exact attempt identity
on the same covered parents, chain, numerical floors and accuracy owner.
-/
@[expose] def Member {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain current floor rootStage accuracy) : Type _ :=
  { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }

end Requested

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

end
