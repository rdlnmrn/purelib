module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain

/-! # Source preparations retaining one actual original request

The same fixed covered spine is prepared at all other programme stages.
At the actual retained request stage, exact Targets transport consumes its
whole original preparation cache. Its original source-list readback retains
that same source; no stage, endpoint bank, source query or shifted acquisition
is replayed at the retained index.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)

/-- Retain the actual preparation at its original index and prepare the same original fixed spine at other stages.

The equality branch transports only the actual Targets index of the whole
stored preparation product. The other branch invokes prepareCovered with
its own genuine Targets. Neither branch reruns the actual original attempt
or claims sharing between independent callbacks.
-/
def preparationFamily (stage : Nat) :
    PreparedParents covered floor (CellEndpoints.Targets.build chain.path stage) :=
  if equal : stage = index then
    Eq.mpr (congrArg (fun selected =>
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path selected)) equal)
      attempt.preparations
  else
    prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage)

/-- The selected branch consumes the whole identical computed-index view of the actual preparation. -/
theorem preparationFamily_at : attempt.preparationFamily index = attempt.preparations := by
  unfold preparationFamily
  rewrite [dif_pos rfl]
  rfl

/-- At every other stage the family is the genuine original source preparation on that same fixed geometry. -/
theorem preparationFamily_other (stage : Nat) (different : stage ≠ index) :
    attempt.preparationFamily stage =
      prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage) := by
  unfold preparationFamily
  rewrite [dif_neg different]
  rfl

/-- The retained stage has the literal original source lists of the actual request, without another source factory. -/
theorem preparationFamily_sources :
    sources covered (attempt.preparationFamily index) chain = sources covered attempt.2.1 chain :=
  (congrArg (fun prepared => sources covered prepared chain) attempt.preparationFamily_at).trans
    attempt.preparations_sources

/-- Extend one retained attempt to the same fixed covered spine at every original programme stage.

The selected branch transports the whole original attempt, including its
Targets, sources, bank, checks and stored StageResult. Every other stage
constructs its own allocation and preparation once before the same bank
and checker operation. No preparation-only callback is treated as completed.
-/
def attemptFamily (stage : Nat) : StageAttempt covered chain stage floor rootStage :=
  if equal : stage = index then
    Eq.mpr (congrArg (fun selected => StageAttempt covered chain selected floor rootStage) equal) attempt
  else
    let targets := CellEndpoints.Targets.build chain.path stage
    let prepared := prepareCovered covered floor targets
    ofPrepared covered chain targets rfl prepared rootStage

/-- The selected stage retains the entire original attempt as the identical cache value. -/
theorem attemptFamily_at : attempt.attemptFamily index = attempt := by
  unfold attemptFamily
  rewrite [dif_pos rfl]
  rfl

/-- At another stage the family executes the original preparation and checker tail on that stage's own Targets. -/
theorem attemptFamily_other (stage : Nat) (different : stage ≠ index) :
    attempt.attemptFamily stage =
      let targets := CellEndpoints.Targets.build chain.path stage
      let prepared := prepareCovered covered floor targets
      ofPrepared covered chain targets rfl prepared rootStage := by
  unfold attemptFamily
  rewrite [dif_neg different]
  rfl

/-- The attempt family has the exact preparation-family values on the same original stage and Targets indices.

At the retained index both sides consume the original cache. Elsewhere this
is equality of the original preparation factories, not a claim that separate
callback invocations shared an earlier execution or its endpoint checks.
-/
theorem attemptFamily_preparations (stage : Nat) :
    (attempt.attemptFamily stage).preparations = attempt.preparationFamily stage := by
  unfold attemptFamily
  split
  next equal =>
    subst stage
    exact attempt.preparationFamily_at.symm
  next different =>
    have selected :
        (ofPrepared covered chain (CellEndpoints.Targets.build chain.path stage) rfl
          (prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage)) rootStage).preparations =
          prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage) :=
      ofPrepared_preparations covered chain (CellEndpoints.Targets.build chain.path stage) rfl
        (prepareCovered covered floor (CellEndpoints.Targets.build chain.path stage)) rootStage
    exact selected.trans (attempt.preparationFamily_other stage different).symm

/-- The same stage family retains the complete original ordered source-chain values at each stage. -/
theorem attemptFamily_sources (stage : Nat) :
    sources covered (attempt.attemptFamily stage).preparations chain =
      sources covered (attempt.preparationFamily stage) chain :=
  congrArg (fun prepared => sources covered prepared chain) (attempt.attemptFamily_preparations stage)

/-- A completed family retains an original completion of each exact indexed attempt.

Each member stores its whole Completed value and equality of its original
attempt with that stage's actual attempt-family cache. This exact function
type keeps those owners and indices together without another container.
-/
@[expose] def CompletedFamily : Type _ :=
  (stage : Nat) → { retained : Completed covered chain stage floor rootStage //
    retained.1 = attempt.attemptFamily stage }

/-- Retain each actual successful family member together with its same original Completion and whole factory law.

The original attempt is let-bound once before Completed.ofReady reads its
stored successful StageResult and Commons. Actual readiness is required at
every requested stage; this operation does not prove that geometric fact.
Independent callbacks remain independent executions.
-/
def readyFamily (paid : (stage : Nat) → (attempt.attemptFamily stage).Ready) : attempt.CompletedFamily :=
  fun stage =>
    let current := attempt.attemptFamily stage
    let retained := Completed.ofReady current (paid stage)
    ⟨retained, Completed.ofReady_attempt current (paid stage)⟩

/-- A retained family member at the selected index owns the same entire original incoming attempt. -/
theorem completedFamily_at (retained : Completed covered chain index floor rootStage)
    (computed : retained.1 = attempt.attemptFamily index) : retained.1 = attempt :=
  computed.trans attempt.attemptFamily_at

/-- A retained completed member consumes the literal original preparation-family source chain.

The actual Completed value and its whole attempt factory equality are
consumed as inputs. No attempt or completion is reconstructed to obtain
the source-chain equality; all original acquired Commons remain stored.
-/
theorem completedFamily_sources (stage : Nat) (retained : Completed covered chain stage floor rootStage)
    (computed : retained.1 = attempt.attemptFamily stage) :
    retained.2.2.val.sources = sources covered (attempt.preparationFamily stage) chain :=
  (Completion.stage_sources retained.1 retained.2).trans
    ((congrArg (fun current : StageAttempt covered chain stage floor rootStage =>
      sources covered current.preparations chain) computed).trans (attempt.attemptFamily_sources stage))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

end
