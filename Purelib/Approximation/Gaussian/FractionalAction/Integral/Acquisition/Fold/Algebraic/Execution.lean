module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Traversal
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Resumable work on an algebraic fractional fold

A pending head decision retains its original numerical cursor and row cache.
Suffix frames retain their actual head action and child work, so a finite
budget can stop and resume within a later fractional action.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- A head request retained between numerical preflight and algebraic decision. -/
@[expose] def PendingHead {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrix : IntegralMatrix) (remaining : List IntegralMatrix) : Type 1 :=
  Run.HeadRequest input matrix remaining

/-- The original numerical preflight retained for one pending head. -/
@[expose] def PendingObservation {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : PendingHead input matrix remaining) : Type 1 := Run.Preflight request

/-- An actual progressed branch of the retained numerical preflight. -/
@[expose] def Progressed {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} (observed : PendingObservation request) : Type 1 :=
  { outcome : Run.Preflight.Outcome observed // match outcome with | .inl _ => False | .inr _ => True }

section

attribute [local irreducible] PendingHead PendingObservation Progressed HeadPreparation RetainedHead
  headAction PreparedAction RowActionIdentity actionOutput actionEvidence State.Cursor

set_option genInjectivity false in
/-- The original fold cursor or a finite suspended head decision within its retained suffix.

Each suffix frame owns its original source and either its computed head or
its action at an independently supplied preparation. The nested work is
indexed by that exact action output and its original algebraic evidence. -/
inductive Work : {tau : CoherentNamed} → (input : Provenance.Algebraic.Sidecar tau) →
    List IntegralMatrix → Type 1 where
  /-- Continue from an original retained fold cursor. -/
  | active {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrices : List IntegralMatrix} (cursor : Cursor input matrices) : Work input matrices
  /-- The original preflight progressed; its same rows await algebraic decision. -/
  | deciding {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {request : PendingHead input matrix remaining} (observed : PendingObservation request)
      (progressed : Progressed observed) : Work input (matrix :: remaining)
  /-- Continue within the actual output of an algebraically decided head. -/
  | tailHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
      (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : childSource = actionEvidence (headAction head))
      (child : Work childSource remaining) : Work input (matrix :: remaining)
  /-- Continue within an original action at a supplied head preparation. -/
  | tailPrepared {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : childSource = actionEvidence action)
      (child : Work childSource remaining) : Work input (matrix :: remaining)

constructive_injectivity Work

end

/-- Read the original cursor corresponding to the exact retained work state.

Suspended suffixes use the same child cursor and cache under their original
head; source identity transports retain the original computational objects. -/
@[expose, noinline, nospecialize] def Work.current {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) : Cursor input matrices :=
  match work with
  | .active cursor => cursor
  | .deciding _ progressed => by
      match selected : progressed.val with
      | .inl _ =>
          have impossible : False := by
            have retained := progressed.property
            rw [selected] at retained
            exact retained
          exact False.elim impossible
      | .inr ⟨_, _, resumed⟩ => exact resumed.val.cursor
  | @Work.tailHead _ _ _ _ source same _ _ head _ childSource_eq child => by
      let current := child.current
      exact ⟨source, same, originalTail head current.original,
        .tail head current.source (current.source_eq.trans childSource_eq) current.cache⟩
  | @Work.tailPrepared _ _ _ _ source same _ rows action action_eq _ childSource_eq child => by
      let current := child.current
      exact ⟨source, same, actionTail action current.original,
        .preparedTail rows action action_eq current.source (current.source_eq.trans childSource_eq) current.cache⟩

/-- A retained work state and its one cached current-cursor projection. -/
@[expose] def Work.Observation {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) : Type 1 :=
  Σ retained : { value : Work input matrices // value = work },
    { cursor : Cursor input matrices // cursor = retained.val.current }

/-- Retain the original work and compute its current cursor once. -/
@[expose, noinline, nospecialize] def Work.observe {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) : Work.Observation work :=
  ⟨⟨work, rfl⟩, ⟨work.current, rfl⟩⟩

/-- Work produced by the exact selected branch of an original preflight. -/
@[expose] def Work.PreflightWork {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} (observed : PendingObservation request)
    (outcome : Run.Preflight.Outcome observed) : Type 1 :=
  match selected : outcome with
  | .inl ⟨_, next⟩ => { work : Work input (matrix :: remaining) // work = .active next.val }
  | .inr _ =>
      let progressed : Progressed observed := ⟨outcome, by rw [selected]; trivial⟩
      { work : Work input (matrix :: remaining) // work = .deciding observed progressed }

/-- Use the actual selected preflight result to create the next retained work state.

The prepared branch carries the original action cursor; the progressed branch
retains the exact observed preflight and its actual suspended result. -/
@[expose, noinline, nospecialize] def Work.fromPreflight {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} (observed : PendingObservation request) :
    Σ advanced : { value : (Σ retained : { value : PendingObservation request // value = observed },
      Run.Preflight.Outcome retained.val) // value = observed.advance },
      Work.PreflightWork advanced.val.1.val advanced.val.2 := by
  let advanced := observed.advance
  have selected : Work.PreflightWork advanced.1.val advanced.2 := by
    cases advanced.2 with
    | inl ready =>
        rcases ready with ⟨_, next⟩
        exact ⟨.active next.val, rfl⟩
    | inr pending =>
        exact ⟨.deciding advanced.1.val ⟨.inr pending, True.intro⟩, rfl⟩
  exact ⟨⟨advanced, rfl⟩, selected⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
