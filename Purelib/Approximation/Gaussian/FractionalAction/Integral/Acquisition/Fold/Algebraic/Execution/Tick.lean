module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Expand
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Selected algebraic fold obstructions

A zero denominator is the actual result of the retained head's row decision.
Wrapping that obstruction through the original suffix frames preserves every
earlier head and its exact pending child work.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- The actual row decision at a retained pending head. -/
@[expose] def HeadDecision {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : PendingHead input matrix remaining) : Type 1 := Run.Decision request

/-- The zero obstruction actually selected by the retained row decision. -/
@[expose] def SelectedZero {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} (observed : HeadDecision request) : Type 1 :=
  { obstruction : Integral.Algebraic.Obstruction observed.1.val.rows // observed.2.val = .error obstruction }

/-- Read the actual resumed request from a retained progressed preflight. -/
@[expose] def progressedRequest {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} {request : PendingHead input matrix remaining}
    {observed : PendingObservation request} (progressed : Progressed observed) :
    PendingHead input matrix remaining := by
  match selected : progressed.val with
  | .inl _ =>
      have impossible : False := by
        have retained := progressed.property
        rw [selected] at retained
        exact retained
      exact False.elim impossible
  | .inr ⟨_, _, resumed⟩ => exact resumed.val

/-- The work state containing this exact progressed preflight. -/
@[expose] def headWork {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} {request : PendingHead input matrix remaining}
    (observed : PendingObservation request) (progressed : Progressed observed) : Work input (matrix :: remaining) :=
  .deciding observed progressed

/-- A suffix work frame with its original computed head. -/
@[expose] def headFrame {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head)) (child : Work childSource remaining) :
    Work input (matrix :: remaining) := .tailHead source source_eq head childSource childSource_eq child

/-- A suffix work frame with its action at the supplied original preparation. -/
@[expose] def preparedFrame {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action) (child : Work childSource remaining) :
    Work input (matrix :: remaining) :=
  .tailPrepared source source_eq rows action action_eq childSource childSource_eq child


section

attribute [local irreducible] PendingHead PendingObservation Progressed progressedRequest
  HeadDecision SelectedZero headWork headFrame preparedFrame
  HeadPreparation RetainedHead headAction PreparedAction RowActionIdentity actionOutput actionEvidence

set_option genInjectivity false in
/-- An actual zero denominator found in the selected retained work.

The head case retains the exact row decision and its selected obstruction.
Suffix cases retain each original action and the same nested work and zero. -/
inductive Zero : {tau : CoherentNamed} → {input : Provenance.Algebraic.Sidecar tau} →
    {matrices : List IntegralMatrix} → Work input matrices → Type 1 where
  /-- The retained head's actual row decision selected this obstruction. -/
  | head {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {request : PendingHead input matrix remaining} (preflight : PendingObservation request)
      (progressed : Progressed preflight) (observed : HeadDecision (progressedRequest progressed))
      (obstruction : SelectedZero observed) : Zero (headWork preflight progressed)
  /-- The zero occurred inside the exact suffix of a computed head. -/
  | tailHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
      (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : childSource = actionEvidence (headAction head))
      (child : Work childSource remaining) (zero : Zero child) :
      Zero (headFrame source source_eq head childSource childSource_eq child)
  /-- The zero occurred inside the exact suffix of an action at a supplied preparation. -/
  | tailPrepared {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : childSource = actionEvidence action)
      (child : Work childSource remaining) (zero : Zero child) :
      Zero (preparedFrame source source_eq rows action action_eq childSource childSource_eq child)

constructive_injectivity Zero

end

/-- The exact row decision for deciding work, or an empty view for other stages. -/
@[expose] def Work.HeadOutcome {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} : Work input matrices → Type 1
  | .deciding _ progressed => HeadDecision (progressedRequest progressed)
  | _ => ULift.{1} Unit

/-- The retained prior work and its stage-indexed head observation. -/
@[expose] def HeadResolution {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) : Type 1 :=
  Σ retained : { value : Work input matrices // value = work }, retained.val.HeadOutcome

/-- Inspect a pending head decision, or return the empty view of another stage. -/
@[expose, noinline, nospecialize] def Work.inspectHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) : work.HeadOutcome :=
  match work with
  | .deciding _ progressed => (progressedRequest progressed).decide
  | .active _ => ULift.up ()
  | .tailHead .. => ULift.up ()
  | .tailPrepared .. => ULift.up ()

/-- Perform one algebraic decision when the actual selected work awaits it.

The result retains the supplied work itself and the actual finite decision.
Other stages return their exact retained work and an empty observation. -/
@[expose, noinline, nospecialize] def resolveHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) : HeadResolution work :=
  ⟨⟨work, rfl⟩, work.inspectHead⟩

/-- An unexpanded original cursor does not itself contain a selected zero. -/
theorem Zero.notActive {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) (zero : Zero (.active cursor)) : False := by
  cases zero

/-- No unpaid expansion of a cursor itself performs a zero decision.

An expansion contains either the original active cursor or one attached
suffix frame whose child remains active. A selected zero requires a prior
paid preflight and row decision. -/
theorem Zero.notExpansion {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices)
    (zero : Zero (Work.fromCursor cursor)) : False := by
  cases matrices with
  | nil => exact Zero.notActive cursor zero
  | cons matrix remaining =>
      change Zero (match found : cursor.original with
        | .tail payload =>
            match Work.fromSuppliedTail cursor payload found with
            | some work => work.val
            | none => .active cursor
        | _ => .active cursor) at zero
      split at zero
      next payload found =>
        split at zero
        next work selected =>
          unfold Work.fromSuppliedTail at selected
          cases cursor with
          | mk source source_eq original cache =>
            cases cache with
            | pending => cases selected
            | tail head childSource childSource_eq nested =>
                change some _ = some work at selected
                have same := Option.some.inj selected
                cases same
                cases zero with
                | tailHead _ _ _ _ _ _ childZero => cases childZero
            | preparedTail rows action action_eq childSource childSource_eq nested =>
                change some _ = some work at selected
                have same := Option.some.inj selected
                cases same
                cases zero with
                | tailPrepared _ _ _ _ _ _ _ _ childZero => cases childZero
            | combinedHead => cases found
            | combinedPrepared => cases found
            | readyHead => cases found
            | readyPrepared => cases found
        next selected => exact Zero.notActive cursor zero
      all_goals exact Zero.notActive cursor zero

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
