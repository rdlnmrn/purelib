module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Expand
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word

/-!
# Cached cursor projections for finite fold work

A snapshot retains both its work state and one corresponding original cursor.
Suffix constructors use the child's existing cursor and cache directly, so
successive work units need not project the same nested work again.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Retained work and its exact cached original-cursor projection. -/
@[expose] def Snapshot {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrices : List IntegralMatrix) : Type 1 :=
  Σ work : Work input matrices, { cursor : Cursor input matrices // cursor = work.current }

/-- Project a work state once and retain both the original work and the resulting cursor. -/
@[expose, noinline, nospecialize] def Work.snapshot {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) : Snapshot input matrices :=
  let observed := work.observe
  ⟨observed.1.val, observed.2⟩

/-- Retain a computed head around an existing original child cursor. -/
@[expose] def wrapHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (child : Cursor childSource remaining) : Cursor input (matrix :: remaining) :=
  ⟨source, source_eq, originalTail head child.original,
    .tail head child.source (child.source_eq.trans childSource_eq) child.cache⟩

/-- Retain an action at a supplied preparation around an existing original child cursor. -/
@[expose] def wrapPreparation {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (child : Cursor childSource remaining) : Cursor input (matrix :: remaining) :=
  ⟨source, source_eq, actionTail action child.original,
    .preparedTail rows action action_eq child.source (child.source_eq.trans childSource_eq) child.cache⟩

/-- Wrap a cached child snapshot in its original computed-head frame.

The parent's original cursor is built directly from the child's stored cursor;
the proof links it to the complete corresponding work without re-projecting it. -/
@[expose, noinline, nospecialize] def Snapshot.tailHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (child : Snapshot childSource remaining) : Snapshot input (matrix :: remaining) := by
  let work := Work.tailHead source source_eq head childSource childSource_eq child.1
  let cursor := wrapHead source source_eq head childSource childSource_eq child.2.val
  have current : cursor = work.current := by
    exact congrArg (wrapHead source source_eq head childSource childSource_eq) child.2.property
  exact ⟨work, ⟨cursor, current⟩⟩

/-- Wrap a cached child snapshot in its original supplied-preparation frame. -/
@[expose, noinline, nospecialize] def Snapshot.tailPrepared {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (child : Snapshot childSource remaining) : Snapshot input (matrix :: remaining) := by
  let work := Work.tailPrepared source source_eq rows action action_eq childSource childSource_eq child.1
  let cursor := wrapPreparation source source_eq rows action action_eq childSource childSource_eq child.2.val
  have current : cursor = work.current := by
    exact congrArg (wrapPreparation source source_eq rows action action_eq childSource childSource_eq)
      child.2.property
  exact ⟨work, ⟨cursor, current⟩⟩

/-- Transport a selected suffix completion back to the actual retained input. -/
private theorem completionOfTransport {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (child : State.Cursor first remaining)
    (tail : FoldPreparations second remaining)
    (finished : State.finished? second remaining
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child same) = some tail) :
    State.finished? first remaining child = some
      (Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail same.symm) := by
  cases same
  exact finished

/-- Extract the actual completed tail and search from the original combined cursor. -/
@[noinline] def extractCombinedParts {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (head : Step.HeadPreparation tau matrix)
    (tail : FoldPreparations (Step.tailInput tau matrix head) remaining)
    (next : State.Cursor tau (matrix :: remaining))
    (isCombined : ∃ search : Cached.CachedSearch tau
      (Matrix.Integral.Word.matrixProduct (matrix :: remaining)),
      next = .combined ⟨head, tail, search⟩) :
    Σ actualTail : FoldPreparations (Step.tailInput tau matrix head) remaining,
      { search : Cached.CachedSearch tau
          (Matrix.Integral.Word.matrixProduct (matrix :: remaining)) //
        next = .combined ⟨head, actualTail, search⟩ ∧ actualTail = tail } := by
  cases next with
  | head value =>
      exfalso
      obtain ⟨search, impossible⟩ := isCombined
      cases impossible
  | tail value =>
      exfalso
      obtain ⟨search, impossible⟩ := isCombined
      cases impossible
  | combined value =>
      obtain ⟨actualHead, actualTail, actualSearch⟩ := value
      have sameHead : actualHead = head := by
        obtain ⟨expectedSearch, same⟩ := isCombined
        cases same
        rfl
      let retainedTail : FoldPreparations (Step.tailInput tau matrix head) remaining :=
        Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
          actualTail sameHead
      refine ⟨retainedTail, ⟨actualSearch, ?_⟩⟩
      obtain ⟨expectedSearch, same⟩ := isCombined
      cases same
      exact ⟨rfl, rfl⟩
  | ready value =>
      exfalso
      obtain ⟨search, impossible⟩ := isCombined
      cases impossible

/-- The same channel transport, reversed and then restored, returns the original value. -/
private theorem restoreTail {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (tail : FoldPreparations second remaining) :
    Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
      (Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail same.symm) same = tail := by
  cases same
  rfl

/-- The original selected combined cursor has the exact retained action and transported suffix. -/
private theorem actionCombined_selected {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation)
    (tail : FoldPreparations (Step.tailInput tau matrix preparation) remaining)
    (search : Cached.CachedSearch tau
      (Matrix.Integral.Word.matrixProduct (matrix :: remaining))) :
    actionCombined action
      (Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail action.1.property.symm)
      search = .combined ⟨preparation, tail, search⟩ := by
  unfold actionCombined
  exact congrArg
    (fun value : FoldPreparations (Step.tailInput tau matrix preparation) remaining =>
      (.combined ⟨preparation, value, search⟩ : State.Cursor tau (matrix :: remaining)))
    (restoreTail action.1.property tail)

/-- Complete a retained computed suffix using the exact selected structural step.

The returned cursor keeps the original source and child cache and stores the
actual cursor, tail and search produced by executing the selected view. -/
@[noinline, nospecialize] def finishHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (child : Cursor childSource remaining)
    (tail : FoldPreparations (Step.tailInput tau matrix preparation) remaining)
    (finished : Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        (headAction head).1.property) tail)
    (selected : Step.View tau (matrix :: remaining)
      (Step.tailCursor tau matrix remaining preparation
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
          (headAction head).1.property)))
    (selected_eq : selected = Step.View.tailFinished preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        (headAction head).1.property) tail finished) : { cursor : Cursor input (matrix :: remaining) //
      cursor.source = source ∧ cursor.original = Step.execute selected } := by
  let next := Step.execute selected
  have isCombined : ∃ search : Cached.CachedSearch tau
      (Matrix.Integral.Word.matrixProduct (matrix :: remaining)),
      next = .combined ⟨preparation, tail, search⟩ := by
    refine ⟨Cached.cachedInitial tau _, ?_⟩
    unfold next
    rw [selected_eq]
    rfl
  let actual := extractCombinedParts preparation tail next isCombined
  let actualTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
    actual.1 (headAction head).1.property.symm
  have finishedActual : Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        (headAction head).1.property) actual.1 :=
    finished.trans (congrArg some actual.2.property.2.symm)
  have completion : SuffixCompletion (headAction head) child.original actualTail :=
    completionOfTransport (headAction head).1.property child.original actual.1 finishedActual
  have sameCursor : actionCombined (headAction head) actualTail actual.2.val = next :=
    (actionCombined_selected (headAction head) actual.1 actual.2.val).trans actual.2.property.1.symm
  let cached : Cache source (matrix :: remaining) (actionCombined (headAction head) actualTail actual.2.val) :=
    .combinedHead head child.source (child.source_eq.trans childSource_eq) child.original child.cache
      actualTail completion actual.2.val
  exact ⟨⟨source, source_eq, next, sameCursor ▸ cached⟩, rfl, rfl⟩

/-- Complete a retained supplied-preparation suffix using the exact selected structural step.

The returned cursor keeps the original source, action and child cache and
stores the actual cursor, tail and search produced by the selected view. -/
@[noinline, nospecialize] def finishPreparation {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (child : Cursor childSource remaining)
    (tail : FoldPreparations (Step.tailInput tau matrix preparation) remaining)
    (finished : Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        action.1.property) tail)
    (selected : Step.View tau (matrix :: remaining)
      (Step.tailCursor tau matrix remaining preparation
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
          action.1.property)))
    (selected_eq : selected = Step.View.tailFinished preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        action.1.property) tail finished) : { cursor : Cursor input (matrix :: remaining) //
      cursor.source = source ∧ cursor.original = Step.execute selected } := by
  let next := Step.execute selected
  have isCombined : ∃ search : Cached.CachedSearch tau
      (Matrix.Integral.Word.matrixProduct (matrix :: remaining)),
      next = .combined ⟨preparation, tail, search⟩ := by
    refine ⟨Cached.cachedInitial tau _, ?_⟩
    unfold next
    rw [selected_eq]
    rfl
  let actual := extractCombinedParts preparation tail next isCombined
  let actualTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
    actual.1 action.1.property.symm
  have finishedActual : Step.TailFinished tau matrix remaining preparation
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child.original
        action.1.property) actual.1 :=
    finished.trans (congrArg some actual.2.property.2.symm)
  have completion : SuffixCompletion action child.original actualTail :=
    completionOfTransport action.1.property child.original actual.1 finishedActual
  have sameCursor : actionCombined action actualTail actual.2.val = next :=
    (actionCombined_selected action actual.1 actual.2.val).trans actual.2.property.1.symm
  let cached : Cache source (matrix :: remaining) (actionCombined action actualTail actual.2.val) :=
    .combinedPrepared rows action action_eq child.source (child.source_eq.trans childSource_eq)
      child.original child.cache actualTail completion actual.2.val
  exact ⟨⟨source, source_eq, next, sameCursor ▸ cached⟩, rfl, rfl⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
