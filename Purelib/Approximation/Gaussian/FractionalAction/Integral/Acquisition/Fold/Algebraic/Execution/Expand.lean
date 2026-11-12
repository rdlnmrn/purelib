module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

/-!
# Retained work from an original fractional-fold cursor

An attached suffix becomes a work frame using its actual stored child source,
child cursor and nested cache. Other stages remain their original active cursor.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Read the actual original tail and certify its identity with the specified tail. -/
@[expose, noinline, nospecialize] def Cursor.actualTail {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (payload : Traversal.OriginalTail tau matrix remaining)
    (atTail : cursor.original = .tail payload) : { actual : Traversal.OriginalTail tau matrix remaining //
      actual = payload } := by
  match found : cursor.original with
  | .tail actual => exact ⟨actual, State.CursorPayload.tail.inj (found.symm.trans atTail)⟩
  | .head _ => cases found.symm.trans atTail
  | .combined _ => cases found.symm.trans atTail
  | .ready _ => cases found.symm.trans atTail

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Changing only an equal original child preserves the complete computed frame. -/
theorem Work.current_tailHead_of_child {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (actual child : State.Cursor (actionOutput (headAction head)) remaining) (same : actual = child)
    (nested : Cache childSource remaining child) :
    (Work.tailHead source source_eq head childSource childSource_eq
      (.active ⟨childSource, rfl, actual, same.symm ▸ nested⟩)).current =
      (⟨source, source_eq, originalTail head child, .tail head childSource childSource_eq nested⟩ :
        Cursor input (matrix :: remaining)) := by
  cases same
  rfl

/-- Changing only an equal original child preserves the complete prepared frame. -/
theorem Work.current_tailPrepared_of_child {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (actual child : State.Cursor (actionOutput action) remaining) (same : actual = child)
    (nested : Cache childSource remaining child) :
    (Work.tailPrepared source source_eq rows action action_eq childSource childSource_eq
      (.active ⟨childSource, rfl, actual, same.symm ▸ nested⟩)).current =
      (⟨source, source_eq, actionTail action child,
        .preparedTail rows action action_eq childSource childSource_eq nested⟩ :
        Cursor input (matrix :: remaining)) := by
  cases same
  rfl

/-- Expand a supplied tail payload while retaining its child and attached cache.

The payload is supplied by the caller and is linked to the cursor by equality.
The work retains its child and the original source and action; every result
reads back the supplied cursor. -/
@[expose, noinline, nospecialize] def Work.fromSuppliedTail {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (payload : Traversal.OriginalTail tau matrix remaining)
    (atTail : cursor.original = .tail payload) :
    Option { work : Work input (matrix :: remaining) // work.current = cursor } := by
  cases cursor with
  | mk source source_eq original cache =>
    cases cache with
    | @tail _ _ _ _ preparation rows head childSource childSource_eq child nested =>
        have same : State.CursorPayload.tail payload = actionTail (headAction head) child := atTail.symm
        let actual := Traversal.originalTailChild (headAction head) child payload same
        have child_eq : actual = child := Traversal.originalTailChild_eq (headAction head) child payload same
        let work := Work.tailHead source source_eq head childSource childSource_eq
          (.active ⟨childSource, rfl, actual, child_eq.symm ▸ nested⟩)
        exact some ⟨work, Work.current_tailHead_of_child source source_eq head childSource childSource_eq
          actual child child_eq nested⟩
    | @preparedTail _ _ _ _ preparation rows action action_eq childSource childSource_eq child nested =>
        have same : State.CursorPayload.tail payload = actionTail action child := atTail.symm
        let actual := Traversal.originalTailChild action child payload same
        have child_eq : actual = child := Traversal.originalTailChild_eq action child payload same
        let work := Work.tailPrepared source source_eq rows action action_eq childSource childSource_eq
          (.active ⟨childSource, rfl, actual, child_eq.symm ▸ nested⟩)
        exact some ⟨work,
          Work.current_tailPrepared_of_child source source_eq rows action action_eq childSource childSource_eq
            actual child child_eq nested⟩
    | _ => exact none

/-- Expand the actual original tail while retaining that exact child and attached cache.

The child is projected from the cursor itself. An unattached suffix returns no
expansion, and every result reads back the same complete cursor. -/
@[expose, noinline, nospecialize] def Work.fromActualTail {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (payload : Traversal.OriginalTail tau matrix remaining)
    (atTail : cursor.original = .tail payload) :
    Option { work : Work input (matrix :: remaining) // work.current = cursor } := by
  let actual := cursor.actualTail payload atTail
  have actualAtTail : cursor.original = .tail actual.val :=
    atTail.trans (congrArg State.CursorPayload.tail actual.property.symm)
  exact Work.fromSuppliedTail cursor actual.val actualAtTail

/-- Convert one original retained cursor to work without inspecting a denominator.

Attached suffixes retain the exact action, child source, original child cursor
and nested cache. Unattached, combined and ready cursors remain active. -/
@[expose, noinline, nospecialize] def Work.fromCursor : {tau : CoherentNamed} →
    {input : Provenance.Algebraic.Sidecar tau} → {matrices : List IntegralMatrix} →
    Cursor input matrices → Work input matrices
  | _, _, [], cursor => .active cursor
  | _, _, _ :: _, cursor => by
      match found : cursor.original with
      | .tail payload =>
          match Work.fromSuppliedTail cursor payload found with
          | some work => exact work.val
          | none => exact .active cursor
      | _ => exact .active cursor

/-- Reading the converted work returns the complete original cursor. -/
theorem Work.current_fromCursor {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) :
    (Work.fromCursor cursor).current = cursor := by
  cases matrices with
  | nil => rfl
  | cons matrix remaining =>
    change (match found : cursor.original with
      | .tail payload =>
          match Work.fromSuppliedTail cursor payload found with
          | some work => work.val
          | none => .active cursor
      | _ => .active cursor).current = cursor
    split
    next payload found =>
      split
      next work selected => exact work.property
      next selected => rfl
    all_goals rfl

/-- The original cursor and the work converted from that same cursor. -/
@[expose] def Work.Expansion {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) : Type 1 :=
  Σ retained : { value : Cursor input matrices // value = cursor },
    { work : Work input matrices // work.current = retained.val }

/-- Retain an original cursor and convert it once to corresponding work. -/
@[expose, noinline, nospecialize] def Work.expand {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (cursor : Cursor input matrices) : Work.Expansion cursor :=
  ⟨⟨cursor, rfl⟩, ⟨Work.fromCursor cursor, Work.current_fromCursor cursor⟩⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
