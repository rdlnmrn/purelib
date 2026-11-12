module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Run

/-!
# Selection through retained algebraic fold evidence

The original fold selector determines each branch. When a head and its suffix
are already retained, the unfinished branch uses that head's actual output
and the same child cursor instead of reconstructing an equal channel.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Traversal

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Transporting a child to an equal channel and back returns the original child. -/
private theorem restoreChild {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (child : State.Cursor first remaining) :
    (same.symm ▸ (same ▸ child)) = child := by
  cases same
  rfl

/-- The dependent preparation and original child stored in a nonempty tail cursor. -/
@[expose] def OriginalTail (tau : CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) : Type 1 :=
  Σ preparation : Step.HeadPreparation tau matrix, State.Cursor (Step.tailInput tau matrix preparation) remaining

/-- The tail payload indexed by the same original cursor is the original action tail. -/
theorem tailPayload_eq {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (child : State.Cursor (actionOutput action) remaining)
    (payload : OriginalTail tau matrix remaining) (same : State.CursorPayload.tail payload = actionTail action child) :
    payload = ⟨preparation,
      Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child action.1.property⟩ := by
  exact State.CursorPayload.tail.inj same

/-- The dependent second component of an equal sigma retains the original value. -/
private theorem sigmaSecond {α : Type u} {family : α → Type v} (pair : Sigma family)
    (index : α) (value : family index) (same : pair = ⟨index, value⟩) :
    Eq.ndrec (motive := family) pair.2 (congrArg Sigma.fst same) = value := by
  cases same
  rfl

/-- Projected actual child transported to the retained action's original output channel. -/
@[expose] def originalTailChild {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (child : State.Cursor (actionOutput action) remaining)
    (payload : OriginalTail tau matrix remaining) (same : State.CursorPayload.tail payload = actionTail action child) :
    State.Cursor (actionOutput action) remaining :=
  let headEq := congrArg Sigma.fst (tailPayload_eq action child payload same)
  let childAtHead := Eq.ndrec (motive := fun head => State.Cursor (Step.tailInput tau matrix head) remaining)
    payload.2 headEq
  Eq.ndrec (motive := fun channel => State.Cursor channel remaining) childAtHead action.1.property.symm

/-- The actual original child is equal to the child indexing its retained cache. -/
theorem originalTailChild_eq {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (child : State.Cursor (actionOutput action) remaining)
    (payload : OriginalTail tau matrix remaining) (same : State.CursorPayload.tail payload = actionTail action child) :
    originalTailChild action child payload same = child := by
  let payloadEq := tailPayload_eq action child payload same
  have second := sigmaSecond payload preparation
    (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child action.1.property) payloadEq
  change Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
    (Eq.ndrec (motive := fun head => State.Cursor (Step.tailInput tau matrix head) remaining)
      payload.2 (congrArg Sigma.fst payloadEq)) action.1.property.symm = child
  calc
    _ = Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child action.1.property)
        action.1.property.symm :=
      congrArg (fun value => Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
        value action.1.property.symm) second
    _ = child := restoreChild action.1.property child

/-- Reuse the actual original cursor at every retained suffix. -/
@[noinline, nospecialize] private def selectActual {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    {original : State.Cursor tau matrices} (cached : Cache input matrices original)
    (actual : { value : State.Cursor tau matrices // value = original }) : Step.View tau matrices actual.val := by
  cases cached with
  | @tail _ _ matrix remaining preparation rows head childSource childSource_eq child nested =>
      match found : actual.val with
      | .tail payload =>
          have same : State.CursorPayload.tail payload = actionTail (headAction head) child :=
            found.symm.trans actual.property
          let actualChild := originalTailChild (headAction head) child payload same
          have child_eq : actualChild = child := originalTailChild_eq (headAction head) child payload same
          have payload_eq := tailPayload_eq (headAction head) child payload same
          have head_eq : payload.1 = preparation := congrArg Sigma.fst payload_eq
          have channel_eq : actionOutput (headAction head) = Step.tailInput tau matrix payload.1 :=
            (headAction head).1.property.trans (congrArg (Step.tailInput tau matrix) head_eq.symm)
          have child_transport : channel_eq.symm ▸ payload.2 = actualChild := by
            cases payload_eq
            rfl
          exact Step.selectTailWith tau matrix remaining payload.1 payload.2 (fun _ =>
            ⟨⟨actionOutput (headAction head), channel_eq⟩,
              child_transport.symm ▸ selectActual nested ⟨actualChild, child_eq⟩⟩)
      | .head _ => cases found.symm.trans actual.property
      | .combined _ => cases found.symm.trans actual.property
      | .ready _ => cases found.symm.trans actual.property
  | @preparedTail _ _ matrix remaining preparation rows action action_eq childSource childSource_eq child nested =>
      match found : actual.val with
      | .tail payload =>
          have same : State.CursorPayload.tail payload = actionTail action child :=
            found.symm.trans actual.property
          let actualChild := originalTailChild action child payload same
          have child_eq : actualChild = child := originalTailChild_eq action child payload same
          have payload_eq := tailPayload_eq action child payload same
          have head_eq : payload.1 = preparation := congrArg Sigma.fst payload_eq
          have channel_eq : actionOutput action = Step.tailInput tau matrix payload.1 :=
            action.1.property.trans (congrArg (Step.tailInput tau matrix) head_eq.symm)
          have child_transport : channel_eq.symm ▸ payload.2 = actualChild := by
            cases payload_eq
            rfl
          exact Step.selectTailWith tau matrix remaining payload.1 payload.2 (fun _ =>
            ⟨⟨actionOutput action, channel_eq⟩,
              child_transport.symm ▸ selectActual nested ⟨actualChild, child_eq⟩⟩)
      | .head _ => cases found.symm.trans actual.property
      | .combined _ => cases found.symm.trans actual.property
      | .ready _ => cases found.symm.trans actual.property
  | _ => exact Step.select tau _ actual.val

/-- Select one original fold branch while reusing its attached suffix evidence. -/
@[noinline, nospecialize] def select {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : State.Cursor tau matrices}
    (cached : Cache input matrices original) : Step.View tau matrices original :=
  selectActual cached ⟨original, rfl⟩

/-- Select using the cursor's actual retained original and attached suffix evidence. -/
def selectCursor {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) : Step.View tau matrices cursor.original :=
  selectActual cursor.cache ⟨cursor.original, rfl⟩

/-- A tail selector agrees when its retained-child execution agrees pointwise. -/
private theorem executeTail (tau : CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (head : Step.HeadPreparation tau matrix)
    (child : State.Cursor (Step.tailInput tau matrix head) remaining)
    (descend : Step.TailUnfinished tau matrix remaining head child →
      Step.TailSelection tau matrix remaining head child)
    (agree : ∀ unfinished,
      Eq.ndrec (motive := fun c => State.Cursor c remaining)
        (Step.execute (descend unfinished).2) (descend unfinished).1.property =
          Step.execute (Step.select (Step.tailInput tau matrix head) remaining child)) :
    Step.execute (Step.selectTailWith tau matrix remaining head child descend) =
      Step.step tau (matrix :: remaining) (Step.tailCursor tau matrix remaining head child) := by
  change Step.execute (Step.selectTailWith tau matrix remaining head child descend) =
    Step.execute (Step.selectTailWith tau matrix remaining head child (fun _ =>
      ⟨⟨Step.tailInput tau matrix head, rfl⟩,
        Step.select (Step.tailInput tau matrix head) remaining child⟩))
  unfold Step.selectTailWith
  split
  · rfl
  · rename_i unfinished
    change Step.tailCursor tau matrix remaining head _ = Step.tailCursor tau matrix remaining head _
    exact congrArg (Step.tailCursor tau matrix remaining head) (agree unfinished)

/-- Transporting child execution and selection along the same channel equality preserves agreement. -/
private theorem executeChild {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (child : State.Cursor first remaining) (view : Step.View first remaining child)
    (agree : Step.execute view = Step.step first remaining child) :
    Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
      (Step.execute (Eq.ndrec (motive := fun cursor => Step.View first remaining cursor)
        view (restoreChild same child).symm)) same =
      Step.execute (Step.select second remaining
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child same)) := by
  cases same
  exact agree

/-- Child execution agrees after reindexing its actual cursor and channel. -/
private theorem executeActualChild {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (child actual : State.Cursor first remaining) (actualEq : actual = child)
    (view : Step.View first remaining actual) (agree : Step.execute view = Step.step first remaining actual) :
    Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
      (Step.execute (Eq.ndrec (motive := fun cursor => Step.View first remaining cursor)
        view (actualEq.trans (restoreChild same child).symm))) same =
      Step.execute (Step.select second remaining
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child same)) := by
  cases actualEq
  exact executeChild same child view agree

/-- Executing a selection at the actual original cursor agrees with the original tick. -/
private theorem execute_selectActual {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : State.Cursor tau matrices}
    (cached : Cache input matrices original)
    (actual : { value : State.Cursor tau matrices // value = original }) :
    Step.execute (selectActual cached actual) = Step.step tau matrices actual.val := by
  induction cached with
  | @pending tau input matrices original =>
      cases matrices <;> rfl
  | @tail tau input matrix remaining preparation rows head childSource childSource_eq child nested ih =>
      cases actual with
      | mk actual same =>
          cases same
          apply executeTail
          intro unfinished
          let payload : OriginalTail tau matrix remaining := ⟨preparation,
            Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child (headAction head).1.property⟩
          let actualChild := originalTailChild (headAction head) child payload rfl
          have childEq : actualChild = child := originalTailChild_eq (headAction head) child payload rfl
          exact executeActualChild (headAction head).1.property child actualChild childEq
            (selectActual nested ⟨actualChild, childEq⟩) (ih ⟨actualChild, childEq⟩)
  | @preparedTail tau input matrix remaining preparation rows action action_eq childSource childSource_eq
      child nested ih =>
      cases actual with
      | mk actual same =>
          cases same
          apply executeTail
          intro unfinished
          let payload : OriginalTail tau matrix remaining := ⟨preparation,
            Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child action.1.property⟩
          let actualChild := originalTailChild action child payload rfl
          have childEq : actualChild = child := originalTailChild_eq action child payload rfl
          exact executeActualChild action.1.property child actualChild childEq
            (selectActual nested ⟨actualChild, childEq⟩) (ih ⟨actualChild, childEq⟩)
  | combinedHead => rfl
  | combinedPrepared => rfl
  | readyHead => rfl
  | readyPrepared => rfl

/-- Executing the cached selector agrees with the original one-tick fold execution. -/
theorem execute_select {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} {original : State.Cursor tau matrices}
    (cached : Cache input matrices original) :
    Step.execute (select cached) = Step.step tau matrices original :=
  execute_selectActual cached ⟨original, rfl⟩

/-- Executing a cursor's cached selector agrees with its original one-tick fold execution. -/
theorem execute_selectCursor {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) :
    Step.execute (selectCursor cursor) = Step.step tau matrices cursor.original :=
  execute_selectActual cursor.cache ⟨cursor.original, rfl⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Traversal

end
