module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Head
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Combined
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Tick
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded execution of algebraic fold heads

A finite attempt checks existing completion before spending fuel. Head
preflights and row decisions use separate work units; an unsupported stage
retains its exact cursor and unresolved obligation for later resumption.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- The original head preparation and its actual dependent suffix cursor. -/
private def OriginalTail (tau : CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) : Type 1 :=
  Σ preparation : Step.HeadPreparation tau matrix, State.Cursor (Step.tailInput tau matrix preparation) remaining

/-- Read the actual tail payload from the original cursor, when it has one. -/
@[noinline, nospecialize] private def Cursor.tail? {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Option (OriginalTail tau matrix remaining) :=
  match cursor.original with
  | .tail payload => some payload
  | _ => none

/-- A returned tail payload is the exact original cursor's tail. -/
private theorem Cursor.tail_sound {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (cursor : Cursor input (matrix :: remaining))
    (payload : OriginalTail tau matrix remaining) (found : cursor.tail? = some payload) :
    cursor.original = .tail payload := by
  have sound (original : State.Cursor tau (matrix :: remaining))
      (payload : OriginalTail tau matrix remaining)
      (found : (match original with | .tail value => some value | _ => none) = some payload) :
      original = .tail payload := by
    cases original with
    | head state => cases found
    | tail value =>
        have same := Option.some.inj found
        cases same
        rfl
    | combined state => cases found
    | ready preparations => cases found
  exact sound cursor.original payload found

/-- The original cursor, selected view and actual tail projection retained together. -/
@[noinline, nospecialize] private def Cursor.observeTail {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) :
    Σ retained : { value : Cursor input (matrix :: remaining) // value = cursor },
      { selected : Step.View tau (matrix :: remaining) retained.val.original //
        selected = Traversal.selectCursor retained.val } ×
      { tail : Option (OriginalTail tau matrix remaining) // tail = retained.val.tail? } :=
  ⟨⟨cursor, rfl⟩, ⟨Traversal.selectCursor cursor, rfl⟩, ⟨cursor.tail?, rfl⟩⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- Transporting an original suffix channel and returning it is identity. -/
private theorem restoreChild {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (child : State.Cursor first remaining) :
    Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
      (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child same) same.symm = child := by
  cases same
  rfl

/-- Transporting a selected suffix child does not change its executed cursor. -/
private theorem executeSelectedTransport {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (preparation : HeadPreparation tau matrix)
    (action : PreparedAction preparation) {first second : State.Cursor (actionOutput action) remaining}
    (same : first = second)
    (selected : Step.View tau (matrix :: remaining)
      (Step.tailCursor tau matrix remaining preparation
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) first action.1.property))) :
    Step.execute (Eq.ndrec (motive := fun child => Step.View tau (matrix :: remaining)
      (Step.tailCursor tau matrix remaining preparation
        (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child action.1.property)))
      selected same) = Step.execute selected := by
  cases same
  rfl

/-- Use an actual selected view and actual projected tail to advance a finished attached suffix. -/
@[noinline, nospecialize] private def advanceSelected {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (retained : Cursor input (matrix :: remaining))
    (selected : Step.View tau (matrix :: remaining) retained.original)
    (selected_eq : selected = Traversal.selectCursor retained)
    (payload : OriginalTail tau matrix remaining) (original_eq : retained.original = .tail payload) :
    Option { next : Cursor input (matrix :: remaining) // next.source = retained.source ∧
      next.original = Step.step tau (matrix :: remaining) retained.original } := by
  cases retained with
  | mk source source_eq original cache =>
    cases cache with
    | @tail _ _ _ _ preparation rows head childSource childSource_eq child nested =>
        have payload_eq : payload = ⟨preparation,
            Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child
              (headAction head).1.property⟩ := by
          apply State.CursorPayload.tail.inj
          exact original_eq.symm
        let sameHead : payload.1 = preparation := congrArg Sigma.fst payload_eq
        let nominalChild := Eq.ndrec
          (motive := fun h => State.Cursor (Step.tailInput tau matrix h) remaining) payload.2 sameHead
        let actualChild := Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
          nominalChild (headAction head).1.property.symm
        have child_eq : actualChild = child := by
          cases payload_eq
          exact restoreChild (headAction head).1.property child
        let retainedChild : Cursor childSource remaining :=
          ⟨childSource, rfl, actualChild, child_eq.symm ▸ nested⟩
        let selectedAtChild : Step.View tau (matrix :: remaining)
            (Step.tailCursor tau matrix remaining preparation
              (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) actualChild
                (headAction head).1.property)) :=
          Eq.ndrec (motive := fun childValue => Step.View tau (matrix :: remaining)
            (Step.tailCursor tau matrix remaining preparation
              (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) childValue
                (headAction head).1.property))) selected child_eq.symm
        match branch_eq : selectedAtChild with
        | .tailFinished _ _ tail finished =>
            let next := finishHead source source_eq head childSource childSource_eq retainedChild
              tail finished selectedAtChild branch_eq
            have selected_agrees : Step.execute selectedAtChild =
                Step.step tau (matrix :: remaining) (originalTail head child) := by
              exact (executeSelectedTransport preparation (headAction head) child_eq.symm selected).trans
                ((congrArg Step.execute selected_eq).trans
                  (Traversal.execute_selectCursor
                    ⟨source, source_eq, originalTail head child, .tail head childSource childSource_eq nested⟩))
            exact some ⟨next.val, next.property.1, next.property.2.trans selected_agrees⟩
        | _ => exact none
    | @preparedTail _ _ _ _ preparation rows action action_eq childSource childSource_eq child nested =>
        have payload_eq : payload = ⟨preparation,
            Eq.ndrec (motive := fun channel => State.Cursor channel remaining) child
              action.1.property⟩ := by
          apply State.CursorPayload.tail.inj
          exact original_eq.symm
        let sameHead : payload.1 = preparation := congrArg Sigma.fst payload_eq
        let nominalChild := Eq.ndrec
          (motive := fun h => State.Cursor (Step.tailInput tau matrix h) remaining) payload.2 sameHead
        let actualChild := Eq.ndrec (motive := fun channel => State.Cursor channel remaining)
          nominalChild action.1.property.symm
        have child_eq : actualChild = child := by
          cases payload_eq
          exact restoreChild action.1.property child
        let retainedChild : Cursor childSource remaining :=
          ⟨childSource, rfl, actualChild, child_eq.symm ▸ nested⟩
        let selectedAtChild : Step.View tau (matrix :: remaining)
            (Step.tailCursor tau matrix remaining preparation
              (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) actualChild
                action.1.property)) :=
          Eq.ndrec (motive := fun childValue => Step.View tau (matrix :: remaining)
            (Step.tailCursor tau matrix remaining preparation
              (Eq.ndrec (motive := fun channel => State.Cursor channel remaining) childValue
                action.1.property))) selected child_eq.symm
        match branch_eq : selectedAtChild with
        | .tailFinished _ _ tail finished =>
            let next := finishPreparation source source_eq rows action action_eq childSource childSource_eq
              retainedChild tail finished selectedAtChild branch_eq
            have selected_agrees : Step.execute selectedAtChild =
                Step.step tau (matrix :: remaining) (actionTail action child) := by
              exact (executeSelectedTransport preparation action child_eq.symm selected).trans
                ((congrArg Step.execute selected_eq).trans
                  (Traversal.execute_selectCursor
                    ⟨source, source_eq, actionTail action child,
                      .preparedTail rows action action_eq childSource childSource_eq nested⟩))
            exact some ⟨next.val, next.property.1, next.property.2.trans selected_agrees⟩
        | _ => exact none
    | _ => exact none

/-- Check whether the original cursor retains an attached suffix cache. -/
@[noinline, nospecialize] private def hasTailCache {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Bool := by
  cases cursor with
  | mk source source_eq original cache =>
    cases cache with
    | tail => exact true
    | preparedTail => exact true
    | _ => exact false

/-- Advance an attached suffix when its selected original tail has finished.

The result retains the original source and the exact selected scheduler
transition, with its actual child and nested cache. Unfinished or unattached
suffixes return no transition. -/
@[noinline, nospecialize] def advanceFinished {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) :
    Option { next : Cursor input (matrix :: remaining) // next.source = cursor.source ∧
      next.original = Step.step tau (matrix :: remaining) cursor.original } := by
  if hasTailCache cursor then
    let observed := cursor.observeTail
    match found : observed.2.2.val with
    | none => exact none
    | some payload =>
        let retained := observed.1.val
        let selected := observed.2.1.val
        have original_eq := retained.tail_sound payload (observed.2.2.property.symm.trans found)
        let next := advanceSelected retained selected observed.2.1.property payload original_eq
        exact observed.1.property ▸ next
  else exact none

/-- Every retained transition's next cursor is the original combined inspection. -/
private theorem combinedTransition_agrees {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (payload : CombinedPayload tau matrix remaining)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2) :
    transition.2.2.val =
      (Step.inspectCombined tau matrix remaining payload.1 payload.2.1 payload.2.2).2.2.val := by
  rcases transition with ⟨⟨actualSearch, sameSearch⟩, ⟨⟨result, sameResult⟩, ⟨next, nextEq⟩⟩⟩
  cases sameSearch
  cases sameResult
  exact nextEq

/-- The shared combined inspection is the original scheduler's selected tick. -/
private theorem combined_step_agrees {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (payload : CombinedPayload tau matrix remaining)
    (original : State.Cursor tau (matrix :: remaining)) (same : original = .combined payload) :
    (Step.inspectCombined tau matrix remaining payload.1 payload.2.1 payload.2.2).2.2.val =
      Step.step tau (matrix :: remaining) original := by
  cases same
  rfl

/-- The current original cursor has an attached combined cache. -/
@[noinline, nospecialize] private def hasCombinedCache {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Bool := by
  cases cursor with
  | mk source source_eq original cache =>
    cases cache with
    | combinedHead => exact true
    | combinedPrepared => exact true
    | _ => exact false

/-- Consume the actual combined observation at its attached cache. -/
@[noinline, nospecialize] private def advanceCombinedSelected {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (retained : Cursor input (matrix :: remaining)) (payload : CombinedPayload tau matrix remaining)
    (original_eq : retained.original = .combined payload)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2)
    (agree : transition.2.2.val = Step.step tau (matrix :: remaining) retained.original) :
    Option { next : Cursor input (matrix :: remaining) // next.source = retained.source ∧
      next.original = Step.step tau (matrix :: remaining) retained.original } := by
  cases retained with
  | mk source source_eq original cache =>
    cases cache with
    | @combinedHead _ _ _ _ preparation rows head childSource childSource_eq child nested tail finished search =>
        have same : State.CursorPayload.combined payload = actionCombined (headAction head) tail search :=
          original_eq.symm
        let next := advanceCombinedHead source source_eq head childSource childSource_eq child nested tail finished
          search payload same transition
        exact some ⟨next.val, next.property.1, next.property.2.trans agree⟩
    | @combinedPrepared _ _ _ _ preparation rows action action_eq childSource childSource_eq
        child nested tail finished search =>
        have same : State.CursorPayload.combined payload = actionCombined action tail search := original_eq.symm
        let next := advanceCombinedPreparation source source_eq rows action action_eq childSource childSource_eq
          child nested tail finished search payload same transition
        exact some ⟨next.val, next.property.1, next.property.2.trans agree⟩
    | _ => exact none

/-- Advance an attached combined search using its single actual inspection.

The returned cursor retains the same source and attached child history and
agrees with the original one-tick step. Unattached work remains unresolved. -/
@[noinline, nospecialize] def advanceCombined {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) :
    Option { next : Cursor input (matrix :: remaining) // next.source = cursor.source ∧
      next.original = Step.step tau (matrix :: remaining) cursor.original } := by
  if hasCombinedCache cursor then
    match observed : observeCombined cursor with
    | none => exact none
    | some observation =>
        let retained := observation.1.val
        let payload := observation.2.1.val
        let transition := observation.2.2
        have agree : transition.2.2.val = Step.step tau (matrix :: remaining) retained.original := by
          have selected := combinedTransition_agrees payload transition
          exact selected.trans (combined_step_agrees payload retained.original observation.2.1.property)
        let next := advanceCombinedSelected retained payload observation.2.1.property transition agree
        exact observation.1.property ▸ next
  else exact none

/-- The unresolved stage of a nonempty fold head.

A cursor not at a head retains its exact original cursor and proof. A suffix
frame remains available in the indexed original work; a pending decision has
no unavailable branch. -/
@[expose] def HeadBlock {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} : Work input (matrix :: remaining) → Type 1
  | .active cursor => Subtype (fun (_ : ULift.{1} Unit) => cursor.headSearch? = none)
  | .deciding .. => ULift.{1} Empty
  | .tailHead .. => ULift.{1} Unit
  | .tailPrepared .. => ULift.{1} Unit

/-- The actual next work, a zero from this work, or its unresolved stage.

A zero is indexed by the work whose retained rows produced it; an unresolved
stage carries the corresponding original work and its precise head obligation. -/
@[expose] def DispatchResult {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (work : Work input (matrix :: remaining)) : Type 1 :=
  Work input (matrix :: remaining) ⊕ Zero work ⊕ HeadBlock work

/-- Read the actual selected preflight work. -/
@[expose] def Work.PreflightWork.work {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} {observed : PendingObservation request}
    (outcome : Run.Preflight.Outcome observed) (work : Work.PreflightWork observed outcome) :
    Work input (matrix :: remaining) := by
  cases outcome with
  | inl ready => exact work.val
  | inr pending => exact work.val

/-- Perform one available head transition, retaining the actual decision and work.

An attached combined search takes one original inspection, and a completed
suffix takes its original structural tick. An original head performs its
numerical preflight, while a progressed preflight makes its retained row
decision. Other stages return their original unresolved obligation without
spending a work unit. -/
@[expose, noinline, nospecialize] def dispatchHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (work : Work input (matrix :: remaining)) : DispatchResult work := by
  match work with
  | .active cursor =>
      match advanceCombined cursor with
      | some next => exact .inl (.active next.val)
      | none =>
          match advanceFinished cursor with
          | some next => exact .inl (.active next.val)
          | none =>
              let selected := chooseHead cursor
              match selected.2 with
              | .inl ⟨_, entry⟩ => exact .inl (Work.PreflightWork.work _ entry.2.2.2)
              | .inr noHead =>
                  have absent : cursor.headSearch? = none := by
                    rw [← selected.1.property]
                    exact noHead.down
                  exact .inr (.inr ⟨⟨()⟩, absent⟩)
  | .deciding observed progressed =>
      let decision := (progressedRequest progressed).decide
      let advanced := decision.advance
      match advanced.2 with
      | .inl ⟨_, _, next⟩ => exact .inl (.active next.val)
      | .inr zero => exact .inr (.inl (.head observed progressed advanced.1.val zero))
  | .tailHead .. => exact .inr (.inr ⟨()⟩)
  | .tailPrepared .. => exact .inr (.inr ⟨()⟩)

/-- Perform the original empty-word acquisition tick using its retained source. -/
@[expose, noinline, nospecialize] def dispatchEmpty {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} (work : Work input []) : Work input [] := by
  cases work with
  | active cursor =>
      let next := Step.step tau [] cursor.original
      exact .active ⟨cursor.source, cursor.source_eq, next, .pending⟩

/-- Work expanded from an original cursor without spending a tick. -/
@[expose] def unresolvedExpansion {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (cursor : Cursor input matrices) : Work input matrices := Work.fromCursor cursor

section
attribute [local irreducible] unresolvedExpansion HeadPreparation RetainedHead headAction
  PreparedAction RowActionIdentity actionOutput actionEvidence

set_option genInjectivity false in
/-- The exact unresolved leaf and original suffix frames of a finite attempt.

An unresolved result records the original cursor, its unpaid expansion when
present, and each retained action above the original non-head leaf. -/
inductive Unresolved : {tau : CoherentNamed} → {input : Provenance.Algebraic.Sidecar tau} →
    {matrices : List IntegralMatrix} → Work input matrices → Type 1 where
  /-- The original cursor is not at a head search. -/
  | active {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (cursor : Cursor input (matrix :: remaining))
      (noHead : cursor.headSearch? = none) : Unresolved (.active cursor)
  /-- The unresolved work lies inside this original cursor's no-fuel expansion. -/
  | expanded {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrices : List IntegralMatrix} (cursor : Cursor input matrices)
      (unresolved : Unresolved (unresolvedExpansion cursor)) : Unresolved (.active cursor)
  /-- The unresolved work lies inside this retained computed suffix. -/
  | tailHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
      (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : childSource = actionEvidence (headAction head))
      (child : Work childSource remaining) (unresolved : Unresolved child) :
      Unresolved (.tailHead source source_eq head childSource childSource_eq child)
  /-- The unresolved work lies inside this retained supplied-preparation suffix. -/
  | tailPrepared {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : childSource = actionEvidence action)
      (child : Work childSource remaining) (unresolved : Unresolved child) :
      Unresolved (.tailPrepared source source_eq rows action action_eq childSource childSource_eq child)

constructive_injectivity Unresolved
end

/-- The exact selected transition or unresolved reason for retained work. -/
@[expose] def RecursiveResult {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) : Type 1 :=
  Work input matrices ⊕ Zero work ⊕ Unresolved work

/-- A child work unit either advances, finds its exact zero, or remains blocked. -/
private def ChildResult {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (child : Work input matrices) : Type 1 :=
  Work input matrices ⊕ Zero child ⊕ Unresolved child

/-- Retain the child's exact next work, zero or unresolved reason. -/
private def childResult {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} {child : Work input (matrix :: remaining)}
    (result : RecursiveResult child) : ChildResult child :=
  match result with
  | .inl next => .inl next
  | .inr (.inl zero) => .inr (.inl zero)
  | .inr (.inr unresolved) => .inr (.inr unresolved)

/-- Take one original computed-head frame tick, descending only when its suffix is unfinished. -/
@[noinline, nospecialize] private def dispatchHeadFrame {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head)) (child : Work childSource remaining)
    (descend : Unit → ChildResult child) :
    RecursiveResult (.tailHead source source_eq head childSource childSource_eq child) := by
  let work := Work.tailHead source source_eq head childSource childSource_eq child
  match advanceFinished work.current with
  | some next => exact .inl (.active next.val)
  | none =>
      match descend () with
      | .inl next => exact .inl (.tailHead source source_eq head childSource childSource_eq next)
      | .inr (.inl zero) => exact .inr (.inl (.tailHead source source_eq head childSource childSource_eq child zero))
      | .inr (.inr unresolved) =>
          exact .inr (.inr (.tailHead source source_eq head childSource childSource_eq child unresolved))

/-- Take one supplied-preparation frame tick, descending only when its suffix is unfinished. -/
@[noinline, nospecialize] private def dispatchPreparedFrame {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action) (child : Work childSource remaining)
    (descend : Unit → ChildResult child) :
    RecursiveResult (.tailPrepared source source_eq rows action action_eq childSource childSource_eq child) := by
  let work := Work.tailPrepared source source_eq rows action action_eq childSource childSource_eq child
  match advanceFinished work.current with
  | some next => exact .inl (.active next.val)
  | none =>
      match descend () with
      | .inl next => exact .inl (.tailPrepared source source_eq rows action action_eq childSource childSource_eq next)
      | .inr (.inl zero) =>
          exact .inr (.inl (.tailPrepared source source_eq rows action action_eq childSource childSource_eq child zero))
      | .inr (.inr unresolved) =>
          exact .inr (.inr (.tailPrepared source source_eq rows action action_eq
            childSource childSource_eq child unresolved))

/-- Descend one paid work unit through the retained suffix frames.

A finished suffix takes its structural transition without inspecting a child.
An unfinished suffix takes one child work unit and retains its parent frames;
any zero or unresolved reason is wrapped through those same original frames. -/
@[noinline, nospecialize] def dispatchRecursive : (remaining : List IntegralMatrix) →
    {tau : CoherentNamed} → {input : Provenance.Algebraic.Sidecar tau} → {matrix : IntegralMatrix} →
    (work : Work input (matrix :: remaining)) → RecursiveResult work
  | remaining, _, _, _, work => by
    match result : dispatchHead work with
    | .inl next => exact .inl next
    | .inr (.inl zero) => exact .inr (.inl zero)
    | .inr (.inr blocked) =>
      let descend {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
          (child : Work input remaining) : ChildResult child := by
        cases remaining with
        | nil => exact .inl (dispatchEmpty child)
        | cons matrix rest => exact childResult (dispatchRecursive rest child)
      match work with
      | .tailHead source source_eq head childSource childSource_eq child =>
          exact dispatchHeadFrame source source_eq head childSource childSource_eq child (fun _ => descend child)
      | .tailPrepared source source_eq rows action action_eq childSource childSource_eq child =>
          exact dispatchPreparedFrame source source_eq rows action action_eq childSource childSource_eq child
            (fun _ => descend child)
      | .active cursor =>
          match expanded : Work.fromCursor cursor with
          | .tailHead source source_eq head childSource childSource_eq child =>
              match dispatchHeadFrame source source_eq head childSource childSource_eq child
                  (fun _ => descend child) with
              | .inl next => exact .inl next
              | .inr (.inl zero) =>
                  have expandedZero : Zero (Work.fromCursor cursor) := expanded.symm ▸ zero
                  exact False.elim (Zero.notExpansion cursor expandedZero)
              | .inr (.inr unresolved) =>
                  have expandedBlocked : Unresolved (unresolvedExpansion cursor) := by
                    change Unresolved (Work.fromCursor cursor)
                    exact expanded.symm ▸ unresolved
                  exact .inr (.inr (.expanded cursor expandedBlocked))
          | .tailPrepared source source_eq rows action action_eq childSource childSource_eq child =>
              match dispatchPreparedFrame source source_eq rows action action_eq childSource childSource_eq child
                  (fun _ => descend child) with
              | .inl next => exact .inl next
              | .inr (.inl zero) =>
                  have expandedZero : Zero (Work.fromCursor cursor) := expanded.symm ▸ zero
                  exact False.elim (Zero.notExpansion cursor expandedZero)
              | .inr (.inr unresolved) =>
                  have expandedBlocked : Unresolved (unresolvedExpansion cursor) := by
                    change Unresolved (Work.fromCursor cursor)
                    exact expanded.symm ▸ unresolved
                  exact .inr (.inr (.expanded cursor expandedBlocked))
          | _ => exact .inr (.inr (.active cursor blocked.property))
      | .deciding .. => exact False.elim (Empty.elim blocked.down)

set_option genInjectivity false in
/-- The outcome of a bounded acquisition, retaining its actual stopped work.

Success carries the original finished cursor. Exhaustion and unresolved stages
retain the unfinished cursor for resumption; zero carries the actual row
decision obstruction. -/
inductive BoundedResult : {tau : CoherentNamed} → (input : Provenance.Algebraic.Sidecar tau) →
    (matrices : List IntegralMatrix) → Type 1 where
  /-- The actual current cursor carries completed preparations. -/
  | ready {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
      (work : Work input matrices) (cursor : Cursor input matrices) (current : cursor = work.current)
      (preparations : FoldPreparations tau matrices)
      (finished : State.finished? tau matrices cursor.original = some preparations) : BoundedResult input matrices
  /-- The supplied budget ended with this work still pending. -/
  | exhausted {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
      (work : Work input matrices) (cursor : Cursor input matrices) (current : cursor = work.current)
      (unfinished : State.finished? tau matrices cursor.original = none) : BoundedResult input matrices
  /-- The selected rows returned this exact obstruction. -/
  | zero {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
      (work : Work input matrices) (obstruction : Zero work) : BoundedResult input matrices
  /-- The exact current nonempty work and its unresolved stage. -/
  | blocked {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      (work : Work input (matrix :: remaining)) (cursor : Cursor input (matrix :: remaining))
      (current : cursor = work.current)
      (unfinished : State.finished? tau (matrix :: remaining) cursor.original = none)
      (obligation : Unresolved work) :
      BoundedResult input (matrix :: remaining)

/-- Execute at most the supplied work budget, retaining the actual unused portion.

Completion is checked before each work unit, including at zero fuel. An
unfinished or unattached suffix stops with its unpaid work rather than
reconstructing missing cache history. -/
@[expose] def attemptBody {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) : (fuel : Nat) →
    { result : Nat × BoundedResult input matrices // result.1 ≤ fuel }
  | 0 => by
    let cursor := work.current
    match finished : State.finished? tau matrices cursor.original with
    | some preparations => exact ⟨⟨0, .ready work cursor rfl preparations finished⟩, Nat.le_refl 0⟩
    | none => exact ⟨⟨0, .exhausted work cursor rfl finished⟩, Nat.le_refl 0⟩
  | fuel + 1 => by
    let cursor := work.current
    match finished : State.finished? tau matrices cursor.original with
    | some preparations => exact ⟨⟨fuel + 1, .ready work cursor rfl preparations finished⟩, Nat.le_refl _⟩
    | none =>
      cases matrices with
      | nil =>
          let result := attemptBody (dispatchEmpty work) fuel
          exact ⟨result.val, Nat.le_succ_of_le result.property⟩
      | cons matrix remaining =>
        match dispatchRecursive remaining work with
        | .inl next =>
            let result := attemptBody next fuel
            exact ⟨result.val, Nat.le_succ_of_le result.property⟩
        | .inr (.inl zero) => exact ⟨⟨fuel, .zero work zero⟩, Nat.le_succ fuel⟩
        | .inr (.inr obligation) => exact ⟨⟨fuel + 1, .blocked work cursor rfl finished obligation⟩, Nat.le_refl _⟩

/-- Run a finite budget and retain the exact result of that attempt.

The result includes the unused budget, its bound by the requested fuel, and
the exact retained work or completed preparation. -/
@[expose, noinline, nospecialize] def attempt {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrices : List IntegralMatrix}
    (work : Work input matrices) (fuel : Nat) :
    { result : { result : Nat × BoundedResult input matrices // result.1 ≤ fuel } //
      result = attemptBody work fuel } := ⟨attemptBody work fuel, rfl⟩


/-- A finished cursor returns the same preparation and all its supplied fuel. -/
private theorem attemptBody_ready_value {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) (fuel : Nat)
    (preparations : FoldPreparations tau matrices)
    (finished : State.finished? tau matrices work.current.original = some preparations) :
    (attemptBody work fuel).val = (fuel, .ready work work.current rfl preparations finished) := by
  cases fuel with
  | zero =>
    unfold attemptBody
    dsimp only
    split
    next actual selected =>
      cases Option.some.inj (selected.symm.trans finished)
      rfl
    next selected => cases selected.symm.trans finished
  | succ fuel =>
    unfold attemptBody
    dsimp only
    split
    next actual selected =>
      cases Option.some.inj (selected.symm.trans finished)
      rfl
    next selected => cases selected.symm.trans finished

/-- An unfinished cursor at zero fuel retains its original work. -/
private theorem attemptBody_exhausted_zero {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices)
    (finished : State.finished? tau matrices work.current.original = none) :
    (attemptBody work 0).val = (0, .exhausted work work.current rfl finished) := by
  unfold attemptBody
  dsimp only
  split
  next actual selected => cases selected.symm.trans finished
  next selected => rfl

/-- An unfinished empty word takes its original single tick. -/
private theorem attemptBody_empty_next {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    (work : Work input []) (fuel : Nat)
    (finished : State.finished? tau [] work.current.original = none) :
    (attemptBody work (fuel + 1)).val = (attemptBody (dispatchEmpty work) fuel).val := by
  conv_lhs => unfold attemptBody; dsimp only
  split
  next actual selected => cases selected.symm.trans finished
  next selected => rfl

/-- An advancing nonempty word resumes at its actual next work. -/
private theorem attemptBody_nonempty_next {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (work : Work input (matrix :: remaining))
    (fuel : Nat) (finished : State.finished? tau (matrix :: remaining) work.current.original = none)
    (next : Work input (matrix :: remaining)) (selected : dispatchRecursive remaining work = .inl next) :
    (attemptBody work (fuel + 1)).val = (attemptBody next fuel).val := by
  conv_lhs => unfold attemptBody; dsimp only
  split
  next actual selectedFinished => cases selectedFinished.symm.trans finished
  next selectedFinished =>
    split
    next actual found => cases Sum.inl.inj (found.symm.trans selected); rfl
    next actual found => cases found.symm.trans selected
    next actual found => cases found.symm.trans selected

/-- A selected row obstruction retains its exact decision and unused fuel. -/
private theorem attemptBody_nonempty_zero {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (work : Work input (matrix :: remaining))
    (fuel : Nat) (finished : State.finished? tau (matrix :: remaining) work.current.original = none)
    (zero : Zero work) (selected : dispatchRecursive remaining work = .inr (.inl zero)) :
    (attemptBody work (fuel + 1)).val = (fuel, .zero work zero) := by
  conv_lhs => unfold attemptBody; dsimp only
  split
  next actual selectedFinished => cases selectedFinished.symm.trans finished
  next selectedFinished =>
    split
    next actual found => cases found.symm.trans selected
    next actual found => cases Sum.inl.inj (Sum.inr.inj (found.symm.trans selected)); rfl
    next actual found => cases Sum.inr.inj (found.symm.trans selected)

/-- An unresolved stage retains its original work and all unused fuel. -/
private theorem attemptBody_nonempty_blocked {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (work : Work input (matrix :: remaining))
    (fuel : Nat) (finished : State.finished? tau (matrix :: remaining) work.current.original = none)
    (obligation : Unresolved work) (selected : dispatchRecursive remaining work = .inr (.inr obligation)) :
    (attemptBody work (fuel + 1)).val =
      (fuel + 1, .blocked work work.current rfl finished obligation) := by
  conv_lhs => unfold attemptBody; dsimp only
  split
  next actual selectedFinished => cases selectedFinished.symm.trans finished
  next selectedFinished =>
    split
    next actual found => cases found.symm.trans selected
    next actual found => cases Sum.inr.inj (found.symm.trans selected)
    next actual found => cases Sum.inr.inj (Sum.inr.inj (found.symm.trans selected)); rfl

/-- Splitting a budget preserves the complete result and every unused unit.

An exhausted first attempt resumes its exact retained work with the second
budget. A ready, zero or blocked result remains unchanged, with the second
budget added to its original unused fuel. -/
theorem attemptBody_add {tau : CoherentNamed} {input : Algebraic.Sidecar tau}
    {matrices : List IntegralMatrix} (work : Work input matrices) (first second : Nat) :
    (attemptBody work (first + second)).val =
      match (attemptBody work first).val with
      | (_, .exhausted saved _ _ _) => (attemptBody saved second).val
      | (unused, stopped) => (unused + second, stopped) := by
  induction first generalizing work with
  | zero =>
      cases finished : State.finished? tau matrices work.current.original with
      | none =>
          rw [Nat.zero_add, attemptBody_exhausted_zero work finished]
      | some preparations =>
          rw [Nat.zero_add, attemptBody_ready_value work 0 preparations finished,
            attemptBody_ready_value work second preparations finished]
          simp only [Nat.zero_add, -eq_self, -iff_self]
          rfl
  | succ first ih =>
      cases finished : State.finished? tau matrices work.current.original with
      | some preparations =>
          rw [attemptBody_ready_value work (Nat.succ first + second) preparations finished,
            attemptBody_ready_value work (Nat.succ first) preparations finished]
      | none =>
          cases matrices with
          | nil =>
              rw [Nat.succ_add, attemptBody_empty_next work (first + second) finished,
                attemptBody_empty_next work first finished]
              exact ih (dispatchEmpty work)
          | cons matrix remaining =>
              cases selected : dispatchRecursive remaining work with
              | inl next =>
                  rw [Nat.succ_add, attemptBody_nonempty_next work (first + second) finished next selected,
                    attemptBody_nonempty_next work first finished next selected]
                  exact ih next
              | inr stopped =>
                  cases stopped with
                  | inl zero =>
                      rw [Nat.succ_add, attemptBody_nonempty_zero work (first + second) finished zero selected,
                        attemptBody_nonempty_zero work first finished zero selected]
                  | inr blocked =>
                      rw [Nat.succ_add, attemptBody_nonempty_blocked work (first + second) finished blocked selected,
                        attemptBody_nonempty_blocked work first finished blocked selected]
                      simp only [Nat.succ_add, -eq_self, -iff_self]
                      rfl

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
