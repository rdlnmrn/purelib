module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Snapshot
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word

/-!
# Retained combined acquisition

A combined observation retains the actual original search, one finite
inspection and its returned cursor. Continuing either cached head kind keeps
its original child history and uses the observed result without replay.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra
open Matrix.Basic (IntegralMatrix)

/-- The actual head, suffix and search in an original combined cursor. -/
@[expose] def CombinedPayload (tau : CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) : Type 1 :=
  Σ head : Step.HeadPreparation tau matrix,
    Σ _tail : FoldPreparations (Step.tailInput tau matrix head) remaining,
      Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining))

/-- The actual combined payload is tied to the cached action, suffix and search. -/
private theorem combinedPayload_eq {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (tail : FoldPreparations (actionOutput action) remaining)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined action tail search) :
    payload = ⟨preparation,
      Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail action.1.property, search⟩ := by
  exact State.CursorPayload.combined.inj same

/-- The dependent second component of an equal sigma retains the original value. -/
private theorem sigmaSecond {α : Type u} {family : α → Type v} (pair : Sigma family)
    (index : α) (value : family index) (same : pair = ⟨index, value⟩) :
    Eq.ndrec (motive := family) pair.2 (congrArg Sigma.fst same) = value := by
  cases same
  rfl

/-- Reversing and restoring one suffix transport keeps the original preparation. -/
private theorem restoreActualTail {first second : CoherentNamed} {remaining : List IntegralMatrix}
    (same : first = second) (tail : FoldPreparations first remaining) :
    Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
      (Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail same) same.symm = tail := by
  cases same
  rfl

/-- Projected actual suffix transported to the retained action output. -/
private def originalCombinedTail {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (tail : FoldPreparations (actionOutput action) remaining)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined action tail search) :
    FoldPreparations (actionOutput action) remaining :=
  let headEq := congrArg Sigma.fst (combinedPayload_eq action tail search payload same)
  let pairAtHead := Eq.ndrec (motive := fun head =>
    Σ _tail : FoldPreparations (Step.tailInput tau matrix head) remaining,
      Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining))) payload.2 headEq
  Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) pairAtHead.1 action.1.property.symm

/-- The projected suffix is equal to the suffix indexing its retained cache. -/
private theorem originalCombinedTail_eq {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (tail : FoldPreparations (actionOutput action) remaining)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined action tail search) :
    originalCombinedTail action tail search payload same = tail := by
  let payloadEq := combinedPayload_eq action tail search payload same
  have second := sigmaSecond payload preparation
    ⟨Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail action.1.property, search⟩ payloadEq
  have actualTail := congrArg Sigma.fst second
  change Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
    (Eq.ndrec (motive := fun head =>
      Σ _tail : FoldPreparations (Step.tailInput tau matrix head) remaining,
        Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining))) payload.2
      (congrArg Sigma.fst payloadEq)).1 action.1.property.symm = tail
  calc
    _ = Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        (Eq.ndrec (motive := fun channel => FoldPreparations channel remaining) tail action.1.property)
        action.1.property.symm :=
      congrArg (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        value action.1.property.symm) actualTail
    _ = tail := restoreActualTail action.1.property tail

/-- The actual combined inspection retained with its original cursor and payload. -/
@[expose] def CombinedObservation {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Type 1 :=
  Σ retained : { value : Cursor input (matrix :: remaining) // value = cursor },
    Σ payload : { value : CombinedPayload tau matrix remaining // retained.val.original = .combined value },
      Step.CombinedTransition tau matrix remaining payload.val.1 payload.val.2.1 payload.val.2.2

/-- Inspect the original combined search once, when that cursor is at its combined stage.

The observation keeps the original cursor and payload together with the single
shared inspection and its actual returned cursor. -/
@[expose, noinline, nospecialize] def observeCombined {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Option (CombinedObservation cursor) := by
  match found : cursor.original with
  | .combined payload =>
      let observed := Step.inspectCombined tau matrix remaining payload.1 payload.2.1 payload.2.2
      exact some ⟨⟨cursor, rfl⟩, ⟨payload, found⟩, observed⟩
  | _ => exact none


/-- Extract the actual suffix and combined preparation from the returned ready cursor. -/
@[noinline] private def extractReadyParts {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (head : Step.HeadPreparation tau matrix)
    (tail : FoldPreparations (Step.tailInput tau matrix head) remaining)
    (combined : HeadPreparation tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (next : State.Cursor tau (matrix :: remaining)) (isReady : next = .ready ⟨head, tail, combined⟩) :
    Σ actualTail : FoldPreparations (Step.tailInput tau matrix head) remaining,
      { actualCombined : HeadPreparation tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)) //
        next = .ready ⟨head, actualTail, actualCombined⟩ ∧ actualTail = tail ∧ actualCombined = combined } := by
  cases next with
  | head value => cases isReady
  | tail value => cases isReady
  | combined value => cases isReady
  | ready value =>
      obtain ⟨actualHead, actualTail, actualCombined⟩ := value
      have sameHead : actualHead = head := by cases isReady; rfl
      let retainedTail : FoldPreparations (Step.tailInput tau matrix head) remaining :=
        Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining) actualTail sameHead
      refine ⟨retainedTail, ⟨actualCombined, ?_⟩⟩
      cases isReady
      exact ⟨rfl, rfl, rfl⟩

/-- Projecting a transported sigma preserves its transported first component. -/
private theorem sigmaFirstTransport {α : Type u} {first : α → Type v} {second : α → Type w}
    {a b : α} (pair : Σ _ : first a, second a) (same : a = b) :
    (Eq.ndrec (motive := fun value => Σ _ : first value, second value) pair same).1 =
      Eq.ndrec (motive := first) pair.1 same := by
  cases same
  rfl

/-- Attach the actual combined result to the retained computed suffix. -/
@[noinline, nospecialize] private def consumeReadyHeadWith {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (child : State.Cursor (actionOutput (headAction head)) remaining)
    (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput (headAction head)) remaining)
    (finished : SuffixCompletion (headAction head) child tail)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined (headAction head) tail search)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2)
    (original : State.Cursor tau (matrix :: remaining))
    (next_eq : original = Step.combinedNext tau matrix remaining payload.1 payload.2.1
      transition.1.val transition.2.1.val) :
    { result : Cursor input (matrix :: remaining) //
      result.source = source ∧ result.original = original } := by
  let actualTail := originalCombinedTail (headAction head) tail search payload same
  have tail_eq : actualTail = tail := originalCombinedTail_eq (headAction head) tail search payload same
  have finishedActual : SuffixCompletion (headAction head) child actualTail :=
    finished.trans (congrArg some tail_eq.symm)
  match branch : transition.2.1.val with
  | .ready ready =>
      let actualSearch := transition.1.val
      have isReady : original = .ready ⟨payload.1, payload.2.1, searchPreparation actualSearch ready⟩ := by
        rw [branch] at next_eq
        exact next_eq
      let actual := extractReadyParts payload.1 payload.2.1 (searchPreparation actualSearch ready) original isReady
      have payload_eq := combinedPayload_eq (headAction head) tail search payload same
      let head_eq := congrArg Sigma.fst payload_eq
      let tailAtHead := Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
        actual.1 head_eq
      let nextTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        tailAtHead (headAction head).1.property.symm
      have nextTail_eq : nextTail = tail := by
        have atHead := congrArg
          (fun value => Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
            value head_eq) actual.2.property.2.1
        have atOutput := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value (headAction head).1.property.symm) atHead
        have pair_eq := sigmaFirstTransport
          (first := fun h : Step.HeadPreparation tau matrix => FoldPreparations (Step.tailInput tau matrix h) remaining)
          (second := fun _ => Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
          payload.2 head_eq
        have restore := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value (headAction head).1.property.symm) pair_eq.symm
        exact atOutput.trans (restore.trans tail_eq)
      have finishedNext : SuffixCompletion (headAction head) child nextTail :=
        finished.trans (congrArg some nextTail_eq.symm)
      let cached : Cache source (matrix :: remaining)
          (actionReady (headAction head) nextTail (searchPreparation actualSearch ready)) :=
        .readyHead head childSource childSource_eq child nested nextTail finishedNext actualSearch ready
      have original_eq :
          actionReady (headAction head) nextTail (searchPreparation actualSearch ready) = original := by
        rw [nextTail_eq]
        rw [branch] at next_eq
        cases payload_eq
        exact next_eq.symm
      exact ⟨⟨source, source_eq, original, original_eq ▸ cached⟩, rfl, rfl⟩
  | .progressed next _ =>
      have isCombined : ∃ nextSearch : Cached.CachedSearch tau
          (Matrix.Integral.Word.matrixProduct (matrix :: remaining)),
          original = .combined ⟨payload.1, payload.2.1, nextSearch⟩ := by
        rw [branch] at next_eq
        exact ⟨{ transition.1.val with search := next }, next_eq⟩
      let actual := extractCombinedParts payload.1 payload.2.1 original isCombined
      have payload_eq := combinedPayload_eq (headAction head) tail search payload same
      let head_eq := congrArg Sigma.fst payload_eq
      let tailAtHead := Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
        actual.1 head_eq
      let nextTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        tailAtHead (headAction head).1.property.symm
      have nextTail_eq : nextTail = tail := by
        have atHead := congrArg
          (fun value => Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
            value head_eq) actual.2.property.2
        have atOutput := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value (headAction head).1.property.symm) atHead
        have pair_eq := sigmaFirstTransport
          (first := fun h : Step.HeadPreparation tau matrix => FoldPreparations (Step.tailInput tau matrix h) remaining)
          (second := fun _ => Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
          payload.2 head_eq
        have restore := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value (headAction head).1.property.symm) pair_eq.symm
        exact atOutput.trans (restore.trans tail_eq)
      have finishedNext : SuffixCompletion (headAction head) child nextTail :=
        finished.trans (congrArg some nextTail_eq.symm)
      have original_eq : actionCombined (headAction head) nextTail actual.2.val = original := by
        rw [nextTail_eq]
        let nextSearch := actual.2.val
        have combined_eq : original = .combined ⟨payload.1, payload.2.1, nextSearch⟩ :=
          actual.2.property.1.trans (congrArg
            (fun value : FoldPreparations (Step.tailInput tau matrix payload.1) remaining =>
              (.combined ⟨payload.1, value, nextSearch⟩ : State.Cursor tau (matrix :: remaining)))
            actual.2.property.2)
        cases payload_eq
        exact combined_eq.symm
      let cached : Cache source (matrix :: remaining)
          (actionCombined (headAction head) nextTail actual.2.val) :=
        .combinedHead head childSource childSource_eq child nested nextTail finishedNext actual.2.val
      exact ⟨⟨source, source_eq, original, original_eq ▸ cached⟩, rfl, rfl⟩

/-- Continue a retained computed suffix using its exact observed combined transition.

Both progressed and prepared results retain the original child cache and use
the actual returned cursor and its tail or search without another inspection. -/
@[noinline, nospecialize] def advanceCombinedHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows source matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : childSource = actionEvidence (headAction head))
    (child : State.Cursor (actionOutput (headAction head)) remaining)
    (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput (headAction head)) remaining)
    (finished : SuffixCompletion (headAction head) child tail)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined (headAction head) tail search)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2) :
    { result : Cursor input (matrix :: remaining) //
      result.source = source ∧ result.original = transition.2.2.val } :=
  consumeReadyHeadWith source source_eq head childSource childSource_eq child nested tail finished search
    payload same transition transition.2.2.val transition.2.2.property

/-- Attach the actual combined result to the retained supplied-preparation suffix. -/
@[noinline, nospecialize] private def consumeReadyPreparationWith {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (child : State.Cursor (actionOutput action) remaining)
    (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput action) remaining)
    (finished : SuffixCompletion action child tail)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined action tail search)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2)
    (original : State.Cursor tau (matrix :: remaining))
    (next_eq : original = Step.combinedNext tau matrix remaining payload.1 payload.2.1
      transition.1.val transition.2.1.val) :
    { result : Cursor input (matrix :: remaining) //
      result.source = source ∧ result.original = original } := by
  let actualTail := originalCombinedTail action tail search payload same
  have tail_eq : actualTail = tail := originalCombinedTail_eq action tail search payload same
  have finishedActual : SuffixCompletion action child actualTail :=
    finished.trans (congrArg some tail_eq.symm)
  match branch : transition.2.1.val with
  | .ready ready =>
      let actualSearch := transition.1.val
      have isReady : original = .ready ⟨payload.1, payload.2.1, searchPreparation actualSearch ready⟩ := by
        rw [branch] at next_eq
        exact next_eq
      let actual := extractReadyParts payload.1 payload.2.1 (searchPreparation actualSearch ready) original isReady
      have payload_eq := combinedPayload_eq action tail search payload same
      let head_eq := congrArg Sigma.fst payload_eq
      let tailAtHead := Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
        actual.1 head_eq
      let nextTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        tailAtHead action.1.property.symm
      have nextTail_eq : nextTail = tail := by
        have atHead := congrArg
          (fun value => Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
            value head_eq) actual.2.property.2.1
        have atOutput := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value action.1.property.symm) atHead
        have pair_eq := sigmaFirstTransport
          (first := fun h : Step.HeadPreparation tau matrix => FoldPreparations (Step.tailInput tau matrix h) remaining)
          (second := fun _ => Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
          payload.2 head_eq
        have restore := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value action.1.property.symm) pair_eq.symm
        exact atOutput.trans (restore.trans tail_eq)
      have finishedNext : SuffixCompletion action child nextTail :=
        finished.trans (congrArg some nextTail_eq.symm)
      let cached : Cache source (matrix :: remaining)
          (actionReady action nextTail (searchPreparation actualSearch ready)) :=
        .readyPrepared rows action action_eq childSource childSource_eq child nested
          nextTail finishedNext actualSearch ready
      have original_eq :
          actionReady action nextTail (searchPreparation actualSearch ready) = original := by
        rw [nextTail_eq]
        rw [branch] at next_eq
        cases payload_eq
        exact next_eq.symm
      exact ⟨⟨source, source_eq, original, original_eq ▸ cached⟩, rfl, rfl⟩
  | .progressed next _ =>
      have isCombined : ∃ nextSearch : Cached.CachedSearch tau
          (Matrix.Integral.Word.matrixProduct (matrix :: remaining)),
          original = .combined ⟨payload.1, payload.2.1, nextSearch⟩ := by
        rw [branch] at next_eq
        exact ⟨{ transition.1.val with search := next }, next_eq⟩
      let actual := extractCombinedParts payload.1 payload.2.1 original isCombined
      have payload_eq := combinedPayload_eq action tail search payload same
      let head_eq := congrArg Sigma.fst payload_eq
      let tailAtHead := Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
        actual.1 head_eq
      let nextTail := Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
        tailAtHead action.1.property.symm
      have nextTail_eq : nextTail = tail := by
        have atHead := congrArg
          (fun value => Eq.ndrec (motive := fun h => FoldPreparations (Step.tailInput tau matrix h) remaining)
            value head_eq) actual.2.property.2
        have atOutput := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value action.1.property.symm) atHead
        have pair_eq := sigmaFirstTransport
          (first := fun h : Step.HeadPreparation tau matrix => FoldPreparations (Step.tailInput tau matrix h) remaining)
          (second := fun _ => Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
          payload.2 head_eq
        have restore := congrArg
          (fun value => Eq.ndrec (motive := fun channel => FoldPreparations channel remaining)
            value action.1.property.symm) pair_eq.symm
        exact atOutput.trans (restore.trans tail_eq)
      have finishedNext : SuffixCompletion action child nextTail :=
        finished.trans (congrArg some nextTail_eq.symm)
      have original_eq : actionCombined action nextTail actual.2.val = original := by
        rw [nextTail_eq]
        let nextSearch := actual.2.val
        have combined_eq : original = .combined ⟨payload.1, payload.2.1, nextSearch⟩ :=
          actual.2.property.1.trans (congrArg
            (fun value : FoldPreparations (Step.tailInput tau matrix payload.1) remaining =>
              (.combined ⟨payload.1, value, nextSearch⟩ : State.Cursor tau (matrix :: remaining)))
            actual.2.property.2)
        cases payload_eq
        exact combined_eq.symm
      let cached : Cache source (matrix :: remaining)
          (actionCombined action nextTail actual.2.val) :=
        .combinedPrepared rows action action_eq childSource childSource_eq child nested
          nextTail finishedNext actual.2.val
      exact ⟨⟨source, source_eq, original, original_eq ▸ cached⟩, rfl, rfl⟩

/-- Continue a retained supplied-preparation suffix using its exact observed combined transition.

Both progressed and prepared results retain the original child cache and use
the actual returned cursor and its tail or search without another inspection. -/
@[noinline, nospecialize] def advanceCombinedPreparation {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (source : Provenance.Algebraic.Sidecar tau) (source_eq : source = input)
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows source matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : childSource = actionEvidence action)
    (child : State.Cursor (actionOutput action) remaining)
    (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput action) remaining)
    (finished : SuffixCompletion action child tail)
    (search : Cached.CachedSearch tau (Matrix.Integral.Word.matrixProduct (matrix :: remaining)))
    (payload : CombinedPayload tau matrix remaining)
    (same : State.CursorPayload.combined payload = actionCombined action tail search)
    (transition : Step.CombinedTransition tau matrix remaining payload.1 payload.2.1 payload.2.2) :
    { result : Cursor input (matrix :: remaining) //
      result.source = source ∧ result.original = transition.2.2.val } :=
  consumeReadyPreparationWith source source_eq rows action action_eq childSource childSource_eq child nested
    tail finished search payload same transition transition.2.2.val transition.2.2.property

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution

end
