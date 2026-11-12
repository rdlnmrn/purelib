module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Execution.Snapshot

/-!
# Entering a selected original fold head

At an original head cursor no suffix cache can already be attached. A single
preflight retains that same cursor and its rows before returning the actual
prepared or progressed branch.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- A cache at an original head search has no attached suffix. -/
private theorem cachePendingAtHead {tau : CoherentNamed} {source : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (search : Step.LeafState matrix tau)
    (cached : Cache source (matrix :: remaining) (.head search)) : cached = .pending := by
  cases cached
  rfl

/-- An original head cursor retains no attached suffix cache. -/
theorem Cursor.pendingAtHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (cursor : Cursor input (matrix :: remaining))
    (search : Step.LeafState matrix tau) (atHead : cursor.original = .head search) :
    cursor.cache = .pending := by
  cases cursor with
  | mk source source_eq original cache =>
      cases atHead
      exact cachePendingAtHead search cache

/-- Read the actual head search of the original cursor when it is at a head. -/
@[expose, noinline, nospecialize] def Cursor.headSearch? {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Option (Step.LeafState matrix tau) :=
  match cursor.original with
  | .head search => some search
  | _ => none

/-- Retain the actual original head search and its identity with a supplied specification. -/
@[expose, noinline, nospecialize] def Cursor.actualHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (search : Step.LeafState matrix tau)
    (atHead : cursor.original = .head search) : { actual : Step.LeafState matrix tau // actual = search } := by
  have expected : cursor.headSearch? = some search := by
    unfold Cursor.headSearch?
    rewrite [atHead]
    rfl
  match found : cursor.headSearch? with
  | some actual => exact ⟨actual, Option.some.inj (found.symm.trans expected)⟩
  | none => cases found.symm.trans expected

/-- A returned head search is the original cursor's actual head. -/
theorem Cursor.headSearch_sound {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix} (cursor : Cursor input (matrix :: remaining))
    (search : Step.LeafState matrix tau) (found : cursor.headSearch? = some search) :
    cursor.original = .head search := by
  have sound (original : State.Cursor tau (matrix :: remaining))
      (found : (match original with | .head state => some state | _ => none) = some search) :
      original = .head search := by
    cases original with
    | head state =>
        have same : state = search := Option.some.inj found
        cases same
        rfl
    | tail _ => cases found
    | combined _ => cases found
    | ready _ => cases found
  exact sound cursor.original found


namespace Execution

/-- The retained original preflight and work at its exact selected branch. -/
@[expose] def PreflightEntry {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : PendingHead input matrix remaining} (observed : PendingObservation request) : Type 1 :=
  Σ advanced : { value : (Σ retained : { value : PendingObservation request // value = observed },
    Run.Preflight.Outcome retained.val) // value = observed.advance },
    Work.PreflightWork advanced.val.1.val advanced.val.2

/-- The original head request, its actual preflight and the selected retained work. -/
@[expose] def HeadEntry {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (search : Step.LeafState matrix tau)
    (atHead : cursor.original = .head search) : Type 1 :=
  Σ request : { value : Run.HeadRequest input matrix remaining //
    value = Run.HeadRequest.create cursor search atHead (cursor.pendingAtHead search atHead) },
    Σ observed : { value : Run.Preflight request.val // value = request.val.preflight },
      PreflightEntry observed.val

/-- Perform one numerical preflight at the exact original selected head.

The result retains the original cursor, its rows, the one preflight and its
selected work. A progressed result postpones the algebraic decision to a later
work unit; a ready result uses the original numerical preparation. -/
@[expose, noinline, nospecialize] def startHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (search : Step.LeafState matrix tau)
    (atHead : cursor.original = .head search) : HeadEntry cursor search atHead := by
  let actual := cursor.actualHead search atHead
  have actualAtHead : cursor.original = .head actual.val := by
    exact atHead.trans (congrArg (fun state => (.head state : State.Cursor tau (matrix :: remaining)))
      actual.property.symm)
  have requestSame {first second : Step.LeafState matrix tau} (same : first = second)
      (firstAt : cursor.original = .head first) (secondAt : cursor.original = .head second) :
      Run.HeadRequest.create cursor first firstAt (cursor.pendingAtHead first firstAt) =
        Run.HeadRequest.create cursor second secondAt (cursor.pendingAtHead second secondAt) := by
    cases same
    rfl
  let request := Run.HeadRequest.create cursor actual.val actualAtHead (cursor.pendingAtHead actual.val actualAtHead)
  let observed := request.preflight
  exact ⟨⟨request, requestSame actual.property actualAtHead atHead⟩,
    ⟨⟨observed, rfl⟩, Work.fromPreflight observed⟩⟩

/-- The selected head entry or an exact report that the original cursor is not at a head. -/
@[expose] def HeadSelection {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Type 1 :=
  (Σ selected : { search : Step.LeafState matrix tau // cursor.original = .head search },
    HeadEntry cursor selected.val selected.property) ⊕ PLift (cursor.headSearch? = none)

/-- Inspect the original cursor and perform one preflight only if it is at a head. -/
@[expose, noinline, nospecialize] def chooseHead {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) :
    Σ retained : { value : Cursor input (matrix :: remaining) // value = cursor }, HeadSelection retained.val := by
  match found : cursor.headSearch? with
  | some search =>
      have atHead := cursor.headSearch_sound search found
      let entry := startHead cursor search atHead
      exact ⟨⟨cursor, rfl⟩, .inl ⟨⟨search, atHead⟩, entry⟩⟩
  | none => exact ⟨⟨cursor, rfl⟩, .inr ⟨found⟩⟩


end Execution

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

end
