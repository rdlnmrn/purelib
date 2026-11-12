module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Control.FiniteRunner.Progress
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.LinearAlgebra.Matrix.Multiplication

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

section
@[expose] public section

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator fractionalLinear)
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- A preparation at one actual head denominator. -/
def HeadPreparation (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) : Type 1 :=
  Prepared.DenominatorPreparation (fractionalDenominator matrix tau)

/-- The actual input channel of the suffix at one head preparation. -/
def tailInput (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix)
    (head : HeadPreparation tau matrix) : Coherent.CoherentNamed := fractionalLinear matrix tau head

/-- The exact search state at one requested denominator. -/
def LeafState (matrix : IntegralMatrix) (tau : Coherent.CoherentNamed) : Type :=
  Acquisition.State matrix tau

/-- A completed identity-denominator cursor. -/
def emptyReadyCursor (tau : Coherent.CoherentNamed) (preparation : FoldPreparations tau []) :
    State.Cursor tau [] := .inr preparation

/-- An identity-denominator search cursor. -/
def identityCursor (tau : Coherent.CoherentNamed) (state : LeafState Multiplication.identity tau) :
    State.Cursor tau [] := .inl state

/-- A completed nonempty fold cursor. -/
def readyCursor (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (preparations : FoldPreparations tau (matrix :: remaining)) : State.Cursor tau (matrix :: remaining) :=
  .ready preparations

/-- A current head-denominator search cursor. -/
def headCursor (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (state : LeafState matrix tau) : State.Cursor tau (matrix :: remaining) := .head state

/-- The original suffix cursor under its retained head preparation. -/
def tailCursor (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (child : State.Cursor (tailInput tau matrix head) remaining) :
    State.Cursor tau (matrix :: remaining) := .tail ⟨head, child⟩

/-- The original combined-denominator cursor with its retained head and suffix. -/
def combinedCursor (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (tail : FoldPreparations (tailInput tau matrix head) remaining)
    (state : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
    State.Cursor tau (matrix :: remaining) := .combined ⟨head, tail, state⟩

/-- The retained suffix cursor has completed with the given preparation. -/
def TailFinished (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (child : State.Cursor (tailInput tau matrix head) remaining)
    (tail : FoldPreparations (tailInput tau matrix head) remaining) : Prop :=
  State.finished? (tailInput tau matrix head) remaining child = some tail

/-- The retained suffix cursor has not yet completed. -/
def TailUnfinished (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (child : State.Cursor (tailInput tau matrix head) remaining) : Prop :=
  State.finished? (tailInput tau matrix head) remaining child = none

section

attribute [local irreducible] HeadPreparation tailInput emptyReadyCursor identityCursor readyCursor
  headCursor tailCursor combinedCursor TailFinished TailUnfinished State.Cursor FoldPreparations LeafState

set_option genInjectivity false in
/-- The branch selected by one fold tick, indexed by its complete original cursor.

An unfinished suffix retains its head, exact child and selected child branch.
A completed suffix is a structural transition and performs no denominator
inspection during the same tick. -/
inductive View : (tau : Coherent.CoherentNamed) → (matrices : List IntegralMatrix) →
    State.Cursor tau matrices → Type 1 where
  /-- The completed empty fold remains unchanged. -/
  | emptyReady {tau} (preparation : FoldPreparations tau []) : View tau [] (emptyReadyCursor tau preparation)
  /-- Inspect the identity denominator of the empty fold. -/
  | identity {tau} (state : LeafState Multiplication.identity tau) : View tau [] (identityCursor tau state)
  /-- A completed nonempty fold remains unchanged. -/
  | ready {tau matrix remaining} (preparations : FoldPreparations tau (matrix :: remaining)) :
      View tau (matrix :: remaining) (readyCursor tau matrix remaining preparations)
  /-- Inspect the current original head denominator. -/
  | head {tau matrix remaining} (state : LeafState matrix tau) :
      View tau (matrix :: remaining) (headCursor tau matrix remaining state)
  /-- Move the completed suffix to combined acquisition without inspecting it. -/
  | tailFinished {tau matrix remaining} (head : HeadPreparation tau matrix)
      (child : State.Cursor (tailInput tau matrix head) remaining)
      (tail : FoldPreparations (tailInput tau matrix head) remaining)
      (finished : TailFinished tau matrix remaining head child tail) :
      View tau (matrix :: remaining) (tailCursor tau matrix remaining head child)
  /-- Descend through the same retained head and actual suffix channel into an unfinished original suffix. -/
  | suffix {tau matrix remaining} (head : HeadPreparation tau matrix)
      (child : State.Cursor (tailInput tau matrix head) remaining)
      (unfinished : TailUnfinished tau matrix remaining head child)
      (next : { value : Coherent.CoherentNamed // value = tailInput tau matrix head })
      (selected : View next.val remaining (next.property.symm ▸ child)) :
      View tau (matrix :: remaining) (tailCursor tau matrix remaining head child)
  /-- Inspect the original cached combined-matrix denominator. -/
  | combined {tau matrix remaining} (head : HeadPreparation tau matrix)
      (tail : FoldPreparations (tailInput tau matrix head) remaining)
      (state : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
      View tau (matrix :: remaining) (combinedCursor tau matrix remaining head tail state)

constructive_injectivity View

end

/-- The actual suffix channel and selected child for one unfinished original tail. -/
def TailSelection (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (child : State.Cursor (tailInput tau matrix head) remaining) : Type 1 :=
  (next : { value : Coherent.CoherentNamed // value = tailInput tau matrix head }) ×
    View next.val remaining (next.property.symm ▸ child)

/-- Select one original tail branch, invoking the supplied child selection only when it is unfinished.

The continuation supplies the actual retained suffix channel and its selected
child. A finished suffix returns its stored preparations without constructing
or selecting another output channel.
-/
def selectTailWith (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (child : State.Cursor (tailInput tau matrix head) remaining)
    (descend : TailUnfinished tau matrix remaining head child → TailSelection tau matrix remaining head child) :
    View tau (matrix :: remaining) (tailCursor tau matrix remaining head child) :=
  match finished : State.finished? (fractionalLinear matrix tau head) remaining child with
  | some tail => .tailFinished head child tail finished
  | none =>
      let selected := descend finished
      .suffix head child finished selected.1 selected.2

/-- Select the exact branch of one original fold tick without inspecting a denominator. -/
def select (tau : Coherent.CoherentNamed) : (matrices : List IntegralMatrix) →
    (cursor : State.Cursor tau matrices) → View tau matrices cursor
  | [], .inr preparation => .emptyReady preparation
  | [], .inl state => .identity state
  | _ :: _, .ready preparations => .ready preparations
  | _ :: _, .head state => .head state
  | matrix :: remaining, .tail ⟨head, child⟩ =>
      selectTailWith tau matrix remaining head child (fun _ =>
        let next := fractionalLinear matrix tau head
        ⟨⟨next, rfl⟩, select next remaining child⟩)
  | _ :: _, .combined ⟨head, tail, state⟩ => .combined head tail state

/-- The next original fold cursor for a supplied combined-search observation. -/
def combinedNext (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (tail : FoldPreparations (tailInput tau matrix head) remaining)
    (state : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
    (result : Acquisition.Step.StepResult state.matrix tau state.search) : State.Cursor tau (matrix :: remaining) :=
  match result with
  | .ready preparation => .ready ⟨head, tail, Cached.cachedPreparation state preparation⟩
  | .progressed next _ => .combined ⟨head, tail, { state with search := next }⟩

/-- One combined-search observation and its resulting original cursor.

The search, its actual step result and the resulting cursor are retained with
their defining equalities, so consumers can inspect the same raw preparation
without repeating the denominator inspection. -/
def CombinedTransition (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix) (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (tail : FoldPreparations (tailInput tau matrix head) remaining)
    (state : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) : Type 1 :=
  Σ actual : { value : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)) // value = state },
    Σ result : { value : Acquisition.Step.StepResult actual.val.matrix tau actual.val.search //
      value = Acquisition.Step.step actual.val.matrix tau actual.val.search },
      { next : State.Cursor tau (matrix :: remaining) //
        next = combinedNext tau matrix remaining head tail actual.val result.val }

/-- Inspect the retained combined search once and retain its actual outcome and next cursor. -/
@[noinline] def inspectCombined (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix)
    (head : HeadPreparation tau matrix) (tail : FoldPreparations (tailInput tau matrix head) remaining)
    (state : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
    CombinedTransition tau matrix remaining head tail state :=
  let result := Acquisition.Step.step state.matrix tau state.search
  ⟨⟨state, rfl⟩, ⟨⟨result, rfl⟩, ⟨combinedNext tau matrix remaining head tail state result, rfl⟩⟩⟩

/-- Execute the selected original branch and return its complete next cursor.

The only recursive case follows the retained suffix, and the only denominator
inspections occur at the identity, head and combined leaves. -/
def execute {tau : Coherent.CoherentNamed} {matrices : List IntegralMatrix}
    {cursor : State.Cursor tau matrices} (view : View tau matrices cursor) : State.Cursor tau matrices :=
  match view with
  | .emptyReady preparation => .inr preparation
  | @View.identity tau state =>
      match Acquisition.Step.step Multiplication.identity tau state with
      | .ready preparation => .inr preparation
      | .progressed next _ => .inl next
  | .ready preparations => .ready preparations
  | @View.head tau matrix remaining state =>
      match Acquisition.Step.step matrix tau state with
      | .ready preparation => .tail ⟨preparation,
          State.initial (fractionalLinear matrix tau preparation) remaining⟩
      | .progressed next _ => .head next
  | @View.tailFinished tau matrix remaining head _ tail _ =>
      .combined ⟨head, tail, Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩
  | @View.suffix tau matrix remaining head _ _ next selected =>
      let same : next.val = fractionalLinear matrix tau head := next.property
      .tail ⟨head, same ▸ execute selected⟩
  | @View.combined tau matrix remaining head tail state =>
      (inspectCombined tau matrix remaining head tail state).2.2.val

/-- One bounded work unit, possibly descending into the retained suffix.

The selected branch performs at most one denominator inspection. A completed
suffix moves to combined acquisition without inspecting that denominator. -/
def step (tau : Coherent.CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : State.Cursor tau matrices) : State.Cursor tau matrices :=
  execute (select tau matrices cursor)
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step

end
