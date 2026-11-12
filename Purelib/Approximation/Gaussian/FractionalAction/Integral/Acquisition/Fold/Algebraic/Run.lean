module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite acquisition at an algebraic fractional-fold head

The numerical preflight and the algebraic decision are separate work units.
Both retain the original cursor and the same row cache, and a zero result is
the actual decision of those rows at the original denominator.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Run

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

/-- The original cursor is at the supplied numerical head. -/
@[expose] def HeadAt {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (search : Step.LeafState matrix tau) : Prop :=
  cursor.original = .head search

/-- The original head has no attached algebraic cache. -/
@[expose] def HeadPending {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Prop := cursor.cache = .pending

/-- Rows at the original source and requested head matrix. -/
@[expose] def HeadRows {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) : Type 1 :=
  Integral.Algebraic.Rows cursor.source matrix

section

attribute [local irreducible] Step.LeafState HeadAt HeadPending HeadRows

set_option genInjectivity false in
/-- One selected original head and its original algebraic rows.

The original cursor must be at the supplied head search and have no attached
head or suffix cache. The rows are indexed by its exact retained source. -/
structure HeadRequest {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrix : IntegralMatrix) (remaining : List IntegralMatrix) where
  /-- The complete original fold cursor and its retained source. -/
  cursor : Cursor input (matrix :: remaining)
  /-- The actual numerical head search. -/
  search : Step.LeafState matrix tau
  /-- The original cursor is at this same head search. -/
  atHead : HeadAt cursor search
  /-- No previous algebraic head or suffix evidence is attached to this cursor. -/
  pending : HeadPending cursor
  /-- The actual cached rows of the retained source and requested matrix. -/
  rows : HeadRows cursor

constructive_injectivity HeadRequest

end

/-- Attach the original row constructions to a selected uncached head. -/
@[expose] def HeadRequest.create {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (cursor : Cursor input (matrix :: remaining)) (search : Acquisition.State matrix tau)
    (atHead : cursor.original = .head search) (pending : cursor.cache = .pending) :
    HeadRequest input matrix remaining :=
  ⟨cursor, search, atHead, pending, Integral.Algebraic.readRows cursor.source matrix⟩

/-- Continue a head search at a supplied state while keeping the same original source and row cache. -/
@[expose] def HeadRequest.resume {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) (next : Acquisition.State matrix tau) :
    HeadRequest input matrix remaining :=
  ⟨⟨request.cursor.source, request.cursor.source_eq, .head next, .pending⟩,
    next, rfl, rfl, request.rows⟩

/-- Resumption keeps the same cached rows. -/
theorem HeadRequest.resume_rows {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) (next : Acquisition.State matrix tau) :
    (request.resume next).rows = request.rows := rfl

/-- The original preflight result and its complete retained head request.

The result is exactly the original finite inspection, including its prepared
denominator or its next state and progress witness. -/
@[expose] def Preflight {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) : Type 1 :=
  Σ retained : { value : HeadRequest input matrix remaining // value = request },
    { result : Acquisition.Step.StepResult matrix tau retained.val.search //
      result = Acquisition.Step.step matrix tau retained.val.search }

/-- The actual algebraic row decision and its complete retained head request.

The original result retains either its successful head or its exact zero
obstruction, and is tied to the decision of the same cached rows. -/
@[expose] def Decision {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) : Type 1 :=
  Σ retained : { value : HeadRequest input matrix remaining // value = request },
    { result : Except (Integral.Algebraic.Obstruction retained.val.rows)
        (Σ preparation : HeadPreparation tau matrix, RetainedHead retained.val.rows preparation) //
      result = retained.val.rows.step }

/-- Inspect the selected numerical head once, retaining its actual result and rows. -/
@[expose, noinline, nospecialize] def HeadRequest.preflight {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) : Preflight request :=
  ⟨⟨request, rfl⟩, ⟨Acquisition.Step.step matrix tau request.search, rfl⟩⟩

/-- Decide the same cached head rows in a separate finite work unit. -/
@[expose, noinline, nospecialize] def HeadRequest.decide {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) : Decision request :=
  ⟨⟨request, rfl⟩, ⟨request.rows.step, rfl⟩⟩

/-- Start a suffix from these rows at a supplied original preparation. -/
@[expose] def HeadRequest.preparedCursor {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) (preparation : HeadPreparation tau matrix) :
    Cursor input (matrix :: remaining) :=
  request.cursor.source_eq ▸ Cursor.ofPreparation request.cursor.source request.rows preparation remaining

/-- Start a suffix from the actual successful head of these rows. -/
@[expose] def HeadRequest.decidedCursor {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    (request : HeadRequest input matrix remaining) {preparation : HeadPreparation tau matrix}
    (head : RetainedHead request.rows preparation) : Cursor input (matrix :: remaining) :=
  request.cursor.source_eq ▸ Cursor.ofHead request.cursor.source head remaining

/-- The selected branch and actual next owner of one retained numerical preflight. -/
@[expose] def Preflight.Outcome {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : HeadRequest input matrix remaining} (observed : Preflight request) : Type 1 :=
  (Σ preparation : HeadPreparation tau matrix,
    { next : Cursor input (matrix :: remaining) // observed.2.val = .ready preparation ∧
      next = observed.1.val.preparedCursor preparation }) ⊕
  (Σ next : Acquisition.State matrix tau,
    Σ progress : Refinement.State.Progress observed.1.val.search next,
      { resumed : HeadRequest input matrix remaining // observed.2.val = .progressed next progress ∧
        resumed = observed.1.val.resume next })

/-- The selected branch and actual next owner of one retained algebraic decision. -/
@[expose] def Decision.Outcome {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : HeadRequest input matrix remaining} (observed : Decision request) : Type 1 :=
  (Σ preparation : HeadPreparation tau matrix,
    Σ head : RetainedHead observed.1.val.rows preparation,
      { next : Cursor input (matrix :: remaining) // observed.2.val = .ok ⟨preparation, head⟩ ∧
        next = observed.1.val.decidedCursor head }) ⊕
  { obstruction : Integral.Algebraic.Obstruction observed.1.val.rows // observed.2.val = .error obstruction }

/-- Retain the preflight and continue using the payload of its actual selected branch.

Ready starts the original suffix at the same preparation; progress resumes the
same original head search and cached rows. Neither branch repeats the inspection. -/
@[expose, noinline, nospecialize] def Preflight.advance {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : HeadRequest input matrix remaining} (observed : Preflight request) :
    Σ retained : { value : Preflight request // value = observed }, Outcome retained.val := by
  match selected : observed.2.val with
  | .ready preparation =>
      let next := observed.1.val.preparedCursor preparation
      exact ⟨⟨observed, rfl⟩, .inl ⟨preparation, ⟨next, selected, rfl⟩⟩⟩
  | .progressed next progress =>
      let resumed := observed.1.val.resume next
      exact ⟨⟨observed, rfl⟩, .inr ⟨next, progress, ⟨resumed, selected, rfl⟩⟩⟩

/-- Retain the row decision and continue using its actual successful head or zero obstruction.

The successful branch starts the original suffix from the retained action.
The zero branch returns the same original row obstruction without another decision. -/
@[expose, noinline, nospecialize] def Decision.advance {tau : CoherentNamed}
    {input : Provenance.Algebraic.Sidecar tau} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {request : HeadRequest input matrix remaining} (observed : Decision request) :
    Σ retained : { value : Decision request // value = observed }, Outcome retained.val := by
  match selected : observed.2.val with
  | .error obstruction => exact ⟨⟨observed, rfl⟩, .inr ⟨obstruction, selected⟩⟩
  | .ok ⟨preparation, head⟩ =>
      let next := observed.1.val.decidedCursor head
      exact ⟨⟨observed, rfl⟩, .inl ⟨preparation, head, ⟨next, selected, rfl⟩⟩⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic.Run

end
