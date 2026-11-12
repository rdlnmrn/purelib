module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Algebraic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Algebraic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
import Purelib.LinearAlgebra.Matrix.Integral.Word
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained algebraic evidence for fractional-fold cursors

The original fold cursor remains the owner of its acquisition state. A cache
may retain either an actual successful head or an action at a supplied
preparation, together with a cache on its exact suffix. A pending cache makes
no assertion about work not yet attached.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

open Purelib.Approximation.Gaussian.FractionalAction
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)

/-- A preparation at the original denominator of one requested fractional action. -/
@[expose] def HeadPreparation (tau : CoherentNamed) (matrix : IntegralMatrix) : Type 1 :=
  Prepared.DenominatorPreparation (fractionalDenominator matrix tau)

/-- The exact retained successful head for the original rows and preparation. -/
@[expose] def RetainedHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} (rows : Integral.Algebraic.Rows input matrix)
    (preparation : HeadPreparation tau matrix) : Type 1 :=
  Integral.Algebraic.Head rows preparation

/-- An original fractional action at a supplied denominator preparation. -/
@[expose] def PreparedAction {tau : CoherentNamed} {matrix : IntegralMatrix}
    (preparation : HeadPreparation tau matrix) : Type 1 :=
  Integral.Algebraic.Action tau matrix preparation

/-- The original action retained by a successful head. -/
@[expose] def headAction {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {rows : Integral.Algebraic.Rows input matrix}
    {preparation : HeadPreparation tau matrix} (head : RetainedHead rows preparation) :
    PreparedAction preparation := head.action

/-- Compute the action using the retained rows and the supplied preparation. -/
@[expose] def rowAction {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} (rows : Integral.Algebraic.Rows input matrix)
    (preparation : HeadPreparation tau matrix) : PreparedAction preparation := rows.output preparation

/-- The cached action is the actual output of the retained rows at the supplied preparation. -/
@[expose] def RowActionIdentity {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} (rows : Integral.Algebraic.Rows input matrix)
    (preparation : HeadPreparation tau matrix) (action : PreparedAction preparation) : Prop :=
  action = rowAction rows preparation

/-- The exact output channel of a retained prepared action. -/
@[expose] def actionOutput {tau : CoherentNamed} {matrix : IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (action : PreparedAction preparation) : CoherentNamed :=
  action.1.val

/-- The original algebraic evidence at the exact retained action output. -/
@[expose] def actionEvidence {tau : CoherentNamed} {matrix : IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (action : PreparedAction preparation) :
    Provenance.Algebraic.Sidecar (actionOutput action) := action.2

/-- An actual child source is the evidence retained by the original action. -/
@[expose] def ChildSourceIdentity {tau : CoherentNamed} {matrix : IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (action : PreparedAction preparation)
    (source : Provenance.Algebraic.Sidecar (actionOutput action)) : Prop := source = actionEvidence action

/-- Retain a suffix cursor under a supplied preparation and its exact action output. -/
@[expose] def actionTail {tau : CoherentNamed} {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (action : PreparedAction preparation)
    (child : State.Cursor (actionOutput action) remaining) : State.Cursor tau (matrix :: remaining) :=
  .tail ⟨preparation, action.1.property ▸ child⟩

/-- Completion of the exact suffix cursor at the retained action output. -/
@[expose] def SuffixCompletion {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (child : State.Cursor (actionOutput action) remaining)
    (tail : FoldPreparations (actionOutput action) remaining) : Prop :=
  State.finished? (actionOutput action) remaining child = some tail

/-- The original combined search reached after the retained action and completed suffix. -/
@[expose] def actionCombined {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (tail : FoldPreparations (actionOutput action) remaining)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
    State.Cursor tau (matrix :: remaining) :=
  .combined ⟨preparation, action.1.property ▸ tail, search⟩

/-- A completed original fold at the retained action and supplied combined preparation. -/
@[expose] def actionReady {tau : CoherentNamed} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} {preparation : HeadPreparation tau matrix}
    (action : PreparedAction preparation) (tail : FoldPreparations (actionOutput action) remaining)
    (combined : HeadPreparation tau (Word.matrixProduct (matrix :: remaining))) :
    State.Cursor tau (matrix :: remaining) :=
  .ready ⟨preparation, action.1.property ▸ tail, combined⟩

/-- A preparation at the actual matrix retained by a combined search. -/
@[expose] def SearchPreparation {tau : CoherentNamed} {matrix : IntegralMatrix}
    (search : Cached.CachedSearch tau matrix) : Type 1 := HeadPreparation tau search.matrix

/-- Transport a search preparation to its original specified matrix. -/
@[expose] def searchPreparation {tau : CoherentNamed} {matrix : IntegralMatrix}
    (search : Cached.CachedSearch tau matrix) (preparation : SearchPreparation search) :
    HeadPreparation tau matrix := Cached.cachedPreparation search preparation

/-- Retain an original suffix cursor under its exact successful head preparation. -/
@[expose] def originalTail {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : HeadPreparation tau matrix}
    {rows : Integral.Algebraic.Rows input matrix} (head : RetainedHead rows preparation)
    (child : State.Cursor (actionOutput (headAction head)) remaining) : State.Cursor tau (matrix :: remaining) :=
  actionTail (headAction head) child

section

attribute [local irreducible] HeadPreparation RetainedHead headAction PreparedAction rowAction
  RowActionIdentity actionOutput actionEvidence ChildSourceIdentity actionTail SuffixCompletion
  actionCombined actionReady
  SearchPreparation searchPreparation State.Cursor originalTail FoldPreparations Cached.CachedSearch

set_option genInjectivity false in
/-- Optional retained algebraic head and suffix evidence for one original fold cursor.

`pending` retains no algebraic history and makes no claim about the original
cursor's readiness. `tail` retains an actual successful head. `preparedTail`
retains the original rows and their action at a supplied preparation without
claiming that a denominator decision produced it. Both retain child caches at
the original suffix cursor and exact action output. Combined and ready stages
retain the same child, its completion, and the original combined search. -/
inductive Cache : {tau : CoherentNamed} → (input : Provenance.Algebraic.Sidecar tau) →
    (matrices : List IntegralMatrix) → State.Cursor tau matrices → Type 1 where
  /-- No algebraic head or suffix evidence has yet been attached to this exact cursor. -/
  | pending {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrices : List IntegralMatrix} {original : State.Cursor tau matrices} : Cache input matrices original
  /-- Retain the original successful head and the cache of its same original suffix. -/
  | tail {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix}
      {rows : Integral.Algebraic.Rows input matrix} (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : ChildSourceIdentity (headAction head) childSource)
      {child : State.Cursor (actionOutput (headAction head)) remaining}
      (nested : Cache childSource remaining child) :
      Cache input (matrix :: remaining) (originalTail head child)
  /-- Retain rows and an action using a supplied preparation, without claiming a computed decision. -/
  | preparedTail {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows input matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : ChildSourceIdentity action childSource)
      {child : State.Cursor (actionOutput action) remaining}
      (nested : Cache childSource remaining child) :
      Cache input (matrix :: remaining) (actionTail action child)
  /-- Retain a computed head and the exact completed suffix during combined acquisition. -/
  | combinedHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows input matrix}
      (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : ChildSourceIdentity (headAction head) childSource)
      (child : State.Cursor (actionOutput (headAction head)) remaining)
      (nested : Cache childSource remaining child)
      (tail : FoldPreparations (actionOutput (headAction head)) remaining)
      (finished : SuffixCompletion (headAction head) child tail)
      (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
      Cache input (matrix :: remaining) (actionCombined (headAction head) tail search)
  /-- Retain a supplied-preparation action and its completed suffix during combined acquisition. -/
  | combinedPrepared {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows input matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : ChildSourceIdentity action childSource)
      (child : State.Cursor (actionOutput action) remaining)
      (nested : Cache childSource remaining child)
      (tail : FoldPreparations (actionOutput action) remaining)
      (finished : SuffixCompletion action child tail)
      (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
      Cache input (matrix :: remaining) (actionCombined action tail search)
  /-- Retain a computed head, completed suffix and combined search after a supplied combined preparation. -/
  | readyHead {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix} {rows : Integral.Algebraic.Rows input matrix}
      (head : RetainedHead rows preparation)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
      (childSource_eq : ChildSourceIdentity (headAction head) childSource)
      (child : State.Cursor (actionOutput (headAction head)) remaining)
      (nested : Cache childSource remaining child)
      (tail : FoldPreparations (actionOutput (headAction head)) remaining)
      (finished : SuffixCompletion (headAction head) child tail)
      (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
      (combined : SearchPreparation search) :
      Cache input (matrix :: remaining)
        (actionReady (headAction head) tail (searchPreparation search combined))
  /-- Retain a supplied-preparation action, completed suffix and combined search after preparation. -/
  | readyPrepared {tau : CoherentNamed} {input : Provenance.Algebraic.Sidecar tau}
      {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
      {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows input matrix)
      (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
      (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
      (childSource_eq : ChildSourceIdentity action childSource)
      (child : State.Cursor (actionOutput action) remaining)
      (nested : Cache childSource remaining child)
      (tail : FoldPreparations (actionOutput action) remaining)
      (finished : SuffixCompletion action child tail)
      (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
      (combined : SearchPreparation search) :
      Cache input (matrix :: remaining)
        (actionReady action tail (searchPreparation search combined))

constructive_injectivity Cache

end

set_option genInjectivity false in
/-- An original input, its original fold cursor and the evidence retained for that exact cursor. -/
structure Cursor {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrices : List IntegralMatrix) where
  /-- The complete original algebraic input, retained for later acquisition. -/
  source : Provenance.Algebraic.Sidecar tau
  /-- The retained source is the original input. -/
  source_eq : source = input
  /-- The exact original generic fold cursor. -/
  original : State.Cursor tau matrices
  /-- The retained head and suffix evidence belongs to this same original cursor and source. -/
  cache : Cache source matrices original

constructive_injectivity Cursor

/-- Retain an original fold cursor before attaching algebraic head evidence. -/
@[expose] def Cursor.pending {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrices : List IntegralMatrix) (original : State.Cursor tau matrices) : Cursor input matrices :=
  ⟨input, rfl, original, .pending⟩

/-- Start the original fold cursor with its complete original algebraic input. -/
@[expose] def Cursor.initial {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    (matrices : List IntegralMatrix) : Cursor input matrices :=
  Cursor.pending input matrices (State.initial tau matrices)

/-- Retain a successful original head and start its original suffix cursor at the cached output.

The same head retains the original row cache, computed denominator decision,
prepared action and output sidecar. Its child cache starts pending at the
suffix cursor constructed from that exact retained output. -/
@[expose] def Cursor.ofHead {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {rows : Integral.Algebraic.Rows input matrix}
    {preparation : Prepared.DenominatorPreparation (fractionalDenominator matrix tau)}
    (head : Integral.Algebraic.Head rows preparation) (remaining : List IntegralMatrix) :
    Cursor input (matrix :: remaining) := by
  let action := head.action
  let childSource := action.2
  let child := State.initial action.1.val remaining
  let original := originalTail head child
  have cached : Cache input (matrix :: remaining) original :=
    .tail (child := child) head childSource rfl .pending
  exact ⟨input, rfl, original, cached⟩

/-- Retain rows and their action at a supplied preparation, starting its actual suffix cursor.

The supplied preparation need not be the result of the rows' decision. The
suffix starts pending at the exact retained output and its original cursor. -/
@[expose] def Cursor.ofPreparation {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} (rows : Integral.Algebraic.Rows input matrix)
    (preparation : HeadPreparation tau matrix) (remaining : List IntegralMatrix) :
    Cursor input (matrix :: remaining) := by
  let action := rowAction rows preparation
  let childSource := action.2
  let child := State.initial action.1.val remaining
  let original := actionTail action child
  have cached : Cache input (matrix :: remaining) original :=
    .preparedTail rows action rfl childSource rfl (child := child) .pending
  exact ⟨input, rfl, original, cached⟩

/-- Retain a computed head and its completed original suffix during combined acquisition. -/
@[expose] def Cursor.ofCombinedHead {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {rows : Integral.Algebraic.Rows input matrix} {preparation : HeadPreparation tau matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : ChildSourceIdentity (headAction head) childSource)
    (child : State.Cursor (actionOutput (headAction head)) remaining) (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput (headAction head)) remaining)
    (finished : SuffixCompletion (headAction head) child tail)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
    Cursor input (matrix :: remaining) :=
  ⟨input, rfl, actionCombined (headAction head) tail search,
    .combinedHead head childSource childSource_eq child nested tail finished search⟩

/-- Retain an action at a supplied head preparation and its completed suffix during combined acquisition. -/
@[expose] def Cursor.ofCombinedPreparation {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows input matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : ChildSourceIdentity action childSource)
    (child : State.Cursor (actionOutput action) remaining) (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput action) remaining) (finished : SuffixCompletion action child tail)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining))) :
    Cursor input (matrix :: remaining) :=
  ⟨input, rfl, actionCombined action tail search,
    .combinedPrepared rows action action_eq childSource childSource_eq child nested tail finished search⟩

/-- Retain a computed head and completed suffix with a supplied combined preparation. -/
@[expose] def Cursor.ofReadyHead {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {rows : Integral.Algebraic.Rows input matrix} {preparation : HeadPreparation tau matrix}
    (head : RetainedHead rows preparation)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput (headAction head)))
    (childSource_eq : ChildSourceIdentity (headAction head) childSource)
    (child : State.Cursor (actionOutput (headAction head)) remaining) (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput (headAction head)) remaining)
    (finished : SuffixCompletion (headAction head) child tail)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
    (combined : SearchPreparation search) : Cursor input (matrix :: remaining) :=
  ⟨input, rfl, actionReady (headAction head) tail (searchPreparation search combined),
    .readyHead head childSource childSource_eq child nested tail finished search combined⟩

/-- Retain a supplied-preparation action and completed suffix with a supplied combined preparation. -/
@[expose] def Cursor.ofReadyPreparation {tau : CoherentNamed} (input : Provenance.Algebraic.Sidecar tau)
    {matrix : IntegralMatrix} {remaining : List IntegralMatrix}
    {preparation : HeadPreparation tau matrix} (rows : Integral.Algebraic.Rows input matrix)
    (action : PreparedAction preparation) (action_eq : RowActionIdentity rows preparation action)
    (childSource : Provenance.Algebraic.Sidecar (actionOutput action))
    (childSource_eq : ChildSourceIdentity action childSource)
    (child : State.Cursor (actionOutput action) remaining) (nested : Cache childSource remaining child)
    (tail : FoldPreparations (actionOutput action) remaining) (finished : SuffixCompletion action child tail)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
    (combined : SearchPreparation search) : Cursor input (matrix :: remaining) :=
  ⟨input, rfl, actionReady action tail (searchPreparation search combined),
    .readyPrepared rows action action_eq childSource childSource_eq child nested tail finished search combined⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Algebraic

end
