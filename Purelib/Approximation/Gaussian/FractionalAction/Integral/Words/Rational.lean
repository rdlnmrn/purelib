module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Rational
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Step
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison
import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Scaling
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Ordered exact rational domain inspection

Each successful node retains the original matrix request, both actual row
readings and its productive numerical output. A blocked node retains the
first zero denominator and the entire unexecuted suffix. The preceding
nodes are the actual prepared prefix; final-matrix simplification cannot
remove an undefined intermediate step.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Rational

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Division
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator fractionalLinear fractionalVector)
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral

set_option genInjectivity false in
/-- Complete ordered rational execution or a first zero denominator following the exact retained prepared prefix. -/
inductive Execution : {tau : CoherentNamed} → RationalSidecar tau → List IntegralMatrix → Type 1 where
  /-- The empty suffix retains the exact current input and needs no division. -/
  | complete {tau : CoherentNamed} {input : RationalSidecar tau}
      (source : RationalSidecar tau) (source_eq : source = input) : Execution input []
  /-- Retain the first actual zero denominator and the original unexecuted matrix suffix. -/
  | blocked {tau : CoherentNamed} {input : RationalSidecar tau} (matrix : IntegralMatrix)
      (remaining : List IntegralMatrix) (rows : Integral.Rational.Rows input matrix)
      (zero : rows.denominatorReading.value = 0) (identity : Zero.ZeroIdentity rows.denominator) :
      Execution input (matrix :: remaining)
  /-- Retain one productive original action and continue from its same cached rational output. -/
  | step {tau : CoherentNamed} {input : RationalSidecar tau} (matrix : IntegralMatrix)
      (remaining : List IntegralMatrix) (rows : Integral.Rational.Rows input matrix)
      (ready : Integral.Rational.Ready rows) (next : Execution ready.reading remaining) :
      Execution input (matrix :: remaining)

constructive_injectivity Execution

/-- Inspect each original ordered denominator once and retain complete execution or its first certified obstruction. -/
@[noinline, nospecialize] def inspect {tau : CoherentNamed} (input : RationalSidecar tau) :
    (matrices : List IntegralMatrix) → Execution input matrices
  | [] => .complete input rfl
  | matrix :: remaining =>
      let rows := Integral.Rational.readRows input matrix
      if zero : rows.denominatorReading.value = 0 then
        .blocked matrix remaining rows zero
          (Provenance.Rational.Arithmetic.rationalZero rows.denominatorReading zero)
      else
        let ready := rows.prepare zero
        .step matrix remaining rows ready (inspect ready.reading remaining)

/-- Read the first undefined original position, with absence precisely when the retained execution completed. -/
@[expose] def Execution.firstUndefined {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} : Execution input matrices → Option Nat
  | .complete _ _ => none
  | .blocked _ _ _ _ _ => some 0
  | .step _ _ _ _ next => next.firstUndefined.map Nat.succ

/-- Read the actual prepared original matrix prefix from the retained ordered execution. -/
@[expose] def Execution.prefix {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} : Execution input matrices → List IntegralMatrix
  | .complete _ _ => []
  | .blocked _ _ _ _ _ => []
  | .step matrix _ _ _ next => matrix :: next.prefix

/-- Read the actual remaining suffix starting at the first undefined step, or empty after complete execution. -/
@[expose] def Execution.remaining {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} : Execution input matrices → List IntegralMatrix
  | .complete _ _ => []
  | .blocked matrix remaining _ _ _ => matrix :: remaining
  | .step _ _ _ _ next => next.remaining

/-- The retained prepared prefix and stopped suffix reconstruct the exact original ordered request. -/
theorem Execution.request_eq {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) :
    execution.prefix ++ execution.remaining = matrices := by
  induction execution with
  | complete source source_eq => rfl
  | blocked matrix remaining rows zero identity => rfl
  | step matrix remaining rows ready next ih => exact congrArg (List.cons matrix) ih

/-- Read the same cached final channel or the actual current channel at the first obstruction. -/
@[expose] def Execution.output {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} : Execution input matrices → CoherentNamed
  | .complete _ _ => tau
  | .blocked _ _ _ _ _ => tau
  | .step _ _ _ _ next => next.output

/-- Read the retained rational evidence at the exact final or stopped numerical channel. -/
@[expose] def Execution.reading {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) : RationalSidecar execution.output :=
  match execution with
  | .complete source _ => source
  | .blocked _ _ rows _ _ => rows.source
  | .step _ _ _ _ next => next.reading

/-- Read the actual ordered denominator preparations for the complete retained successful prefix. -/
@[expose] def Execution.preparations {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) :
    Step.StepPreparations tau execution.prefix :=
  match execution with
  | .complete _ _ => ULift.up ()
  | .blocked _ _ _ _ _ => ULift.up ()
  | .step _ _ _ ready next =>
      ⟨ready.toPreparation, Step.transportPreparations ready.output_spec next.prefix next.preparations⟩

/-- The retained final or stopped channel is exactly execution of the same original prepared prefix. -/
theorem Execution.output_eq {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) :
    execution.output = Step.stepAction tau execution.prefix execution.preparations := by
  induction execution with
  | complete source source_eq => rfl
  | blocked matrix remaining rows zero identity => rfl
  | step matrix remaining rows ready next ih =>
      exact ih.trans (Step.stepAction_transport ready.output_spec next.prefix next.preparations).symm

/-- A stopped execution reports the length of its complete original prepared prefix as the first undefined position. -/
theorem Execution.firstUndefined_eq_prefix_length {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) (index : Nat)
    (stopped : execution.firstUndefined = some index) : execution.prefix.length = index := by
  induction execution generalizing index with
  | complete source source_eq => cases stopped
  | blocked matrix remaining rows zero identity => exact Option.some.inj stopped
  | step matrix remaining rows ready next ih =>
      cases selected : next.firstUndefined with
      | none =>
          change next.firstUndefined.map Nat.succ = some index at stopped
          rewrite [selected] at stopped
          cases stopped
      | some earlier =>
          have index_eq : earlier + 1 = index := by
            change (next.firstUndefined.map Nat.succ) = some index at stopped
            rewrite [selected] at stopped
            exact Option.some.inj stopped
          exact (congrArg Nat.succ (ih earlier selected)).trans index_eq

/-- A completed inspection prepares the exact full original ordered request. -/
theorem Execution.prefix_eq_of_complete {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) : execution.prefix = matrices := by
  induction execution with
  | complete source source_eq => rfl
  | blocked matrix remaining rows zero identity => cases completed
  | step matrix remaining rows ready next ih =>
      cases selected : next.firstUndefined with
      | none => exact congrArg (List.cons matrix) (ih selected)
      | some earlier =>
          change next.firstUndefined.map Nat.succ = none at completed
          rewrite [selected] at completed
          cases completed

/-- Read the exact full original preparation schedule when ordered inspection completes. -/
@[noinline, nospecialize] def Execution.fullPreparations {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) : Step.StepPreparations tau matrices :=
  Step.transportRequest (execution.prefix_eq_of_complete completed) execution.preparations

/-- Completed inspection returns the exact original ordered evaluator through the same retained preparations. -/
theorem Execution.output_eq_full {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) :
    execution.output = Step.stepAction tau matrices (execution.fullPreparations completed) :=
  execution.output_eq.trans
    (Step.stepAction_transport_request (execution.prefix_eq_of_complete completed) execution.preparations).symm

/-- Exact rational evidence for the original folded denominator, its nonzero condition and all suffix preparations. -/
@[expose] def FoldData (tau : CoherentNamed) (matrices : List IntegralMatrix) : Type 1 :=
  Sigma fun reading : RationalSidecar (fractionalDenominator (Word.matrixProduct matrices) tau) =>
    PProd (reading.value ≠ 0) (Fold.Basic.FoldPreparations tau matrices)

/-- Transport cached rational fold evidence through literal identity of its original input channel. -/
private def transportFoldData {first second : CoherentNamed} (equal : first = second)
    (matrices : List IntegralMatrix) (data : FoldData first matrices) : FoldData second matrices :=
  equal ▸ data

/-- Literal source transport retains the same rational coefficient. -/
private theorem transportedReading_value {first second : CoherentNamed} (equal : first = second)
    (reading : RationalSidecar first) : (equal ▸ reading : RationalSidecar second).value = reading.value := by
  cases equal
  rfl

/-- Construct full fold evidence for the actual successful prefix from the same retained rational row caches.

Each combined reading is the product of the cached first denominator and the
cached tail denominator, transported by homogeneous scaling. A blocked node
contributes only its empty successful prefix, preserving the undefined step.
-/
@[noinline, nospecialize] def Execution.foldData {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) : FoldData tau execution.prefix :=
  match execution with
  | .complete _ _ | .blocked _ _ _ _ _ =>
      let reading : RationalSidecar (fractionalDenominator (Word.matrixProduct []) tau) :=
        ⟨1, Action.matrixAction_identity
          (fractionalVector tau) 0⟩
      have nonzero : reading.value ≠ 0 := by
        change (1 : Basic.Canonical) ≠ 0
        decide +kernel
      let prepared := reading.prepare nonzero
      ⟨reading, nonzero, ⟨prepared.denominator, prepared.apart, prepared.equivalent⟩⟩
  | .step matrix _ rows ready next =>
      let tail := transportFoldData ready.output_spec next.prefix next.foldData
      let first : RationalSidecar (fractionalDenominator matrix tau) :=
        rows.denominator_eq ▸ rows.denominatorReading
      have firstNonzero : first.value ≠ 0 := by
        rewrite [transportedReading_value rows.denominator_eq rows.denominatorReading]
        exact ready.nonzero
      let product := first.mul tail.1
      let scaled := Integral.Composition.Scaling.fractionalRows_mul_scaled
        (Word.matrixProduct next.prefix) matrix tau ready.toPreparation 0
      let reading : RationalSidecar
          (fractionalDenominator (Word.matrixProduct (matrix :: next.prefix)) tau) :=
        ⟨product.value, NamedEquivalent.trans scaled product.equivalent⟩
      have nonzero : reading.value ≠ 0 :=
        Field.mul_ne_zero_direct firstNonzero tail.2.1
      let prepared := reading.prepare nonzero
      ⟨reading, nonzero, ⟨ready.toPreparation, tail.2.2,
        ⟨prepared.denominator, prepared.apart, prepared.equivalent⟩⟩⟩

/-- Construct all full-word fold preparations after exact ordered rational execution completes. -/
@[noinline, nospecialize] def Execution.fullFoldPreparations {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) : Fold.Basic.FoldPreparations tau matrices :=
  Fold.Basic.FoldPreparations.transportRequest (execution.prefix_eq_of_complete completed) execution.foldData.2.2

/-- Completed rational inspection agrees with any independently supplied schedule for the same original ordered word. -/
def Execution.agrees_with_preparations {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) (other : Step.StepPreparations tau matrices) :
    NamedEquivalent execution.output.name (Step.stepAction tau matrices other).name := by
  have equivalent := Step.stepAction_preparation_independent tau matrices
    (execution.fullPreparations completed) other
  rewrite [execution.output_eq_full completed]
  exact equivalent

/-- Completed rational inspection agrees with the actual output of independently supplied full fold preparations. -/
def Execution.agrees_with_fold {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) (other : Fold.Basic.FoldPreparations tau matrices) :
    NamedEquivalent execution.output.name (Fold.Basic.foldAction tau matrices other).name :=
  execution.agrees_with_preparations completed (Fold.Basic.FoldPreparations.toSteps matrices other)

/-- Completed rational inspection agrees with an independently prepared folded-matrix action. -/
def Execution.agrees_with_product {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) (other : Fold.Basic.FoldPreparations tau matrices) :
    NamedEquivalent execution.output.name
      (fractionalLinear (Word.matrixProduct matrices) tau
        (Fold.Basic.FoldPreparations.combined matrices other)).name :=
  NamedEquivalent.trans (execution.agrees_with_fold completed other)
    (NamedEquivalent.symm (Fold.Comparison.productOutput_equivalent_foldAction matrices tau other))

/-- The successful cached rational output agrees with its automatically prepared single-product action. -/
def Execution.agrees_with_folded_output {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices)
    (completed : execution.firstUndefined = none) :
    NamedEquivalent execution.output.name
      (fractionalLinear (Word.matrixProduct matrices) tau
        (Fold.Basic.FoldPreparations.combined matrices (execution.fullFoldPreparations completed))).name :=
  execution.agrees_with_product completed (execution.fullFoldPreparations completed)

/-- Independent successful rational executions agree across their explicitly compared original input channels. -/
def Execution.respects {first second : CoherentNamed} {leftSource : RationalSidecar first}
    {rightSource : RationalSidecar second} {matrices : List IntegralMatrix}
    (left : Execution leftSource matrices) (right : Execution rightSource matrices)
    (leftComplete : left.firstUndefined = none) (rightComplete : right.firstUndefined = none)
    (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent left.output.name right.output.name := by
  have compared := Step.stepAction_respects matrices first second equivalent
    (left.fullPreparations leftComplete) (right.fullPreparations rightComplete)
  rewrite [left.output_eq_full leftComplete, right.output_eq_full rightComplete]
  exact compared

/-- Completion of a retained productive step certifies completion of its same cached tail. -/
theorem Execution.tail_complete {tau : CoherentNamed} {input : RationalSidecar tau} {matrix : IntegralMatrix}
    {remaining : List IntegralMatrix} (rows : Integral.Rational.Rows input matrix)
    (ready : Integral.Rational.Ready rows) (tail : Execution ready.reading remaining)
    (completed : (Execution.step matrix remaining rows ready tail).firstUndefined = none) :
    tail.firstUndefined = none := by
  cases selected : tail.firstUndefined with
  | none => rfl
  | some index =>
      change tail.firstUndefined.map Nat.succ = none at completed
      rewrite [selected] at completed
      cases completed

/-- Append another retained execution at the exact cached output of a completed original request. -/
@[noinline, nospecialize] def Execution.append {tau : CoherentNamed} {input : RationalSidecar tau}
    {first second : List IntegralMatrix} (execution : Execution input first)
    (completed : execution.firstUndefined = none) (next : Execution execution.reading second) :
    Execution input (first ++ second) :=
  match execution with
  | .complete _ source_eq => source_eq ▸ next
  | .blocked _ _ _ _ _ => nomatch completed
  | .step matrix remaining rows ready tail =>
      .step matrix (remaining ++ second) rows ready
        (tail.append (Execution.tail_complete rows ready tail completed) next)

/-- Inspect only the new request at a completed execution's same cached output and append the retained results. -/
@[noinline, nospecialize] def Execution.continue {tau : CoherentNamed} {input : RationalSidecar tau}
    {first : List IntegralMatrix} (execution : Execution input first)
    (completed : execution.firstUndefined = none) (second : List IntegralMatrix) :
    Execution input (first ++ second) :=
  execution.append completed (inspect execution.reading second)

/-- Appending retained execution reuses the exact final numerical channel of the supplied continuation. -/
theorem Execution.append_output {tau : CoherentNamed} {input : RationalSidecar tau}
    {first second : List IntegralMatrix} (execution : Execution input first)
    (completed : execution.firstUndefined = none) (next : Execution execution.reading second) :
    (execution.append completed next).output = next.output := by
  induction execution with
  | complete source source_eq =>
      cases source_eq
      rfl
  | blocked matrix remaining rows zero identity => cases completed
  | step matrix remaining rows ready tail ih =>
      exact ih (Execution.tail_complete rows ready tail completed) next

/-- Adding an empty prefix preserves an optional original position. -/
private theorem position_zero (position : Option Nat) : position.map (0 + ·) = position := by
  cases position with
  | none => rfl
  | some index => exact congrArg Option.some (Nat.zero_add index)

/-- Adding one prepared step increments the optional shifted original position. -/
private theorem position_succ (position : Option Nat) (count : Nat) :
    (position.map (count + ·)).map Nat.succ = position.map ((count + 1) + ·) := by
  cases position with
  | none => rfl
  | some index => exact congrArg Option.some (Nat.succ_add count index).symm

/-- Appending at a completed cached prefix preserves the continuation's exact undefined-step position. -/
theorem Execution.append_firstUndefined {tau : CoherentNamed} {input : RationalSidecar tau}
    {first second : List IntegralMatrix} (execution : Execution input first)
    (completed : execution.firstUndefined = none) (next : Execution execution.reading second) :
    (execution.append completed next).firstUndefined = next.firstUndefined.map (first.length + ·) := by
  induction execution with
  | complete source source_eq =>
      cases source_eq
      exact (position_zero next.firstUndefined).symm
  | blocked matrix remaining rows zero identity => cases completed
  | step matrix remaining rows ready tail ih =>
      have recurse := ih (Execution.tail_complete rows ready tail completed) next
      exact (congrArg (Option.map Nat.succ) recurse).trans
        (position_succ next.firstUndefined remaining.length)

/-- Two completed ordered executions undo each other when their actual folded matrices multiply to identity.

The proof constructs every combined denominator from the retained successful
row caches. Both complete schedules remain required: the matrix identity alone
cannot establish the definedness of an intermediate step.
-/
def Execution.reversal {tau : CoherentNamed} {input : RationalSidecar tau}
    {forward reverse : List IntegralMatrix} (execution : Execution input forward)
    (completed : execution.firstUndefined = none) (next : Execution execution.reading reverse)
    (reverseComplete : next.firstUndefined = none)
    (inverse : Multiplication.mul
      (Word.matrixProduct reverse) (Word.matrixProduct forward) =
        Multiplication.identity) :
    NamedEquivalent next.output.name tau.name := by
  let joined := execution.append completed next
  have joinedComplete : joined.firstUndefined = none := by
    rewrite [Execution.append_firstUndefined execution completed next, reverseComplete]
    rfl
  have combined := joined.agrees_with_folded_output joinedComplete
  have identity := Integral.Identity.fractionalLinear_of_matrix_eq_identity
    (Word.matrixProduct (forward ++ reverse)) tau
    (Fold.Basic.FoldPreparations.combined (forward ++ reverse) (joined.fullFoldPreparations joinedComplete))
    ((Word.matrixProduct_append forward reverse).trans inverse)
  have result := NamedEquivalent.trans combined identity
  rewrite [Execution.append_output execution completed next] at result
  exact result

set_option genInjectivity false in
/-- The first actual undefined step after a retained prepared prefix, with its original row and exact zero reading. -/
structure Stopped {tau : CoherentNamed} {input : RationalSidecar tau} {matrices : List IntegralMatrix}
    (execution : Execution input matrices) (index : Nat) where
  /-- The actual first unexecuted original matrix. -/
  matrix : IntegralMatrix
  /-- The original unexecuted suffix after that matrix. -/
  suffix : List IntegralMatrix
  /-- The retained matrices are the actual stopped suffix. -/
  remaining_eq : execution.remaining = matrix :: suffix
  /-- Every earlier original step is prepared; this index is its exact prefix length. -/
  index_eq : execution.prefix.length = index
  /-- The actual original denominator at the retained stopped channel. -/
  denominator : CoherentNamed
  /-- The denominator is the first unexecuted original matrix's actual row. -/
  denominator_eq : denominator = fractionalDenominator matrix execution.output
  /-- Exact rational evidence at this same original denominator. -/
  reading : RationalSidecar denominator
  /-- The actual checked exact coefficient is zero. -/
  zero : reading.value = 0
  /-- The actual original denominator is operationally zero. -/
  identity : Zero.ZeroIdentity denominator

constructive_injectivity Stopped

/-- Read the actual first undefined-step certificate while retaining the same complete prepared prefix and zero row. -/
@[noinline, nospecialize] def Execution.stopped {tau : CoherentNamed} {input : RationalSidecar tau}
    {matrices : List IntegralMatrix} (execution : Execution input matrices) (index : Nat)
    (selected : execution.firstUndefined = some index) : Stopped execution index :=
  match execution with
  | .complete _ _ => nomatch selected
  | .blocked matrix remaining rows zero identity =>
      ⟨matrix, remaining, rfl,
        (Execution.blocked matrix remaining rows zero identity).firstUndefined_eq_prefix_length index selected,
        rows.denominator, rows.denominator_eq, rows.denominatorReading, zero, identity⟩
  | .step matrix remaining rows ready next => by
      cases earlier : next.firstUndefined with
      | none =>
          change next.firstUndefined.map Nat.succ = some index at selected
          rewrite [earlier] at selected
          cases selected
      | some position =>
          let stopped := next.stopped position earlier
          exact ⟨stopped.matrix, stopped.suffix, stopped.remaining_eq,
            (Execution.step matrix remaining rows ready next).firstUndefined_eq_prefix_length index selected,
            stopped.denominator,
            stopped.denominator_eq, stopped.reading, stopped.zero, stopped.identity⟩

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Rational

end
