module
import Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Division.Gap.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
import Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch
import Purelib.Approximation.Gaussian.Division.Acquisition.State
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.RootIsolation.SquareRoot.Observation.Annotated
import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Division.Gap
import Purelib.Approximation.Gaussian.Division.Acquisition.Report
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Polynomial.Multivariate.Sparse

open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

/-! Regression checks for the retained approximation gaussian acquisition automation contracts. -/

namespace TestPurelib.Approximation.Gaussian.Acquisition.Automation

open Purelib.Examples.Approximation.Gaussian.Acquisition.Automation.WorkedExamples

open Purelib.Approximation.Gaussian.Acquisition (Annotated)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples (oneInput tinyInput zeroInput)
open Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne (delayedOne)
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Name
open Purelib.Examples.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Polynomial.Multivariate (Sparse)

/-- The acquisition report retains the delayed denominator's refined source. -/
theorem delayed_state_retained :
  delayedDivision.1.next.state.source = true := rfl

/-- Delayed acquisition preserves its original next-index counter. -/
theorem delayed_index_unchanged :
  delayedDivision.1.next.state.nextIndex = 0 := rfl

/-- Resuming the ready delayed report uses its cached acquisition route. -/
theorem delayed_resume_uses_cache :
  (Acquisition.Dispatch.Report.resume delayedDivision
  Bounded.WorkedExamples.tinyInput 1 (by decide)).1.route = .cached := rfl

/-- Resuming the tiny denominator with its smaller certified threshold prepares it.

Reuses the original numerical report and requests the exact positive squared-norm gap of the fixed tiny input. -/
theorem tiny_resume_finer_ready :
    (Acquisition.Dispatch.Report.resume (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput
      opaqueTiny 1 (by decide)) Bounded.WorkedExamples.oneInput
      Gap.WorkedExamples.tinyGap
      Gap.WorkedExamples.tinyGap_positive).2.status = .ready := rfl

/-- Resuming a symbolic cancellation report uses its cached zero result. -/
theorem zero_resume_uses_cache
  (input : CoherentNamed) :
    (Acquisition.Dispatch.Report.resume (Acquisition.Dispatch.acquire Bounded.WorkedExamples.oneInput
      (Acquisition.State.start (cancellation input)) 1 (by decide))
      Bounded.WorkedExamples.tinyInput 1 (by decide)).1.route = .cached := rfl
open Purelib.Approximation.Gaussian.Division.Acquisition

/-- The inferred zero sidecar leaves the original arithmetic evaluator literally unchanged. -/
theorem commuted_zero_original_channel (first second : CoherentNamed) :
    (commutedZero first second).channel = commutedSumDifference.denote (opaquePair first second) :=
  commutedSumDifference.compile_channel (opaquePair first second)

/-- Inferred unit evidence retains the entire original expanded numerical evaluator. -/
theorem expanded_unit_original_channel (first second : CoherentNamed) :
    (expandedUnit first second).channel = expandedUnitExpression.denote (opaquePair first second) :=
  expandedUnitExpression.compile_channel (opaquePair first second)

namespace FoldStep

open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic (FoldPreparations)
open Purelib.Approximation.Gaussian.Name
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalLinear)

/-- The original complete fold transition, used as a regression reference for the selected transition. -/
private def originalStep (tau :
  Coherent.CoherentNamed) : (matrices : List IntegralMatrix) →
    State.Cursor tau matrices → State.Cursor tau matrices
  | [], .inr preparations => .inr preparations
  | [], .inl state =>
      match Acquisition.Step.step _ tau state with
      | .ready preparation => .inr preparation
      | .progressed next _ => .inl next
  | _ :: _, .ready preparations => .ready preparations
  | matrix :: remaining, .head state =>
      match Acquisition.Step.step matrix tau state with
      | .ready preparation => .tail ⟨preparation,
          State.initial (fractionalLinear matrix tau preparation) remaining⟩
      | .progressed next _ => .head next
  | matrix :: remaining, .tail ⟨head, cursor⟩ =>
      match State.finished? (fractionalLinear matrix tau head) remaining cursor with
      | some tail => .combined ⟨head, tail,
          Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩
      | none => .tail ⟨head, originalStep
        (fractionalLinear matrix tau head) remaining cursor⟩
  | _ :: _, .combined ⟨head, tail, state⟩ =>
      match Acquisition.Step.step state.matrix tau state.search with
      | .ready preparation => .ready ⟨head, tail, Cached.cachedPreparation state preparation⟩
      | .progressed next _ => .combined ⟨head, tail, { state with search := next }⟩

/-- Selection and execution preserve the complete original transition for every cursor. -/
theorem step_eq_original (matrices : List IntegralMatrix) :
    ∀ (tau : Coherent.CoherentNamed) (cursor : State.Cursor tau matrices),
      Fold.Step.step tau matrices cursor = originalStep tau matrices cursor := by
  induction matrices with
  | nil =>
      intro tau cursor
      cases cursor <;> rfl
  | cons matrix remaining inductionHypothesis =>
      intro tau cursor
      cases cursor with
      | head state => rfl
      | ready preparations => rfl
      | combined state =>
          rcases state with ⟨head, tail, search⟩
          rfl
      | tail state =>
          rcases state with ⟨head, child⟩
          cases finished : State.finished? (fractionalLinear matrix tau head) remaining child with
          | none =>
              have newStep : Fold.Step.step tau (matrix :: remaining) (.tail ⟨head, child⟩) =
                  .tail ⟨head, Fold.Step.step (fractionalLinear matrix tau head) remaining child⟩ := by
                conv_lhs => unfold Fold.Step.step Fold.Step.select Fold.Step.selectTailWith
                split
                · rename_i actual observed
                  cases finished.symm.trans observed
                · rfl
              have oldStep : originalStep tau (matrix :: remaining) (.tail ⟨head, child⟩) =
                  .tail ⟨head, originalStep (fractionalLinear matrix tau head) remaining child⟩ := by
                conv_lhs => unfold originalStep
                rw [finished]
              rw [newStep, oldStep]

              exact congrArg (fun (next : State.Cursor (fractionalLinear matrix tau head) remaining) =>
                (State.CursorPayload.tail ⟨head, next⟩ : State.Cursor tau (matrix :: remaining)))
                (inductionHypothesis (fractionalLinear matrix tau head) child)
          | some tail =>
              have newStep : Fold.Step.step tau (matrix :: remaining) (.tail ⟨head, child⟩) =
                  .combined ⟨head, tail, Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩ := by
                conv_lhs => unfold Fold.Step.step Fold.Step.select Fold.Step.selectTailWith
                split
                · rename_i actual observed
                  cases Option.some.inj (observed.symm.trans finished)
                  rfl
                · rename_i observed
                  cases observed.symm.trans finished
              have oldStep : originalStep tau (matrix :: remaining) (.tail ⟨head, child⟩) =
                  .combined ⟨head, tail, Cached.cachedInitial tau (Word.matrixProduct (matrix :: remaining))⟩ := by
                conv_lhs => unfold originalStep
                rw [finished]
              rw [newStep, oldStep]

/-- A successful combined observation retains the raw preparation used by its resulting cursor. -/
theorem combined_transition_ready (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (head : Fold.Step.HeadPreparation tau matrix)
    (tail : FoldPreparations (Fold.Step.tailInput tau matrix head) remaining)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
    (preparation : Fold.Step.HeadPreparation tau
      (Fold.Step.inspectCombined tau matrix remaining head tail search).1.val.matrix)
    (ready : (Fold.Step.inspectCombined tau matrix remaining head tail search).2.1.val = .ready preparation) :
    (Fold.Step.inspectCombined tau matrix remaining head tail search).2.2.val =
      .ready ⟨head, tail, Cached.cachedPreparation
        (Fold.Step.inspectCombined tau matrix remaining head tail search).1.val preparation⟩ := by
  rw [(Fold.Step.inspectCombined tau matrix remaining head tail search).2.2.property, ready]
  rfl

/-- A progressed combined observation uses its actual next search in the resulting cursor. -/
theorem combined_transition_progressed (tau : Coherent.CoherentNamed) (matrix : IntegralMatrix)
    (remaining : List IntegralMatrix) (head : Fold.Step.HeadPreparation tau matrix)
    (tail : FoldPreparations (Fold.Step.tailInput tau matrix head) remaining)
    (search : Cached.CachedSearch tau (Word.matrixProduct (matrix :: remaining)))
    (next : Acquisition.State (Fold.Step.inspectCombined tau matrix remaining head tail search).1.val.matrix tau)
    (progress : Coherent.Refinement.State.Progress
      (Fold.Step.inspectCombined tau matrix remaining head tail search).1.val.search next)
    (observed : (Fold.Step.inspectCombined tau matrix remaining head tail search).2.1.val = .progressed next progress) :
    (Fold.Step.inspectCombined tau matrix remaining head tail search).2.2.val =
      .combined ⟨head, tail,
        { (Fold.Step.inspectCombined tau matrix remaining head tail search).1.val with search := next }⟩ := by
  rw [(Fold.Step.inspectCombined tau matrix remaining head tail search).2.2.property, observed]
  rfl
end FoldStep

end TestPurelib.Approximation.Gaussian.Acquisition.Automation
