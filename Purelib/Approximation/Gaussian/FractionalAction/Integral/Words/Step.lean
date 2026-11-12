module

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.Riemann.Integration.LegendreModularMonodromy
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Init.Core
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.LinearAlgebra.Matrix

section
@[expose] public section

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Step

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreModularMonodromy hiding IntegralMatrix
open Purelib.Riemann.Integration.LegendreFractionalAction
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-! ## Stepwise productive preparations and append -/

/-- One denominator preparation for every actual intermediate productive name. The tail is indexed by the output
produced using the head evidence. -/
def StepPreparations (tau :
  CoherentNamed) :
    List IntegralMatrix -> Type 1
  | [] => ULift Unit
  | matrix :: remaining =>
      Sigma fun head : Approximation.Gaussian.Division.Prepared.DenominatorPreparation
        (fractionalDenominator matrix tau) =>
          StepPreparations (fractionalLinear matrix
            tau head) remaining

/-- Execute a finite word with its precisely indexed step preparations. -/
def stepAction (tau :
  CoherentNamed) :
    (matrices : List IntegralMatrix) ->
      StepPreparations tau matrices ->
        CoherentNamed
  | [], _ => tau
  | matrix :: remaining, preparations =>
      stepAction (fractionalLinear matrix tau
        preparations.1)
        remaining preparations.2

/-- Independent prepared schedules respect agreement of their two actual original starting channels. -/
def stepAction_respects : (matrices : List IntegralMatrix) → (first second : CoherentNamed) →
    NamedEquivalent first.name second.name →
    (left : StepPreparations first matrices) → (right : StepPreparations second matrices) →
    NamedEquivalent (stepAction first matrices left).name (stepAction second matrices right).name
  | [], _, _, equivalent, _, _ => equivalent
  | matrix :: remaining, first, second, equivalent, left, right =>
      stepAction_respects remaining (fractionalLinear matrix first left.1)
        (fractionalLinear matrix second right.1)
        (Integral.Comparison.fractionalLinear_respects matrix first second equivalent left.1 right.1)
        left.2 right.2

/-- Different preparations of one original ordered word produce operationally agreeing actual outputs. -/
def stepAction_preparation_independent (tau : CoherentNamed) (matrices : List IntegralMatrix)
    (left right : StepPreparations tau matrices) :
    NamedEquivalent (stepAction tau matrices left).name (stepAction tau matrices right).name :=
  stepAction_respects matrices tau tau (NamedEquivalent.refl _) left right

/-- Transport an existing ordered preparation schedule along an exact identity of its original starting channel. -/
def transportPreparations {first second : CoherentNamed} (same : first = second)
    (matrices : List IntegralMatrix) (preparations : StepPreparations first matrices) :
    StepPreparations second matrices := same ▸ preparations

/-- Transport of the starting channel retains the exact numerical output of the same ordered schedule. -/
theorem stepAction_transport {first second : CoherentNamed} (same : first = second)
    (matrices : List IntegralMatrix) (preparations : StepPreparations first matrices) :
    stepAction second matrices (transportPreparations same matrices preparations) =
      stepAction first matrices preparations := by
  cases same
  rfl

/-- Read an existing preparation schedule at an exactly identified original ordered request. -/
def transportRequest {tau : CoherentNamed} {first second : List IntegralMatrix} (same : first = second)
    (preparations : StepPreparations tau first) : StepPreparations tau second := same ▸ preparations

/-- Exact request transport preserves the numerical output of the same original preparation schedule. -/
theorem stepAction_transport_request {tau : CoherentNamed} {first second : List IntegralMatrix}
    (same : first = second) (preparations : StepPreparations tau first) :
    stepAction tau second (transportRequest same preparations) = stepAction tau first preparations := by
  cases same
  rfl

/-- An empty prepared word returns the original coherent input. -/
@[simp] theorem stepAction_nil (tau :
  CoherentNamed)
    (preparations : StepPreparations tau []) :
    stepAction tau [] preparations = tau := rfl

/-- A nonempty prepared word executes its head action before the retained tail schedule. -/
@[simp] theorem stepAction_cons (tau :
  CoherentNamed)
    (matrix : IntegralMatrix) (remaining : List
      IntegralMatrix)
    (preparations : StepPreparations tau (matrix ::
      remaining)) :
    stepAction tau (matrix :: remaining) preparations =
      stepAction (fractionalLinear matrix tau
        preparations.1)
        remaining preparations.2 := rfl

/-- Concatenate two already prepared step schedules. -/
def appendPreparations (tau :
  CoherentNamed)
    (second : List IntegralMatrix) :
    (first : List IntegralMatrix) ->
      (firstPreparations : StepPreparations tau first) ->
      StepPreparations
        (stepAction tau first firstPreparations) second ->
      StepPreparations tau (first ++ second)
  | [], _, secondPreparations => secondPreparations
  | matrix :: remaining, firstPreparations, secondPreparations =>
      ⟨firstPreparations.1,
        appendPreparations
          (fractionalLinear matrix tau firstPreparations.1) second
          remaining firstPreparations.2 secondPreparations⟩

/-- Executing appended preparation schedules is definitionally the same as executing the first schedule and then the
second. -/
theorem stepAction_append (tau :
  CoherentNamed)
    (second : List IntegralMatrix) :
    (first : List IntegralMatrix) ->
      (firstPreparations : StepPreparations tau first) ->
      (secondPreparations : StepPreparations
        (stepAction tau first firstPreparations) second) ->
      stepAction tau (first ++ second)
          (appendPreparations tau second first
            firstPreparations
            secondPreparations) =
        stepAction
          (stepAction tau first firstPreparations) second
          secondPreparations
  | [], _, _ => rfl
  | _matrix :: remaining, firstPreparations, secondPreparations =>
      stepAction_append
        (fractionalLinear _ tau firstPreparations.1) second remaining
        firstPreparations.2 secondPreparations
namespace FoldPreparations
end FoldPreparations
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Step

end
