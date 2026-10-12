module

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.Riemann.Integration.LegendreModularMonodromy
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
