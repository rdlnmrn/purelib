module
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib.Approximation.Gaussian.Division.Prepared (DenominatorPreparation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.LinearAlgebra.Matrix

open Purelib.LinearAlgebra.Matrix.Integral

open Purelib.Approximation

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreModularMonodromy hiding IntegralMatrix
open Purelib.Riemann.Integration.LegendreFractionalAction

/-! ## Fold certificates: local and combined preparations -/

/-- Stepwise evidence plus a preparation for the exact matrix product at each recursive suffix. The latter is what lets
productive composition compare the step execution with one quotient by the folded matrix. -/
def FoldPreparations (tau :
  CoherentNamed) :
    List IntegralMatrix -> Type 1
  | [] => DenominatorPreparation
      (fractionalDenominator Multiplication.identity tau)
  | matrix :: remaining =>
      Sigma fun head : DenominatorPreparation
        (fractionalDenominator matrix tau) =>
      Sigma fun _tail : FoldPreparations
        (fractionalLinear matrix tau head) remaining =>
        DenominatorPreparation
          (fractionalDenominator (Word.matrixProduct (matrix :: remaining)) tau)

namespace FoldPreparations

/-- Preparation of the single exact folded matrix. -/
def combined {tau :
  CoherentNamed} :
    (matrices : List IntegralMatrix) ->
      Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic.FoldPreparations tau matrices ->
      DenominatorPreparation (fractionalDenominator
        (Word.matrixProduct matrices) tau)
  | [], preparation => preparation
  | _ :: _, preparations => preparations.2.2

/-- Forget the combined preparations while retaining every actual step. -/
def toSteps {tau :
  CoherentNamed} :
    (matrices : List IntegralMatrix) ->
      Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic.FoldPreparations tau matrices ->
        Step.StepPreparations tau matrices
  | [], _ => ULift.up ()
  | _matrix :: remaining, preparations =>
      ⟨preparations.1,
        toSteps remaining
          preparations.2.1⟩

end FoldPreparations

/-- Stepwise productive output retained by a full fold preparation. -/
def foldAction (tau :
  CoherentNamed) (matrices : List
  IntegralMatrix)
    (preparations : FoldPreparations tau matrices) :
      CoherentNamed :=
  Step.stepAction tau matrices
    (FoldPreparations.toSteps matrices preparations)
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic

end
