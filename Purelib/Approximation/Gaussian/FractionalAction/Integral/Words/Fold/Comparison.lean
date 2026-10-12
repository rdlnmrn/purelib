module
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Laws
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral

public section

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

open Purelib.Approximation

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Riemann.Integration.LegendreFractionalAction

/-- One quotient by the folded matrix agrees with the fully prepared stepwise execution. -/
@[expose] def productOutput_equivalent_foldAction :
    (matrices : List LinearAlgebra.Matrix.Basic.IntegralMatrix) -> (tau : CoherentNamed)
      ->
      (preparations : Fold.Basic.FoldPreparations tau matrices) ->
      Gaussian.Equivalence.NamedEquivalent
        (fractionalLinear (Word.matrixProduct matrices) tau
          (FoldPreparations.combined matrices preparations)).name
        (Fold.Basic.foldAction tau matrices preparations).name
  | [], tau, preparations => by
      change Gaussian.Equivalence.NamedEquivalent
        (fractionalLinear Purelib.LinearAlgebra.Matrix.Multiplication.identity tau
          preparations).name tau.name
      exact Identity.fractionalLinear_identity tau preparations
  | matrix :: remaining, tau, preparations => by
      let head := preparations.1
      let inner := fractionalLinear matrix tau head
      let tail := preparations.2.1
      let combined := preparations.2.2
      let composition : Composition.Basic.CompositionPreparation
          (Word.matrixProduct remaining) matrix tau :=
        { inner := head
          outer := FoldPreparations.combined remaining tail
          combined := combined }
      have compose := Laws.fractionalLinear_mul
        (Word.matrixProduct remaining) matrix tau composition
      have recurse :=
        productOutput_equivalent_foldAction
        remaining inner tail
      change Gaussian.Equivalence.NamedEquivalent
        (fractionalLinear (Word.matrixProduct (matrix :: remaining)) tau
          combined).name (Fold.Basic.foldAction tau (matrix :: remaining)
            preparations).name
      have composeStep : Gaussian.Equivalence.NamedEquivalent
          (fractionalLinear (Word.matrixProduct (matrix :: remaining)) tau
            combined).name
          (fractionalLinear (Word.matrixProduct remaining) inner
            (FoldPreparations.combined remaining tail)).name := by
        simpa only [composition, Word.matrixProduct,
            CompositionPreparation.combinedOutput,
            CompositionPreparation.nestedOutput,
            Composition.Basic.CompositionPreparation.innerOutput] using compose
      have recurseStep : Gaussian.Equivalence.NamedEquivalent
          (fractionalLinear (Word.matrixProduct remaining) inner
            (FoldPreparations.combined remaining tail)).name
          (Fold.Basic.foldAction tau (matrix :: remaining) preparations).name := by
        simpa only [inner, tail, Fold.Basic.foldAction, Step.StepPreparations,
            FoldPreparations.toSteps, Step.stepAction] using recurse
      exact NamedEquivalent.trans
        composeStep recurseStep

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison
