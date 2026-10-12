module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Inverse
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold
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

/-! ## Stepwise productive reversal -/

set_option genInjectivity false in
/-- A shallow carrier for the evidence needed to reverse an actual prepared finite-word execution.

The reverse fold is indexed by the literal output of the forward fold, while the composition certificate retains its
independently prepared single-product representatives. -/
structure FoldReversalPreparationsPayload
    (forwardType : Type 1) (forwardOutput : forwardType -> CoherentNamed)
    (reverseType : (forward : forwardType) -> Type 1)
    (compositionType : Type 1) where
  /-- The precisely indexed preparations for the forward word. -/ forward : forwardType
  /-- The reverse preparations indexed by the retained forward preparation and its actual output. -/ reverse :
    reverseType forward
  /-- The retained preparation of the two folded matrix actions and their combined action. -/ composition :
    compositionType

constructive_injectivity FoldReversalPreparationsPayload

/-- Precisely indexed preparations for a stepwise forward word, its stepwise reverse beginning at the actual forward
output, and the certified folded composition used to prove cancellation. -/
@[expose] def FoldReversalPreparations (forward reverse : List LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : CoherentNamed) : Type 1 :=
  Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal.FoldReversalPreparationsPayload
    (Fold.Basic.FoldPreparations tau forward)
    (fun preparation => Fold.Basic.foldAction tau forward preparation)
    (fun preparation => Fold.Basic.FoldPreparations
      (Fold.Basic.foldAction tau forward preparation) reverse)
    (Composition.Basic.CompositionPreparation
      (Word.matrixProduct reverse) (Word.matrixProduct forward) tau)

/-- A stepwise prepared reverse word undoes the actual stepwise prepared forward word whenever their exact folded
matrices are certified inverses.

Every local denominator remains indexed by the concrete intermediate name at which it is consumed. -/
@[expose] def foldAction_reversal (forward reverse : List LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : CoherentNamed)
    (preparations : Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal.FoldReversalPreparations
      forward reverse tau)
    (inverse : Multiplication.mul
        (Word.matrixProduct reverse) (Word.matrixProduct forward) =
      Multiplication.identity) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction
        (Fold.Basic.foldAction tau forward preparations.forward)
        reverse preparations.reverse).name tau.name := by
  let forwardOutput := Fold.Basic.foldAction tau forward preparations.forward
  let reverseOutput := Fold.Basic.foldAction forwardOutput reverse preparations.reverse
  let forwardSingle := fractionalLinear (Word.matrixProduct forward) tau
    (FoldPreparations.combined forward preparations.forward)
  let reverseSingle := fractionalLinear (Word.matrixProduct reverse) forwardOutput
    (FoldPreparations.combined reverse preparations.reverse)
  have forwardSingleToFold : Gaussian.Equivalence.NamedEquivalent forwardSingle.name
      forwardOutput.name := by
    simpa only [forwardSingle, forwardOutput] using
      Comparison.productOutput_equivalent_foldAction forward tau preparations.forward
  have forwardSingleToComposition : Gaussian.Equivalence.NamedEquivalent forwardSingle.name
      preparations.composition.innerOutput.name := by
    simpa only [forwardSingle, CompositionPreparation.innerOutput] using
      Comparison.fractionalLinear_preparation_independent (Word.matrixProduct forward) tau
        (FoldPreparations.combined forward preparations.forward)
        preparations.composition.inner
  have forwardFoldToComposition : Gaussian.Equivalence.NamedEquivalent forwardOutput.name
      preparations.composition.innerOutput.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm forwardSingleToFold)
      forwardSingleToComposition
  have reverseSingleToFold : Gaussian.Equivalence.NamedEquivalent reverseSingle.name
      reverseOutput.name := by
    simpa only [reverseSingle, reverseOutput, forwardOutput] using
      Comparison.productOutput_equivalent_foldAction reverse forwardOutput
        preparations.reverse
  have reverseInputsAgree : Gaussian.Equivalence.NamedEquivalent reverseSingle.name
      preparations.composition.nestedOutput.name := by
    simpa only [reverseSingle, CompositionPreparation.nestedOutput] using
      Comparison.fractionalLinear_respects (Word.matrixProduct reverse) forwardOutput
        preparations.composition.innerOutput forwardFoldToComposition
        (FoldPreparations.combined reverse preparations.reverse)
        preparations.composition.outer
  have compositionCancels : Gaussian.Equivalence.NamedEquivalent
      preparations.composition.nestedOutput.name tau.name :=
    Inverse.fractionalLinear_inverse_of_mul_eq_identity
      (Word.matrixProduct reverse) (Word.matrixProduct forward) tau
      preparations.composition inverse
  change Gaussian.Equivalence.NamedEquivalent reverseOutput.name tau.name
  exact NamedEquivalent.trans
    (NamedEquivalent.symm reverseSingleToFold)
    (NamedEquivalent.trans reverseInputsAgree
      compositionCancels)

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
