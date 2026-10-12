module
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Inverse
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Product

open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
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

/-- Independently prepared finite words with the same exact folded matrix produce operationally equivalent
single-product outputs. -/
@[expose] def productOutput_of_matrixProduct_eq
    {left right : List LinearAlgebra.Matrix.Basic.IntegralMatrix}
    (matrixEq : Word.matrixProduct left = Word.matrixProduct right)
    (tau : CoherentNamed)
    (leftPreparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator (Word.matrixProduct left) tau))
    (rightPreparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator (Word.matrixProduct right) tau)) :
    Gaussian.Equivalence.NamedEquivalent
      (fractionalLinear (Word.matrixProduct left) tau leftPreparation).name
      (fractionalLinear (Word.matrixProduct right) tau rightPreparation).name :=
  Comparison.fractionalLinear_of_matrix_eq matrixEq tau
    leftPreparation rightPreparation

/-- A finite reverse word whose folded matrix is a certified left inverse undoes the forward word at the productive
single-product level. -/
@[expose] def productReversal
    (forward reverse : List LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau :
      CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation
      (Word.matrixProduct reverse) (Word.matrixProduct forward) tau)
    (inverse : Multiplication.mul
        (Word.matrixProduct reverse) (Word.matrixProduct forward) =
      Multiplication.identity) :
    Gaussian.Equivalence.NamedEquivalent preparation.nestedOutput.name tau.name :=
  Inverse.fractionalLinear_inverse_of_mul_eq_identity
    (Word.matrixProduct reverse) (Word.matrixProduct forward) tau preparation inverse

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Product
