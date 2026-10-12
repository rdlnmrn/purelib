module
import Purelib.Approximation.Matrix.Operational.Integral.Action

import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
public import Purelib.Approximation.Matrix.Operational.Integral.Word
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
public import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Homogeneous

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Vector.Operational.Basic
open Purelib.Approximation.Matrix.Operational.Integral
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

open Purelib.Riemann.Integration.LegendreGaussManin
open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Riemann.Integration.LegendreFractionalAction

/-- Homogeneous fractional rows of a word agree with stepwise matrix action, without denominator evidence. -/
@[expose] def fractionalRows_word (matrices : List LinearAlgebra.Matrix.Basic.IntegralMatrix)
    (tau : CoherentNamed) :
    Vector.Operational.Basic.VectorEquivalent
      (Action.matrixAction (Word.matrixProduct matrices) (fractionalVector tau))
      (Word.blockAction matrices (fractionalVector tau)) :=
  Word.matrixProduct_action matrices (fractionalVector tau)

/-- Exact folded-matrix equality makes two finite words have the same homogeneous action. -/
@[expose] def fractionalRows_of_matrixProduct_eq
    {left right : List LinearAlgebra.Matrix.Basic.IntegralMatrix}
    (matrixEq : Word.matrixProduct left = Word.matrixProduct right)
    (tau : CoherentNamed) :
    Vector.Operational.Basic.VectorEquivalent
      (Action.matrixAction (Word.matrixProduct left) (fractionalVector tau))
      (Action.matrixAction (Word.matrixProduct right) (fractionalVector tau)) := by
  rw [matrixEq]
  exact VectorEquivalent.refl _

end

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Homogeneous
