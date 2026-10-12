module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Dual

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Homogeneous
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Approximation.Matrix.Operational.Integral.Word
public import Purelib.Curves.Legendre.FractionalWords.Braid
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

namespace Purelib.Curves.Legendre.FractionalWords.Periods

open Purelib
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Vector.Operational.Basic
open Purelib.Approximation.Matrix.Operational.Integral
open Purelib.Curves.Legendre.FractionalWords
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

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

/-- Transposed generator matrices in the reverse list order forced by dual period transport.

The reversal is essential: transposition reverses the homology matrix product. -/
@[expose] def periodBraidMatrices (word : Braid.Word 3) :
    List IntegralMatrix :=
  Word.dualMatrices (Braid.braidMatrices word)

/-- The finite fold of the reversed transposed generators is exactly the dual matrix acting on the period column. -/
theorem matrixProduct_periodBraidMatrices
    (word : Braid.Word 3) :
    Word.matrixProduct (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) =
      Dual.periodMatrix word := by
  rw [Curves.Legendre.FractionalWords.Periods.periodBraidMatrices, Word.matrixProduct_dualMatrices,
    Braid.matrixProduct_braidMatrices]
  rfl

/-- For an arbitrary finite braid word, its dual homogeneous period rows are the stepwise action of the reversed
transposed generator list. -/
@[expose] def periodBraidRows_word (word : Braid.Word 3)
    (tau : CoherentNamed) :
    Gaussian.Vector.Operational.Basic.VectorEquivalent
      (Action.matrixAction
        (Dual.periodMatrix word)
        (fractionalVector tau))
      (Word.blockAction (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) (fractionalVector tau)) := by
  rw [← Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices word]
  exact Homogeneous.fractionalRows_word (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) tau

/-- The preparations needed to execute the dual action of every generator and compare it with the one exact folded
period matrix. -/
@[expose] def PeriodFoldPreparations (word : Braid.Word 3)
    (tau : CoherentNamed) : Type 1 :=
  Fold.Basic.FoldPreparations tau (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)

/-- Reindex the retained combined preparation by the proved equality between the finite dual fold and `periodMatrix`. -/
@[expose] def PeriodFoldPreparations.periodPreparation
    (word : Braid.Word 3) (tau : CoherentNamed)
    (preparations : Curves.Legendre.FractionalWords.Periods.PeriodFoldPreparations word tau) :
    Gaussian.Division.Prepared.DenominatorPreparation
      (fractionalDenominator
        (Dual.periodMatrix word) tau) := by
  rw [← Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices word]
  exact FoldPreparations.combined (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) preparations

/-- One productive quotient by the exact dual period matrix agrees with the actual stepwise execution of all reversed
transposed generators. -/
@[expose] def periodOutput_equivalent_foldAction
    (word : Braid.Word 3) (tau : CoherentNamed)
    (preparations : Curves.Legendre.FractionalWords.Periods.PeriodFoldPreparations word tau) :
    Gaussian.Equivalence.NamedEquivalent
      (fractionalLinear
        (Dual.periodMatrix word) tau
        (preparations.periodPreparation word tau)).name
      (Fold.Basic.foldAction tau (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) preparations).name
        :=
  NamedEquivalent.trans
    (Comparison.fractionalLinear_of_matrix_eq
      (Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices word).symm tau
      (preparations.periodPreparation word tau)
      (FoldPreparations.combined (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) preparations))
    (Comparison.productOutput_equivalent_foldAction
      (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word) tau preparations)

/-- The stepwise productive dual word satisfies the fraction-free quotient equation for the exact period matrix. -/
@[expose] def periodFold_denominator_mul
    (word : Braid.Word 3) (tau : CoherentNamed)
    (preparations : Curves.Legendre.FractionalWords.Periods.PeriodFoldPreparations word tau) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul
        (fractionalDenominator
          (Dual.periodMatrix word) tau)
        (Fold.Basic.foldAction tau (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)
          preparations)).name
      (fractionalNumerator
        (Dual.periodMatrix word) tau).name := by
  let matrix := Dual.periodMatrix word
  let denominator := fractionalDenominator matrix tau
  let direct := fractionalLinear matrix tau
    (preparations.periodPreparation word tau)
  let folded := Fold.Basic.foldAction tau (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)
    preparations
  have directToFold : Gaussian.Equivalence.NamedEquivalent direct.name folded.name := by
    simpa only [matrix, direct, folded] using
      Curves.Legendre.FractionalWords.Periods.periodOutput_equivalent_foldAction word tau preparations
  have replaceFold : Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul denominator folded).name
      (CoherentNamed.mul denominator direct).name :=
    Congruence.coherentMul_respects
      denominator denominator folded direct
      (NamedEquivalent.refl denominator.name)
      (NamedEquivalent.symm directToFold)
  exact NamedEquivalent.trans replaceFold
    (by
      simpa only [matrix, denominator, direct] using
        denominator_mul_fractionalLinear matrix tau
          (preparations.periodPreparation word tau))

/-- The dual period fold of the inverse braid is a left inverse of the dual period fold of the original braid. -/
theorem periodBraidMatrices_inverse_left
    (word : Braid.Word 3) :
    Multiplication.mul
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse))
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)) =
      Multiplication.identity := by
  rw [Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices,
    Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices]
  exact
    (Dual.periodMatrix_inverse_identities
      word).2

/-- The corresponding dual period folds are inverse in the other multiplication order as well. -/
theorem periodBraidMatrices_inverse_right
    (word : Braid.Word 3) :
    Multiplication.mul
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word))
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse)) =
      Multiplication.identity := by
  rw [Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices,
    Curves.Legendre.FractionalWords.Periods.matrixProduct_periodBraidMatrices]
  exact
    (Dual.periodMatrix_inverse_identities
      word).1

/-- For every finite braid word, a prepared stepwise dual action followed by the prepared dual action of the inverse
word returns the original normalized period ratio operationally. -/
@[expose] def periodBraidWord_foldReversal (word : Braid.Word 3)
    (tau : CoherentNamed)
    (preparations : Reversal.FoldReversalPreparations
      (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)
        (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse) tau) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction
        (Fold.Basic.foldAction tau (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)
          preparations.forward)
        (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse) preparations.reverse).name
      tau.name :=
  Reversal.foldAction_reversal (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word)
    (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices word.inverse) tau preparations
    (Curves.Legendre.FractionalWords.Periods.periodBraidMatrices_inverse_left word)

end

end Purelib.Curves.Legendre.FractionalWords.Periods
