module
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Composition.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Homogeneous
import Purelib.Approximation.Matrix.Operational.Integral.Action
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Generators
import Purelib.Topology.Knot.Braid.ThreeStrand.Integral.Words

import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Reversal
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Product
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Topology.Knot.Braid.Basic

namespace Purelib.Curves.Legendre.FractionalWords.Braid

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Vector.Operational.Basic
open Purelib.Approximation.Matrix.Operational.Integral
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

/-! ## Matrix-equivalent words and reversal -/

/-- The exact integral matrices carried by a finite three-strand braid word, retained in traversal order. -/
@[expose] def braidMatrices (word : Braid.Word 3) :
    List IntegralMatrix :=
  word.map Generators.generatorMatrix

/-- Folding the matrices of a finite braid word is exactly the established Picard--Lefschetz word matrix. -/
theorem matrixProduct_braidMatrices
    (word : Braid.Word 3) :
    Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word) =
      Words.wordMatrix word := by
  induction word with
  | nil => rfl
  | cons generator remaining inductionHypothesis =>
      change Multiplication.mul
          (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices remaining))
          (Generators.generatorMatrix generator) =
        Multiplication.mul
          (Words.wordMatrix remaining)
          (Generators.generatorMatrix generator)
      rw [inductionHypothesis]

/-- Reversing a finite braid word and reversing each of its certified generator matrices gives a left inverse of the
traversal-order matrix fold. -/
theorem braidMatrices_inverse_left
    (word : Braid.Word 3) :
    Multiplication.mul
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse))
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word)) =
      Multiplication.identity := by
  rw [Curves.Legendre.FractionalWords.Braid.matrixProduct_braidMatrices,
    Curves.Legendre.FractionalWords.Braid.matrixProduct_braidMatrices]
  exact
    (Words.wordMatrix_inverse_identities word).1

/-- The same certified generator reversal is also a right inverse. -/
theorem braidMatrices_inverse_right
    (word : Braid.Word 3) :
    Multiplication.mul
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word))
        (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse)) =
      Multiplication.identity := by
  rw [Curves.Legendre.FractionalWords.Braid.matrixProduct_braidMatrices,
    Curves.Legendre.FractionalWords.Braid.matrixProduct_braidMatrices]
  exact
    (Words.wordMatrix_inverse_identities word).2

/-- Finite braid-word reversal undoes the homogeneous fractional action with no denominator evidence.

The inverse law is derived from the certified inverse of every displayed braid generator. -/
@[expose] def braidWord_reversal_rows (word : Braid.Word 3)
    (tau : CoherentNamed) :
    Gaussian.Vector.Operational.Basic.VectorEquivalent
      (Action.matrixAction (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse))
        (Action.matrixAction (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word))
          (fractionalVector tau)))
      (fractionalVector tau) :=
  Homogeneous.fractionalRows_inverse_of_mul_eq_identity
    (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse))
    (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word)) tau
    (Curves.Legendre.FractionalWords.Braid.braidMatrices_inverse_left word)

/-- Productive finite braid-word reversal, with all three denominator preparations retained at their exact combined and
intermediate names. -/
@[expose] def braidWord_productReversal (word : Braid.Word 3)
    (tau : CoherentNamed)
    (preparation : Composition.Basic.CompositionPreparation
      (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse))
      (Word.matrixProduct (Curves.Legendre.FractionalWords.Braid.braidMatrices word)) tau) :
    Gaussian.Equivalence.NamedEquivalent preparation.nestedOutput.name tau.name :=
  Words.Product.productReversal (Curves.Legendre.FractionalWords.Braid.braidMatrices word)
    (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse) tau
    preparation (Curves.Legendre.FractionalWords.Braid.braidMatrices_inverse_left word)

/-- Reversing a finite braid word and every certified generator undoes its actual stepwise productive fold, not merely
the quotient by its folded matrix. -/
@[expose] def braidWord_foldReversal (word : Braid.Word 3)
    (tau : CoherentNamed)
    (preparations : Reversal.FoldReversalPreparations
      (Curves.Legendre.FractionalWords.Braid.braidMatrices word) (Curves.Legendre.FractionalWords.Braid.braidMatrices
        word.inverse) tau) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction
        (Fold.Basic.foldAction tau (Curves.Legendre.FractionalWords.Braid.braidMatrices word) preparations.forward)
        (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse) preparations.reverse).name tau.name :=
  Reversal.foldAction_reversal (Curves.Legendre.FractionalWords.Braid.braidMatrices word)
    (Curves.Legendre.FractionalWords.Braid.braidMatrices word.inverse) tau
    preparations (Curves.Legendre.FractionalWords.Braid.braidMatrices_inverse_left word)

end

end Purelib.Curves.Legendre.FractionalWords.Braid
