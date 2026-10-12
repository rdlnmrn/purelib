module
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Identity
import Purelib.LinearAlgebra.Matrix.Multiplication

import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Legendre.Monodromy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Integral.Word
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs

namespace Purelib.Curves.Legendre.FractionalWords.Standard

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Curves.Legendre
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

/-! ## Standard finite words -/

/-- Singleton traversal word for the standard loop around zero. -/
@[expose] def standardZeroMatrices : List IntegralMatrix :=
  [Monodromy.zeroMatrix]

/-- Singleton traversal word for the standard loop around one. -/
@[expose] def standardOneMatrices : List IntegralMatrix :=
  [Monodromy.oneMatrix]

/-- Singleton traversal word for the standard loop around infinity. -/
@[expose] def standardInfinityMatrices : List IntegralMatrix :=
  [Monodromy.infinityMatrix]

/-- The singleton zero-loop matrix word folds to the standard zero homology matrix. -/
@[simp] theorem standardZeroMatrices_product :
    Word.matrixProduct Curves.Legendre.FractionalWords.Standard.standardZeroMatrices =
      Monodromy.zeroMatrix := by
  change Multiplication.mul Multiplication.identity Monodromy.zeroMatrix =
    Monodromy.zeroMatrix
  exact Multiplication.identity_mul_int _

/-- The singleton one-loop matrix word folds to the standard one homology matrix. -/
@[simp] theorem standardOneMatrices_product :
    Word.matrixProduct Curves.Legendre.FractionalWords.Standard.standardOneMatrices =
      Monodromy.oneMatrix := by
  change Multiplication.mul Multiplication.identity Monodromy.oneMatrix =
    Monodromy.oneMatrix
  exact Multiplication.identity_mul_int _

/-- The singleton infinity-loop matrix word folds to the standard infinity homology matrix. -/
@[simp] theorem standardInfinityMatrices_product :
    Word.matrixProduct Curves.Legendre.FractionalWords.Standard.standardInfinityMatrices =
      Monodromy.infinityMatrix := by
  change Multiplication.mul Multiplication.identity Monodromy.infinityMatrix =
    Monodromy.infinityMatrix
  exact Multiplication.identity_mul_int _

/-- The generic prepared finite-word fold specializes to the standard zero-loop quotient `tau / (1 - 2*tau)`. -/
@[expose] def standardZero_fold_formula (tau : CoherentNamed)
    (preparations : Fold.Basic.FoldPreparations tau Curves.Legendre.FractionalWords.Standard.standardZeroMatrices) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction tau Curves.Legendre.FractionalWords.Standard.standardZeroMatrices preparations).name
      (zeroTransform preparations.1).name :=
  NamedEquivalent.refl _

/-- The generic prepared finite-word fold specializes to the unconditional affine one-loop formula `2 + tau`; the
singleton fold's unit-denominator preparation is used only to compare with the legacy division-shaped output. -/
@[expose] def standardOne_fold_formula (tau : CoherentNamed)
    (preparations : Fold.Basic.FoldPreparations tau Curves.Legendre.FractionalWords.Standard.standardOneMatrices) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction tau Curves.Legendre.FractionalWords.Standard.standardOneMatrices preparations).name
      (oneAffineTransform tau).name := by
  change Gaussian.Equivalence.NamedEquivalent (oneTransform preparations.1).name
    (oneAffineTransform tau).name
  exact oneTransform_equivalent_affine preparations.1

/-- The generic prepared finite-word fold specializes to the standard infinity quotient `(-2 + tau) / (-3 + 2*tau)`. -/
@[expose] def standardInfinity_fold_formula (tau : CoherentNamed)
    (preparations : Fold.Basic.FoldPreparations tau Curves.Legendre.FractionalWords.Standard.standardInfinityMatrices) :
    Gaussian.Equivalence.NamedEquivalent
      (Fold.Basic.foldAction tau Curves.Legendre.FractionalWords.Standard.standardInfinityMatrices preparations).name
      (infinityTransform preparations.1).name :=
  NamedEquivalent.refl _

/-- The traversal-order matrix word for the standard zero, one and infinity loops. -/
@[expose] def standardProductMatrices : List IntegralMatrix :=
  [Monodromy.zeroMatrix,
    Monodromy.oneMatrix,
    Monodromy.infinityMatrix]

/-- The traversal-order standard product folds to `infinity * (one * zero)`, hence exactly the identity. -/
theorem standardProductMatrices_eq_identity :
    Word.matrixProduct Curves.Legendre.FractionalWords.Standard.standardProductMatrices =
      Multiplication.identity := by
  simp only [Curves.Legendre.FractionalWords.Standard.standardProductMatrices, Word.matrixProduct]
  rw [Multiplication.identity_mul_int,
    Multiplication.mul_assoc,
    Monodromy.explicit_loop_product_left]

/-- Every fully prepared stepwise execution of the standard product word returns the source ratio operationally. -/
@[expose] def standardProduct_fold_identity (tau : CoherentNamed)
    (preparations : Fold.Basic.FoldPreparations tau Curves.Legendre.FractionalWords.Standard.standardProductMatrices) :
    Gaussian.Equivalence.NamedEquivalent (Fold.Basic.foldAction tau
      Curves.Legendre.FractionalWords.Standard.standardProductMatrices preparations).name
      tau.name :=
  NamedEquivalent.trans
    (NamedEquivalent.symm
      (Comparison.productOutput_equivalent_foldAction
        Curves.Legendre.FractionalWords.Standard.standardProductMatrices tau preparations))
    (Identity.fractionalLinear_of_matrix_eq_identity
      (Word.matrixProduct Curves.Legendre.FractionalWords.Standard.standardProductMatrices) tau
      (FoldPreparations.combined Curves.Legendre.FractionalWords.Standard.standardProductMatrices preparations)
      Curves.Legendre.FractionalWords.Standard.standardProductMatrices_eq_identity)

end

end Purelib.Curves.Legendre.FractionalWords.Standard
