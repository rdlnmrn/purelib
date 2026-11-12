module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
public section

/-!
# Residual bounds for finite multiplicity bases

The exact multiplicity basis gives two complementary finite statements.
First, a sufficiently small residual of the original polynomial selects at
least one displayed squarefree basis factor with small residual.  Second, for
a preselected factor, an explicit positive lower bound on the remaining
unit/cofactor product transfers its residual bound back to the original
polynomial in an integer-power form.

No rational root, real exponent, root collection, or completed value occurs:
all powers are natural powers of displayed rational quadrances.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Cofactor

/-! ## A preselected factor and its explicit cofactor -/

/-- The remaining positive-factor value after exposing one selected entry in
a displayed list split. -/
@[expose] def cofactorValue (before after : List
  Basis.Positive.PositiveEntry)
    (point : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Basis.Positive.positiveValue before point *
    Basis.Positive.positiveValue after point

/-- A displayed list split factors the weighted value into the focused power and the remaining product. -/
theorem positiveValue_split
    (before after : List Basis.Positive.PositiveEntry) (entry :
      Basis.Positive.PositiveEntry)
    (point : Gaussian.Basic.Canonical) :
    Basis.Positive.positiveValue (before ++ entry :: after) point =
      entry.part.polynomial.eval point ^ entry.multiplicity *
        cofactorValue before after point := by
  induction before with
  | nil =>
      simp only [List.nil_append, Basis.Positive.positiveValue,
        cofactorValue]
      rw [Gaussian.Basic.one_mul]
  | cons head before inductionHypothesis =>
      simp only [List.cons_append, Basis.Positive.positiveValue]
      rw [inductionHypothesis]
      dsimp only [cofactorValue]
      rw [Basis.Positive.positiveValue]
      ring1

set_option genInjectivity false in
/-- Explicit positive lower certificate for the omitted unit and all other
factor values at one displayed sample. -/
structure CofactorLower
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Squarefree.Decomposition p)
    (before after : List Basis.Positive.PositiveEntry) (point : Gaussian.Basic.Canonical)
      where
  /-- The retained rational lower bound for the omitted unit and cofactor quadrance. -/ bound : Fraction.Rational
  /-- The retained lower bound is strictly positive. -/ positive : 0 < bound
  /-- The bound lies below the exact unit quadrance times the cofactor squared norm. -/ lower : bound ≤
    Basic.unitQuadrance decomposition *
    Gaussian.Norm.Basic.normSq (cofactorValue before after point)

constructive_injectivity CofactorLower

/-- Exact norm factorization at a displayed selected multiplicity entry. -/
theorem selected_residual_identity
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Squarefree.Decomposition p)
    (before after : List Basis.Positive.PositiveEntry) (entry :
      Basis.Positive.PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian.Basic.Canonical) :
    Gaussian.Norm.Basic.normSq (p.eval point) =
      (Basic.unitQuadrance decomposition *
        Gaussian.Norm.Basic.normSq (cofactorValue before after
          point)) *
      Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) ^ entry.multiplicity := by
  rw [Basic.residual_product_identity decomposition point, split,
    positiveValue_split, Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow]
  ring1

/-- A cofactor lower bound transfers the selected factor's integer-power
residual to the original residual without extracting an `m`-th root. -/
theorem
  cofactor_mul_factorResidualPow_le_sourceResidual
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Squarefree.Decomposition p)
    (before after : List Basis.Positive.PositiveEntry) (entry :
      Basis.Positive.PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian.Basic.Canonical)
    (cofactor : CofactorLower decomposition before after point) :
    cofactor.bound *
        Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) ^ entry.multiplicity ≤
      Gaussian.Norm.Basic.normSq (p.eval point) := by
  rw [selected_residual_identity decomposition before after entry split
    point]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    cofactor.lower
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Gaussian.Norm.Basic.normSq_nonneg (entry.part.polynomial.eval point)) entry.multiplicity)
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Cofactor

end
