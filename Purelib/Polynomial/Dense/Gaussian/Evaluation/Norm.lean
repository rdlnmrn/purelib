module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Power
public import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm

/-! ## Finite monomial lists -/

/-- The displayed monomials of one high-to-low coefficient list. -/
def monomialTerms : List Gaussian.Basic.Canonical →
  Gaussian.Basic.Canonical → List Gaussian.Basic.Canonical
  | [], _ => []
  | coefficient :: coefficients, z =>
      coefficient * z ^ coefficients.length :: monomialTerms
        coefficients z

/-- Monomial expansion preserves the number of displayed coefficients. -/
@[simp] theorem monomialTerms_length (coefficients : List
  Gaussian.Basic.Canonical)
    (z : Gaussian.Basic.Canonical) :
    (monomialTerms coefficients z).length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      rw [monomialTerms, List.length_cons, inductionHypothesis,
        List.length_cons]

/-- Structural monomial expansion of the finite Horner program. -/
theorem gaussianSum_monomialTerms :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (z : Gaussian.Basic.Canonical),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (monomialTerms coefficients z) =
        DensePolynomial.evalCoeffs z coefficients
  | [], _ => rfl
  | coefficient :: coefficients, z => by
      rw [monomialTerms, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        gaussianSum_monomialTerms coefficients z,
        DensePolynomial.evalCoeffs_cons_expansion]

/-- Sum of the squared norms of the displayed monomials. -/
def monomialNormSqSum : List Gaussian.Basic.Canonical →
  Fraction.Rational → Fraction.Rational
  | [], _ => 0
  | coefficient :: coefficients, radiusSq =>
      Data.Gaussian.Norm.Basic.normSq coefficient * radiusSq ^ coefficients.length +
        monomialNormSqSum coefficients radiusSq

/-- The sum of monomial quadrances equals the coefficient norm sum at the input quadrance. -/
theorem gaussianNormSqSum_monomialTerms :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (z : Gaussian.Basic.Canonical),
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum (monomialTerms coefficients z) =
        monomialNormSqSum coefficients (Data.Gaussian.Norm.Basic.normSq z)
  | [], _ => rfl
  | coefficient :: coefficients, z => by
      rw [monomialTerms, Gaussian.Norm.Sum.Basic.gaussianNormSqSum,
        gaussianNormSqSum_monomialTerms coefficients z,
        monomialNormSqSum, ← Gaussian.Norm.Basic.normSq_eq_canonical,
          Gaussian.Norm.Basic.normSq_mul, Purelib.Data.Gaussian.Power.normSq_pow]

/-- Cauchy--Schwarz specialized to the finite Horner monomial expansion. -/
theorem normSq_evalCoeffs_le (coefficients : List
  Gaussian.Basic.Canonical) (z : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (DensePolynomial.evalCoeffs z coefficients) ≤
      (coefficients.length : Fraction.Rational) *
        monomialNormSqSum coefficients (Data.Gaussian.Norm.Basic.normSq z) := by
  rw [← gaussianSum_monomialTerms coefficients z,
    ← gaussianNormSqSum_monomialTerms coefficients z,
    ← monomialTerms_length coefficients z]
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
    Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (monomialTerms coefficients z)

end Purelib.Polynomial.Dense.Gaussian.Evaluation.Norm

end
