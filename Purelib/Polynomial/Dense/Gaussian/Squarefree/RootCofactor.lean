module

public import Purelib.Polynomial.Dense.Gaussian.Division
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Bool.Decide
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-! # The retained nonvanishing cofactor at a displayed squarefree root -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Linear.Translated

set_option genInjectivity false in
/-- Original division by a displayed root's linear factor, retaining its nonvanishing squarefree complement.

The complete original division result owns the quotient, remainder and actual
step count. Both exact factorization and the complement's point value refer to
that same result; squarefreeness proves that the point value is nonzero.
-/
structure RootCofactor (polynomial : CoefficientPolynomial) (point : Canonical) where
  /-- The retained original finite division by the same displayed linear factor. -/
  result : DensePolynomial.DivResult polynomial (translatedCoordinate point)
  /-- The retained result is the original executable division on those ordered inputs. -/
  result_eq : result = polynomial.divMod (translatedCoordinate point)
  /-- The original remainder is identically zero. -/
  remainderZero : result.remainder.isZero = true
  /-- The original polynomial factors through this displayed linear factor and the same retained quotient. -/
  factorization : Factorization.Identity.ProductIdentity polynomial (translatedCoordinate point) result.quotient
  /-- The same original quotient has a nonzero coefficient table. -/
  quotientNonzero : result.quotient.isZero = false
  /-- The original linear factor and same retained quotient are coprime. -/
  coprime : Coprime.Basic.CoprimeCertificate (translatedCoordinate point) result.quotient
  /-- The actual cached quotient evaluation at this same displayed root. -/
  value : Canonical
  /-- The cached reading comes from the same original quotient and point. -/
  value_eq : result.quotient.eval point = value
  /-- The squarefree complement does not vanish at the same original point. -/
  valueNonzero : value ≠ 0

constructive_injectivity RootCofactor

namespace RootCofactor

/-- Divide by a displayed squarefree root once and retain the original exact quotient and its nonzero point value.

The degree-one divisor forces the normalized remainder to be constant.
Evaluating the original division identity at the supplied root makes that
constant zero. Squarefree-factor coprimality then proves the same retained
quotient's displayed point value nonzero.
-/
@[expose] def ofRoot (polynomial : CoefficientPolynomial) (point : Canonical)
    (nonzero : polynomial.isZero = false) (squarefree : Basic.SquarefreeCertificate polynomial)
    (root : polynomial.eval point = 0) : RootCofactor polynomial point := by
  let linear := translatedCoordinate point
  have linearNonzero : linear.isZero = false := Squarefree.translatedCoordinate_nonzero point
  have linearZero : linear.eval point = 0 := by
    rewrite [translatedCoordinate_eval, Purelib.Data.Gaussian.Basic.sub_self]
    rfl
  let result := polynomial.divMod linear
  have remainderAtPoint : result.remainder.eval point = 0 := by
    have identity := DensePolynomial.divMod_eval_equation polynomial linear point
    rewrite [linearZero, Purelib.Data.Gaussian.Basic.zero_mul, Purelib.Data.Gaussian.Basic.add_zero, root] at identity
    exact identity
  have count : linear.degreeCount = 2 := by
    change (⟨[1, -point]⟩ : CoefficientPolynomial).normalize.coeffs.length = 2
    rewrite [DensePolynomial.normalize_linear_of_leading_ne_zero (by decide +kernel : (1 : Canonical) ≠ 0)]
    rfl
  have smaller : result.remainder.degreeCount < 2 := by
    have bound := DensePolynomial.divMod_remainder_degreeCount_lt polynomial linear linearNonzero
    rewrite [count] at bound
    exact bound
  have remainderZero : result.remainder.isZero = true := by
    cases selected : result.remainder.isZero with
    | true => rfl
    | false =>
        have balance := DensePolynomial.natDegree_add_one_eq_degreeCount selected
        have degree : result.remainder.natDegree = 0 := by omega0
        have normalized := DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero selected degree
        have same : result.remainder.eval point = result.remainder.leadingCoeff := by
          rewrite [← DensePolynomial.eval_normalize result.remainder point, normalized, DensePolynomial.eval_constant]
          rfl
        exact ((DensePolynomial.leadingCoeff_ne_zero selected) (same.symm.trans remainderAtPoint)).elim
  have identity : ∀ value, polynomial.eval value = linear.eval value * result.quotient.eval value := by
    intro value
    have original := DensePolynomial.divMod_eval_equation polynomial linear value
    rewrite [DensePolynomial.eval_eq_zero_of_isZero remainderZero, Purelib.Data.Gaussian.Basic.zero_add] at original
    exact original.symm
  let factorization := Factorization.Identity.factorizationOfCandidateEvals polynomial linear result.quotient
    (fun value _ => identity value)
  have normalizedFactorization : Factorization.Identity.ProductIdentity polynomial.normalize linear result.quotient :=
    Factorization.Identity.factorizationOfCandidateEvals polynomial.normalize linear result.quotient
      (fun value _ => (DensePolynomial.eval_normalize polynomial value).trans (identity value))
  have quotientNonzero := Factorization.Identity.right_isZero_false
    ((DensePolynomial.isZero_normalize polynomial).trans nonzero)
    (DensePolynomial.normalize_normalize polynomial) normalizedFactorization
  let coprime := Coprime.Factors.factorsCoprime squarefree linearNonzero factorization
  let value := result.quotient.eval point
  have valueNonzero : value ≠ 0 := by
    rcases coprime.eval_ne_zero point with left | right
    · exact (left linearZero).elim
    · exact right
  exact ⟨result, rfl, remainderZero, factorization, quotientNonzero, coprime, value, rfl, valueNonzero⟩

end RootCofactor

end Purelib.Polynomial.Dense.Gaussian.Squarefree

end
