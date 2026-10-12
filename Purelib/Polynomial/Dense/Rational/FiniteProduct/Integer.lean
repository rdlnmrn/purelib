module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Integer
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.Divisibility
public import Purelib.Polynomial.Dense.Rational.FiniteProduct
public import Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Monic integer coefficients for the finite cyclotomic construction

The rational long-division factors constructed in `Cyclotomic` are
shown here to be monic and to carry executable ascending integer coefficient
lists.  The proof is a second primitive recursion over the already verified
factorization; it uses the finite monic-division theorem rather than a UFD or
root factorization.
-/

namespace Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer

open Purelib.Polynomial.Dense.Basic.DensePolynomial

namespace IntegerBridge

/-- The rational constant-one polynomial has leading coefficient one. -/
theorem leadingCoeff_constant_one :
    (DensePolynomial.constant (1 : Fraction.Rational)).leadingCoeff = 1 := by
  unfold DensePolynomial.leadingCoeff
  rw [DensePolynomial.normalize_constant_of_ne
    Fraction.Field.zero_ne_one.symm]
  rfl

/-- A finite product of nonzero monic rational polynomials is monic. -/
theorem leadingCoeff_productFin_one : ∀
  (count : Nat)
    (factor : Fin count → Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial),
    (∀ index, (factor index).isZero = false) →
    (∀ index, (factor index).leadingCoeff = 1) →
    (Dense.Rational.FiniteProduct.productFin count factor).leadingCoeff = 1
  | 0, factor, allNonzero, allMonic => leadingCoeff_constant_one
  | count + 1, factor, allNonzero, allMonic => by
      rw [Dense.Rational.FiniteProduct.productFin_succ,
        DensePolynomial.leadingCoeff_mul
          (Dense.Rational.FiniteProduct.productFin_nonzero count (fun index => factor index.castSucc)
            (fun index => allNonzero index.castSucc))
          (allNonzero (Fin.last count)),
        leadingCoeff_productFin_one count
          (fun index => factor index.castSucc)
          (fun index => allNonzero index.castSucc)
          (fun index => allMonic index.castSucc),
        allMonic (Fin.last count), one_mul]

/-- A finite product of rational polynomials with integral coefficients again has integral coefficients. -/
theorem integral_productFin : ∀ (count :
  Nat)
    (factor : Fin count → Polynomial.Dense.Rational.Divisibility.CoefficientPolynomial),
    (∀ index, Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (factor index)) →
    Dense.Rational.IntegerCoefficients.Basic.IsIntegralPolynomial (Dense.Rational.FiniteProduct.productFin count factor)
  | 0, factor, allIntegral => by
      exact Dense.Rational.IntegerCoefficients.Basic.integral_constant
        (Purelib.Data.Rat.Fraction.Integer.integral_of_integer 1)
  | count + 1, factor, allIntegral => by
      rw [Dense.Rational.FiniteProduct.productFin_succ]
      exact Dense.Rational.IntegerCoefficients.Basic.integral_mul
        (integral_productFin count (fun index =>
          factor index.castSucc)
          (fun index => allIntegral index.castSucc))
        (allIntegral (Fin.last count))
end IntegerBridge

/-- Product of a `Fin`-indexed family of ascending integer polynomials. -/
def coefficientProductFin : (count : Nat) →
    (Fin count → List Int) → List Int
  | 0, _ => [1]
  | count + 1, factor =>
      Ascending.Integer.Basic.Certificate.mul
        (coefficientProductFin count
          (fun index => factor index.castSucc))
        (factor (Fin.last count))

/-- The empty ascending-integer polynomial product is `[1]`. -/
@[simp] theorem coefficientProductFin_zero (factor : Fin
  0 → List Int) :
    coefficientProductFin 0 factor = [1] := rfl

/-- Compute a finite coefficient product by appending the last indexed factor. -/
@[simp] theorem coefficientProductFin_succ
    (factor : Fin (count + 1) → List Int) :
    coefficientProductFin (count + 1) factor =
      Ascending.Integer.Basic.Certificate.mul
        (coefficientProductFin count
          (fun index => factor index.castSucc))
        (factor (Fin.last count)) := rfl

/-- Converting the finite integer coefficient product gives the rational polynomial product.

The identity preserves the original `Fin` indexing and exact ascending coefficient multiplication. -/
theorem ofAscending_coefficientProductFin : ∀ (count :
  Nat)
    (factor : Fin count → List Int),
    Dense.Rational.AscendingInteger.Basic.ofAscending
        (coefficientProductFin count factor) =
      Dense.Rational.FiniteProduct.productFin count (fun index =>
        Dense.Rational.AscendingInteger.Basic.ofAscending
          (factor index))
  | 0, factor => Dense.Rational.AscendingInteger.Basic.ofAscending_one
  | count + 1, factor => by
      rw [coefficientProductFin_succ,
        Dense.Rational.AscendingInteger.Basic.ofAscending_mul,
        ofAscending_coefficientProductFin count
          (fun index => factor index.castSucc), Dense.Rational.FiniteProduct.productFin_succ]
end Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer

end
