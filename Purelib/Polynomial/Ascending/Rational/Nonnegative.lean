module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.Composition
import Purelib.Polynomial.Ascending.Rational.Convolution
import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Nonnegative

/-! ## Finite coefficient majorants -/

/-- Every zero-extended rational coefficient of the finite polynomial is nonnegative. -/
def CoefficientsNonnegative (polynomial :
  CoefficientPolynomial) : Prop :=
  ∀ degree, 0 ≤ Ascending.Rational.Basic.coefficient polynomial degree

/-- A nonnegative rational constant gives a polynomial with nonnegative coefficients. -/
theorem coefficientsNonnegative_constant {value :
  Fraction.Rational}
    (nonnegative : 0 ≤ value) : CoefficientsNonnegative
      (Ascending.Rational.Basic.constant value) := by
  intro degree
  rw [Ascending.Rational.Coefficientwise.coefficient_constant]
  split
  · exact nonnegative
  · exact le_rfl

/-- Addition preserves nonnegative coefficients. -/
theorem coefficientsNonnegative_add {left right :
  CoefficientPolynomial}
    (leftNonnegative : CoefficientsNonnegative left)
    (rightNonnegative : CoefficientsNonnegative right) :
    CoefficientsNonnegative (Ascending.Rational.Basic.add left right) := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_add]
  exact add_nonneg (leftNonnegative degree) (rightNonnegative degree)

/-- Scaling by a nonnegative rational preserves nonnegative coefficients. -/
theorem coefficientsNonnegative_scale {factor :
  Fraction.Rational}
    (factorNonnegative : 0 ≤ factor) {polynomial : CoefficientPolynomial}
    (nonnegative : CoefficientsNonnegative polynomial) :
    CoefficientsNonnegative (Ascending.Rational.Basic.scale factor polynomial) := by
  intro degree
  rw [Ascending.Rational.Basic.coefficient_scale]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (nonnegative degree)

/-- The product of two polynomials with nonnegative coefficients has nonnegative coefficients.

Each coefficient is a finite sum of products of nonnegative rational entries. -/
theorem coefficientsNonnegative_mul {left right :
  CoefficientPolynomial}
    (leftNonnegative : CoefficientsNonnegative left)
    (rightNonnegative : CoefficientsNonnegative right) :
    CoefficientsNonnegative (Ascending.Rational.Basic.mul left right) := open
      Purelib.Algebra in by
  intro degree
  rw [Ascending.Rational.Convolution.coefficient_mul]
  exact FiniteSum.Prefix.coordinateSum_nonnegative _ (by
    intro index
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (leftNonnegative index) (rightNonnegative (degree - index))) _

/-- Every natural power of a polynomial with nonnegative coefficients retains that property. -/
theorem coefficientsNonnegative_pow {polynomial :
  CoefficientPolynomial}
    (nonnegative : CoefficientsNonnegative polynomial) : ∀ exponent,
    CoefficientsNonnegative (Ascending.Rational.Basic.pow polynomial exponent)
  | 0 => coefficientsNonnegative_constant (by decide)
  | exponent + 1 =>
      coefficientsNonnegative_mul
        (coefficientsNonnegative_pow nonnegative exponent) nonnegative

/-- A monomial with nonnegative value has nonnegative coefficients at all degrees. -/
theorem coefficientsNonnegative_monomial (degree : Nat)
    {value : Fraction.Rational} (nonnegative : 0 ≤ value) :
    CoefficientsNonnegative (Ascending.Rational.Monomial.monomial degree value) := by
  intro outputDegree
  rw [Ascending.Rational.Monomial.coefficient_monomial]
  split
  · exact nonnegative
  · exact le_rfl

/-- Substituting a nonnegative-coefficient polynomial into a nonnegative coefficient list preserves nonnegativity.

Horner recursion combines a nonnegative constant with a product of nonnegative-coefficient polynomials. -/
theorem coefficientsNonnegative_composeCoefficients
    {inner : CoefficientPolynomial} (innerNonnegative :
      CoefficientsNonnegative inner) :
    ∀ coefficients,
      (∀ degree, 0 ≤ Ascending.Rational.Basic.coefficientCoefficients coefficients degree) →
        CoefficientsNonnegative (Ascending.Rational.Composition.composeCoefficients
          coefficients inner)
  | [], outerNonnegative => fun degree => by
      change 0 ≤ 0
      exact le_rfl
  | coefficient :: remaining, outerNonnegative => by
      apply coefficientsNonnegative_add
      · exact coefficientsNonnegative_constant (outerNonnegative 0)
      · apply coefficientsNonnegative_mul innerNonnegative
        apply coefficientsNonnegative_composeCoefficients
          innerNonnegative
        intro degree
        exact outerNonnegative (degree + 1)

/-- Composition preserves nonnegative coefficients when both outer and inner polynomials have them. -/
theorem coefficientsNonnegative_compose {outer inner :
  CoefficientPolynomial}
    (outerNonnegative : CoefficientsNonnegative outer)
    (innerNonnegative : CoefficientsNonnegative inner) :
    CoefficientsNonnegative (Ascending.Rational.Composition.compose outer inner) :=
  coefficientsNonnegative_composeCoefficients innerNonnegative
    outer.coefficients outerNonnegative
end Purelib.Polynomial.Ascending.Rational.Nonnegative

end
