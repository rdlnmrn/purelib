module

-- Retain the original public coefficient type aliases and scalar field owner.
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic

/-!
# Rational coordinate monomials

The coordinate polynomial retains the original coefficient table `[1, 0]`.
Finite Horner evaluation reads its argument, while its nonzero leading one
retains both coefficient slots under normalization.
-/

namespace Purelib.Polynomial.Dense.Rational.Monomial.Coordinate

open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- Retain the rational coordinate polynomial with coefficient table `[1, 0]`.

The monic leading coefficient and explicit zero constant slot remain in the
original descending representation without an intermediate normalization. -/
@[expose] public def coordinateVariable : DensePolynomial Fraction.Rational := ⟨[1, 0]⟩

/-- The retained coordinate table evaluates to its supplied argument.

The two original Horner steps multiply the leading one by that argument and
add the zero constant slot. -/
public theorem coordinateVariable_eval (t : Fraction.Rational) :
    coordinateVariable.eval t = t := by
  change (0 * t + 1) * t + 0 = t
  rewrite [MulZeroClass.zero_mul, _root_.zero_add, _root_.one_mul, _root_.add_zero]
  exact Eq.refl _

/-- The rational coordinate polynomial always fails the Boolean zero test.

Its leading rational one is nonzero, so normalization retains the complete
original two-slot table. -/
public theorem coordinateVariable_isZero_false :
    (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).isZero = false := by
  change (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).normalize.coeffs.isEmpty = false
  rewrite [DensePolynomial.normalize_linear_of_leading_ne_zero
    (Ne.symm Fraction.Field.zero_ne_one)]
  exact Eq.refl _

/-- The rational coordinate polynomial has two normalized coefficient slots.

The nonzero leading coefficient retains the explicit zero constant slot,
which remains part of its original descending representation. -/
public theorem coordinateVariable_degreeCount :
    (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).degreeCount = 2 := by
  change (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).normalize.coeffs.length = 2
  rewrite [DensePolynomial.normalize_linear_of_leading_ne_zero
    (Ne.symm Fraction.Field.zero_ne_one)]
  exact Eq.refl _

/-- The rational coordinate polynomial has natural degree one.

The natural degree convention subtracts one from the two retained normalized
coefficient slots of the monic coordinate table. -/
public theorem coordinateVariable_natDegree :
    (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).natDegree = 1 := by
  change (⟨[1, 0]⟩ : DensePolynomial Fraction.Rational).degreeCount - 1 = 1
  rewrite [coordinateVariable_degreeCount]
  exact Eq.refl _

end Purelib.Polynomial.Dense.Rational.Monomial.Coordinate
