module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Guard

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

/-- Multiply the six coordinate polynomials in their displayed order.

The five dense multiplications retain their original left-associated
order and all six coordinate polynomial factors. Nonzero evaluations
at the supplied parameter certify their actual scalar components. -/
@[expose] public def productEventGuard
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  ((((A * B) * C) * D) * E) * H

/-- The product guard is nonzero when all six coordinate polynomials are nonzero.

Each original coordinate has a false structural zero test. The
retained dense multiplication nonzero certificate propagates those
six conditions through the same five original product operations. -/
public theorem productEventGuard_isZero_false
    {A B C D E H : Dense.Rational.Basic.CoordinatePolynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false) :
    (productEventGuard A B C D E H).isZero = false := by
  unfold productEventGuard
  exact Dense.Basic.DensePolynomial.isZero_mul_eq_false
    (Dense.Basic.DensePolynomial.isZero_mul_eq_false
      (Dense.Basic.DensePolynomial.isZero_mul_eq_false
        (Dense.Basic.DensePolynomial.isZero_mul_eq_false
          (Dense.Basic.DensePolynomial.isZero_mul_eq_false A_nonzero B_nonzero) C_nonzero)
        D_nonzero)
      E_nonzero)
    H_nonzero

/-- A nonzero guard value implies all six coordinate values are nonzero at that point.

Evaluation of the original left-associated dense product is the
same scalar product. A zero value of any retained factor would make
that exact product zero, contradicting the supplied guard condition. -/
public theorem productEventGuard_eval_ne_zero_components
    (A B C D E H : Dense.Rational.Basic.CoordinatePolynomial) (x : Fraction.Rational)
    (guardNonzero : (productEventGuard A B C D E H).eval x ≠ 0) :
    A.eval x ≠ 0 ∧ B.eval x ≠ 0 ∧
      C.eval x ≠ 0 ∧ D.eval x ≠ 0 ∧
      E.eval x ≠ 0 ∧ H.eval x ≠ 0 := by
  have evaluated : (productEventGuard A B C D E H).eval x =
      ((((A.eval x * B.eval x) * C.eval x) * D.eval x) * E.eval x) * H.eval x := by
    unfold productEventGuard
    rw [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_mul,
      Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_mul,
      Dense.Basic.DensePolynomial.eval_mul]
  have productNonzero :
      ((((A.eval x * B.eval x) * C.eval x) * D.eval x) * E.eval x) * H.eval x ≠ 0 := by
    intro zero
    exact guardNonzero (evaluated.trans zero)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct]
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.mul_zero_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct]
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.mul_zero_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct]
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.mul_zero_direct, Fraction.Field.zero_mul_direct,
      Fraction.Field.zero_mul_direct]
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.mul_zero_direct, Fraction.Field.zero_mul_direct]
  · intro zero
    apply productNonzero
    rw [zero, Fraction.Field.mul_zero_direct]

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Guard
