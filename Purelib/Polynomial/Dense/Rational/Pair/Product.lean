module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field

/-!
# Dense rational coordinate products

Finite polynomial multiplication combines two retained coordinate pairs.
Their real and imaginary coordinates use the original scalar product order.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Product

open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-- Construct the real coordinate of the product of two rational polynomial pairs.

The retained coordinate polynomials form the difference of their two diagonal
products. All multiplication and subtraction use the original dense operations. -/
@[expose] public def productReal (A B C D : CoordinatePolynomial) : DensePolynomial Fraction.Rational :=
  A * C - B * D

/-- Construct the imaginary coordinate of the product of two rational polynomial pairs.

The retained coordinate polynomials form the sum of the two cross products,
with the original operand order in each dense multiplication. -/
@[expose] public def productImag (A B C D : CoordinatePolynomial) : DensePolynomial Fraction.Rational :=
  A * D + B * C

/-- The real product coordinate evaluates to the difference of the diagonal products.

The finite dense evaluation laws transport both retained polynomial products
and their subtraction at the supplied rational parameter. -/
@[simp] public theorem eval_productReal (A B C D : CoordinatePolynomial)
    (t : Fraction.Rational) :
    (productReal A B C D).eval t = A.eval t * C.eval t - B.eval t * D.eval t := by
  unfold productReal
  rw [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul]

/-- The imaginary product coordinate evaluates to the sum of the cross products.

The same finite dense evaluation laws transport both retained cross products
and their addition at the supplied rational parameter. -/
@[simp] public theorem eval_productImag (A B C D : CoordinatePolynomial)
    (t : Fraction.Rational) :
    (productImag A B C D).eval t = A.eval t * D.eval t + B.eval t * C.eval t := by
  unfold productImag
  rw [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_mul]

end Purelib.Polynomial.Dense.Rational.Pair.Product
