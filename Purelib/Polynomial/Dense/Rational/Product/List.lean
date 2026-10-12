module
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
public import Mathlib.Data.List.Basic

/-!
# Products of rational coefficient polynomials

The original list recursion multiplies the retained polynomials in occurrence
order. Evaluation and nonzero membership certificates use the same finite list
and coefficient operations.
-/

namespace Purelib.Polynomial.Dense.Rational.Product.List

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

public section

/-- Multiply a finite list of rational coefficient polynomials in occurrence order.

The empty list returns the unit polynomial. Each retained head multiplies the
product of its original tail using the same dense polynomial multiplication,
so repeated occurrences remain separate factors. -/
@[expose] def polynomialProduct : List Dense.Rational.Basic.CoordinatePolynomial →
  Dense.Rational.Basic.CoordinatePolynomial
  | [] => Dense.Basic.DensePolynomial.constant 1
  | p :: polynomials => p * Purelib.Polynomial.Dense.Rational.Product.List.polynomialProduct polynomials

/-- Evaluation of the polynomial-list product equals the product of the evaluated list.

The empty list retains the unit polynomial and each retained head multiplies
the original tail product. Scalar multiplicative evaluation proves the same
ordered recurrence for the displayed evaluated list. -/
@[simp] theorem eval_polynomialProduct
    (polynomials : List Dense.Rational.Basic.CoordinatePolynomial) (parameter : Fraction.Rational) :
    (Dense.Rational.Product.List.polynomialProduct polynomials).eval parameter =
      (polynomials.map fun p => p.eval parameter).prod := by
  induction polynomials with
  | nil =>
      change (Dense.Basic.DensePolynomial.constant 1).eval parameter = 1
      rewrite [Dense.Basic.DensePolynomial.eval_constant]
      exact Eq.refl _
  | cons p polynomials inductionHypothesis =>
      change (p * Dense.Rational.Product.List.polynomialProduct polynomials).eval parameter =
        (p.eval parameter :: polynomials.map (fun polynomial => polynomial.eval parameter)).prod
      rewrite [Dense.Basic.DensePolynomial.eval_mul, List.prod_cons, inductionHypothesis]
      exact Eq.refl _

/-- A finite list of nonzero rational polynomials has nonzero polynomial product.

Every original factor has a represented false zero test. The unit polynomial
handles the empty list, and the retained multiplication certificate propagates
nonzero representation through each original head and tail. -/
theorem polynomialProduct_isZero_false
    {polynomials : List Dense.Rational.Basic.CoordinatePolynomial}
    (allNonzero : ∀ polynomial ∈ polynomials, polynomial.isZero = false) :
    (Dense.Rational.Product.List.polynomialProduct polynomials).isZero = false := by
  induction polynomials with
  | nil =>
      change (Dense.Basic.DensePolynomial.constant (1 : Fraction.Rational)).isZero = false
      change ([1].dropWhile (fun value : Fraction.Rational => value = 0)).isEmpty =
        false
      have retained : decide ((1 : Fraction.Rational) = 0) = false := by decide
      rewrite [Data.List.DropWhile.cons_of_false
        (fun value : Fraction.Rational => decide (value = 0)) 1 [] retained]
      exact Eq.refl _
  | cons p polynomials inductionHypothesis =>
      rewrite [Dense.Rational.Product.List.polynomialProduct]
      exact Dense.Basic.DensePolynomial.isZero_mul_eq_false
        (allNonzero p (List.Mem.head polynomials))
        (inductionHypothesis (fun polynomial member =>
          allNonzero polynomial (List.Mem.tail p member)))

/-- A nonzero value of the list product forces each displayed factor value to be nonzero.

An alleged zero factor value makes the original product value zero. Structural
membership retains the exact head or tail occurrence, so the negative product
certificate excludes that factor value. -/
theorem eval_ne_zero_of_mem_of_polynomialProduct
    {polynomials : List Dense.Rational.Basic.CoordinatePolynomial} {p : Dense.Rational.Basic.CoordinatePolynomial}
    {parameter : Fraction.Rational} (member : p ∈ polynomials)
    (productNonzero : (Dense.Rational.Product.List.polynomialProduct polynomials).eval parameter ≠ 0) :
    p.eval parameter ≠ 0 := by
  induction polynomials with
  | nil => nomatch member
  | cons head tail inductionHypothesis =>
      rw [Dense.Rational.Product.List.polynomialProduct, Dense.Basic.DensePolynomial.eval_mul] at productNonzero
      have headNonzero : head.eval parameter ≠ 0 := by
        intro headZero
        apply productNonzero
        rw [headZero, Fraction.Field.zero_mul_direct]
      have tailNonzero : (Dense.Rational.Product.List.polynomialProduct tail).eval parameter ≠ 0 := by
        intro tailZero
        apply productNonzero
        rw [tailZero, Fraction.Field.mul_zero_direct]
      cases member with
      | head => exact headNonzero
      | tail _ tailMember => exact inductionHypothesis tailMember tailNonzero
end

end Purelib.Polynomial.Dense.Rational.Product.List
