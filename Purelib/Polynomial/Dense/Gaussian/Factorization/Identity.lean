module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
import Purelib.Data.Bool.Decide
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Finite displayed factorization identities

An exactly zero coefficient difference certifies the retained product of two
dense Gaussian polynomials. Checking the original bounded candidate list
establishes that coefficient identity; scalar evaluation and leading-term
certificates retain its pointwise and degree consequences.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Factorization.Identity

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Leading
open _root_.Purelib.Polynomial.Dense.Leading renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian.Basic
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Bool

/-- A retained target differs from its two-factor product by zero coefficients.

The executable zero test reads the normalized finite coefficient difference
of the original target and the same ordered product. -/
public abbrev ProductIdentity (p left right : Basic.CanonicalCoefficients.CoefficientPolynomial) : Prop :=
  (p - left * right).isZero = true

/-- The original product candidate evaluations certify its coefficient identity.

Every displayed point comes from the candidate list of the same target-minus-
product difference. Its finite root-count certificate then gives zero coefficients. -/
public theorem factorizationOfCandidateEvals
    (p left right : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (identity : ∀ point ∈
      NonzeroEvaluation.candidates (p - left * right),
      p.eval point = left.eval point * right.eval point) :
    ProductIdentity p left right := by
  apply NonzeroEvaluation.difference_isZero_of_candidate_evals
  intro point member
  rw [DensePolynomial.eval_mul]
  exact identity point member

/-- A nonzero normalized target forces its displayed right factor to be nonzero.

A zero right factor makes the same product zero and reduces the retained
coefficient difference to the target, contradicting its nonzero zero-test value. -/
public theorem right_isZero_false
    {p left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (factorization : ProductIdentity p left right) :
    right.isZero = false := by
  by_cases rightZero : right.isZero = true
  · have productZero : left * right = (0 : Basic.CanonicalCoefficients.CoefficientPolynomial) :=
      DensePolynomial.mul_eq_zero_of_isZero_right rightZero
    change (p - left * right).isZero = true at factorization
    rw [productZero] at factorization
    have targetZero : p.isZero = true := by
      change (p + -(0 : Basic.CanonicalCoefficients.CoefficientPolynomial)).isZero = true at factorization
      have negZero : -(0 : Basic.CanonicalCoefficients.CoefficientPolynomial) = 0 := rfl
      rw [negZero, DensePolynomial.add_zero_normalize, pNormalized] at factorization
      exact factorization
    rw [pNonzero] at targetZero
    exact Bool.noConfusion targetZero
  · exact Decide.bool_eq_false_of_not_eq_true _ rightZero

/-- The retained nonzero factors have natural degrees summing to the target degree.

The zero coefficient difference identifies the target and product leading
degrees. The original multiplication count certificate supplies their sum. -/
public theorem factor_natDegree_add
    {p left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (leftNonzero : left.isZero = false) (rightNonzero : right.isZero = false)
    (factorization : ProductIdentity p left right) :
    left.natDegree + right.natDegree = p.natDegree := by
  have productNonzero := DensePolynomial.isZero_mul_eq_false leftNonzero rightNonzero
  have degree := LeadingTerm.natDegree_eq_of_sub_isZero pNonzero
    productNonzero pNormalized (DensePolynomial.normalize_mul left right) factorization
  rw [DensePolynomial.natDegree_mul leftNonzero rightNonzero] at degree
  exact degree.symm

/-- A zero coefficient difference gives the corresponding scalar product identity.

Evaluate the original difference at the supplied point, then cancel that zero
scalar difference directly. The same ordered factors supply the product value. -/
public theorem eval_factorization
    {p left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (factorization : ProductIdentity p left right) (point : Canonical) :
    p.eval point = left.eval point * right.eval point := by
  have differenceZero := DensePolynomial.eval_eq_zero_of_isZero factorization point
  rewrite [DensePolynomial.eval_sub] at differenceZero
  calc
    p.eval point =
        (p.eval point - (left * right).eval point) + (left * right).eval point := by ring0
    _ = 0 + (left * right).eval point :=
      congrArg (fun value => value + (left * right).eval point) differenceZero
    _ = (left * right).eval point := zero_add _
    _ = left.eval point * right.eval point := DensePolynomial.eval_mul left right point

/-- A zero coefficient difference identifies the retained derivative evaluations.

The finite derivative difference certificate is specialized at the original
supplied Gaussian point, using the same target and ordered product. -/
public theorem eval_derivative_factorization
    {p left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (factorization : ProductIdentity p left right) (point : Canonical) :
    (GCD.derivative p).eval point =
      (GCD.derivative (left * right)).eval point :=
  Derivative.eval_derivative_eq_of_sub_isZero
    factorization point

/-- Swapping the displayed factors preserves their coefficient product identity.

Commuting scalar evaluation certifies each original candidate of the target
minus the swapped product. The finite candidate certificate gives its zero difference. -/
public theorem factorization_swap
    {p left right : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (factorization : ProductIdentity p left right) :
    ProductIdentity p right left := by
  apply factorizationOfCandidateEvals
  intro point _
  rw [eval_factorization factorization point]
  exact Purelib.Data.Gaussian.Basic.mul_comm _ _
end Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
