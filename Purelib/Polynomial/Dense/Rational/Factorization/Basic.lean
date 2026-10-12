module
import Purelib.Data.Bool.Decide

import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Grid.Interior
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Roots.FiniteBound
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

public section

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Data.Bool

/-- Exact finite coefficient factorization. -/
abbrev Factorization (p left right : BoundaryFactorization.CoefficientPolynomial) : Prop :=
  (p - left * right).isZero = true

namespace Factorization

/-- A pointwise identity need only be checked on one explicit finite list
longer than the represented difference polynomial. -/
theorem factorizationOfEvals
    (p left right : BoundaryFactorization.CoefficientPolynomial)
    (identity : ∀ point : Fraction.Rational,
      p.eval point = left.eval point * right.eval point) :
    Factorization p left right := open Purelib in by
  let difference := p - left * right
  let points := Approximation.Rational.Grid.Interior.interiorCandidates
    (0 : Fraction.Rational) 1 difference.degreeCount
  by_cases zero : difference.isZero = true
  · exact zero
  · have nonzero : difference.isZero = false := Decide.bool_eq_false_of_not_eq_true difference.isZero zero
    have allZero : ∀ point ∈ points, difference.eval point = 0 := by
      intro point _member
      dsimp only [difference]
      rw [Dense.Basic.DensePolynomial.eval_sub, Dense.Basic.DensePolynomial.eval_mul, identity point]
      ring1
    have tooMany :=
      Dense.Rational.Roots.FiniteBound.nodup_zeros_length_lt_degreeCount
        difference nonzero points
        (Approximation.Rational.Grid.Interior.interiorCandidates_nodup
          (show (0 : Fraction.Rational) < 1 by decide) difference.degreeCount)
        allZero
    have pointCount : points.length = difference.degreeCount + 1 := by
      exact Approximation.Rational.Grid.Interior.interiorCandidates_length
        0 1 difference.degreeCount
    rw [pointCount] at tooMany
    exact (Nat.not_lt_of_ge (Nat.le_succ difference.degreeCount) tooMany).elim

end Factorization

namespace Factorization

/-- A zero tested coefficient difference yields the displayed factorization of polynomial values. -/
theorem eval_factorization
    {p left right : BoundaryFactorization.CoefficientPolynomial}
    (factorization : Factorization p left right) (point : Fraction.Rational) :
    p.eval point = left.eval point * right.eval point := by
  have differenceZero := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero factorization point
  rw [Dense.Basic.DensePolynomial.eval_sub, Dense.Basic.DensePolynomial.eval_mul] at differenceZero
  calc
    p.eval point =
        (p.eval point - left.eval point * right.eval point) +
          left.eval point * right.eval point := by ring1
    _ = 0 + left.eval point * right.eval point := by rw [differenceZero]
    _ = left.eval point * right.eval point :=
      Fraction.Field.zero_add _

end Factorization

namespace Factorization

/-- The finite coefficient factorization also identifies the automatic
derivatives pointwise. -/
theorem eval_derivative_factorization
    {p left right : BoundaryFactorization.CoefficientPolynomial}
    (factorization : Factorization p left right) (point : Fraction.Rational) :
    (Dense.Derivative.derivative p).eval point =
      (Dense.Derivative.derivative (left * right)).eval point :=
  Dense.Derivative.eval_derivative_eq_of_sub_isZero
    factorization point

end Factorization

namespace Factorization

/-- Exchange the two displayed factors without polynomial extensionality. -/
theorem factorization_swap
    {p left right : BoundaryFactorization.CoefficientPolynomial}
    (factorization : Factorization p left right) :
    Factorization p right left := by
  apply Dense.Rational.Factorization.factorizationOfEvals
  intro point
  rw [Dense.Rational.Factorization.eval_factorization factorization point]
  exact Fraction.Field.mul_comm _ _

end Factorization

namespace Factorization

/-- A factorization of a normalized nonzero polynomial has a nonzero right factor. -/
theorem right_isZero_false
    {p left right : BoundaryFactorization.CoefficientPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (factorization : Factorization p left right) :
    right.isZero = false := by
  by_cases rightZero : right.isZero = true
  · have productZero : left * right = (0 : BoundaryFactorization.CoefficientPolynomial) :=
      Dense.Basic.DensePolynomial.mul_eq_zero_of_isZero_right rightZero
    change (p - left * right).isZero = true at factorization
    rw [productZero] at factorization
    have targetZero : p.isZero = true := by
      change (p + -(0 : BoundaryFactorization.CoefficientPolynomial)).isZero = true at factorization
      have negZero : -(0 : BoundaryFactorization.CoefficientPolynomial) = 0 := rfl
      rw [negZero, Dense.Basic.DensePolynomial.add_zero_normalize, pNormalized] at factorization
      exact factorization
    rw [pNonzero] at targetZero
    exact Bool.noConfusion targetZero
  · exact Decide.bool_eq_false_of_not_eq_true right.isZero rightZero

end Factorization

namespace Factorization

/-- The degrees of two nonzero displayed factors add to the degree of their normalized nonzero product polynomial. -/
theorem factor_natDegree_add
    {p left right : BoundaryFactorization.CoefficientPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (leftNonzero : left.isZero = false) (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    left.natDegree + right.natDegree = p.natDegree := by
  have productNonzero := Dense.Basic.DensePolynomial.isZero_mul_eq_false leftNonzero rightNonzero
  have degree := Dense.Leading.LeadingTerm.natDegree_eq_of_sub_isZero pNonzero
    productNonzero pNormalized (Dense.Basic.DensePolynomial.normalize_mul left right) factorization
  rw [Dense.Basic.DensePolynomial.natDegree_mul leftNonzero rightNonzero] at degree
  exact degree.symm

end Factorization

end Purelib.Polynomial.Dense.Rational

end
