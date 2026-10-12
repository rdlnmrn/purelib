module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Squarefree (Factor)

public section

open Purelib.Data.Rat

open Purelib.Polynomial

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace Purelib.Polynomial.Dense.Rational.Squarefree

/-- Multiply the displayed squarefree factors in list order, with constant one for the empty list. -/
@[expose] def factorProduct : List Factor
  → BoundaryFactorization.CoefficientPolynomial
  | [] => DensePolynomial.constant 1
  | factor :: factors => factor.polynomial * factorProduct factors

/-- Remove the first occurrence of a displayed factor polynomial from a
finite factor product.  Matching only the polynomial data avoids requiring
decidable equality on the proof-bearing `Factor` record. -/
@[expose] def factorCofactor (target :
  BoundaryFactorization.CoefficientPolynomial) : List Factor →
  BoundaryFactorization.CoefficientPolynomial
  | [] => DensePolynomial.constant 1
  | factor :: factors =>
      if factor.polynomial = target then factorProduct factors
      else factor.polynomial * factorCofactor target factors

/-- A factor selected from the finite decomposition can be split from the
product with an explicitly computed remaining cofactor. -/
theorem factorProduct_eval_eq_factor_mul_cofactor
    (factor : Factor) (factors : List Factor)
    (member : factor ∈ factors) (point : Fraction.Rational) :
    (factorProduct factors).eval point =
      factor.polynomial.eval point *
        (factorCofactor factor.polynomial factors).eval point := by
  induction factors with
  | nil => exact (List.not_mem_nil member).elim
  | cons head factors inductionHypothesis =>
      by_cases samePolynomial : head.polynomial = factor.polynomial
      · simp only [factorProduct, factorCofactor, samePolynomial,
          if_pos (Eq.refl factor.polynomial),
          DensePolynomial.eval_mul, -eq_self, -iff_self]
        rfl
      · have tailMember : factor ∈ factors := by
          rcases Purelib.Data.List.Membership.mem_cons.mp member with sameFactor | tailMember
          · subst factor
            exact (samePolynomial rfl).elim
          · exact tailMember
        simp only [factorProduct, factorCofactor, if_neg
          samePolynomial,
          DensePolynomial.eval_mul, -eq_self, -iff_self]
        rw [inductionHypothesis tailMember]
        ring1

/-- A finite product of squarefree factors vanishes exactly when a retained factor vanishes.

The statement identifies an actual member of the displayed factor list at the given rational point. -/
theorem factorProduct_eval_eq_zero_iff
    (factors : List Factor) (point : Fraction.Rational) :
    (factorProduct factors).eval point = 0 ↔
      ∃ factor ∈ factors, factor.polynomial.eval point = 0 := by
  induction factors with
  | nil =>
      constructor
      · intro productZero
        simp only [factorProduct, DensePolynomial.eval_constant, -eq_self,
          -iff_self] at productZero
        exact (Fraction.Field.zero_ne_one productZero.symm).elim
      · rintro ⟨factor, member, _zero⟩
        exact (List.not_mem_nil member).elim
  | cons factor factors inductionHypothesis =>
      rw [factorProduct, DensePolynomial.eval_mul]
      constructor
      · intro productZero
        by_cases headZero : factor.polynomial.eval point = 0
        · exact ⟨factor, List.mem_cons_self, headZero⟩
        · have tailZero : (factorProduct factors).eval point = 0 := by
            by_cases tailZero : (factorProduct factors).eval point = 0
            · exact tailZero
            · exact (Fraction.Field.mul_ne_zero_direct
                headZero tailZero productZero).elim
          rcases inductionHypothesis.mp tailZero with
            ⟨found, member, zero⟩
          exact ⟨found, List.mem_cons_of_mem factor member, zero⟩
      · rintro ⟨found, member, zero⟩
        rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | tailMember
        · rw [zero, Fraction.Field.zero_mul_direct]
        · rw [(inductionHypothesis.mpr ⟨found, tailMember, zero⟩),
            Fraction.Field.mul_zero_direct]
end Purelib.Polynomial.Dense.Rational.Squarefree

end
