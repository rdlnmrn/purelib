module
import Purelib.Data.Bool.Decide
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Factor
public import Purelib.Polynomial.Dense.Rational.Bezout.GCD
public import Purelib.Polynomial.Dense.Rational.Degree.Zero
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
public import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Rat

open Purelib.Polynomial
open Purelib.Data.List
open Purelib.Data.Bool

section
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

namespace Purelib.Polynomial.Dense.Rational.Factorization

/-- Split a squarefree polynomial factor against a retained condition polynomial.

The common-divisor piece retains its factorization of the original condition.
The complementary piece carries a finite coprimality certificate with that
same condition; the retained pieces cover exactly the original factor's roots. -/
@[expose] def splitAgainstCondition
    (factor : Dense.Rational.Squarefree.Factor) (condition : BoundaryFactorization.CoefficientPolynomial) :
    Dense.Rational.Factorization.ConditionPartition factor condition := by
  by_cases conditionZero : condition.isZero = true
  · let zeroPiece : Dense.Rational.Factorization.ConditionPiece factor condition :=
      { factor := factor
        cofactor := Dense.Basic.DensePolynomial.constant 1
        factorization := by
          apply Dense.Rational.Factorization.factorizationOfEvals
          intro point
          rw [Dense.Basic.DensePolynomial.eval_constant,
            Fraction.Field.mul_one_direct]
        relation := .equality (Dense.Basic.DensePolynomial.constant 0) (by
          apply Dense.Rational.Factorization.factorizationOfEvals
          intro point
          rw [Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero conditionZero point,
            Dense.Basic.DensePolynomial.eval_constant,
            Fraction.Field.mul_zero_direct]) }
    exact
      { pieces := [zeroPiece]
        nonempty := List.cons_ne_nil _ _
        rootCoverage := by
          intro point
          constructor
          · intro factorZero
            exact ⟨zeroPiece, List.mem_cons_self, factorZero⟩
          · rintro ⟨piece, member, pieceZero⟩
            have equal : piece = zeroPiece := Membership.mem_singleton.mp member
            subst piece
            exact pieceZero }
  · have conditionNonzero : condition.isZero = false :=
      Decide.bool_eq_false_of_not_eq_true condition.isZero conditionZero
    let result := Dense.GCD.extendedGCD
      factor.polynomial condition
    have gcdNonzero : result.gcd.isZero = false :=
      result.nonzero (Or.inl factor.nonzero)
    by_cases gcdDegreeZero : result.gcd.natDegree = 0
    · let coprime := Dense.Rational.Bezout.certificateOfConstantGCD factor.polynomial condition
        gcdNonzero gcdDegreeZero
      let apartPiece : Dense.Rational.Factorization.ConditionPiece factor condition :=
        { factor := factor
          cofactor := Dense.Basic.DensePolynomial.constant 1
          factorization := by
            apply Dense.Rational.Factorization.factorizationOfEvals
            intro point
            rw [Dense.Basic.DensePolynomial.eval_constant,
              Fraction.Field.mul_one_direct]
          relation := .apart coprime }
      exact
        { pieces := [apartPiece]
          nonempty := List.cons_ne_nil _ _
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              exact ⟨apartPiece, List.mem_cons_self, factorZero⟩
            · rintro ⟨piece, member, pieceZero⟩
              have equal : piece = apartPiece := Membership.mem_singleton.mp member
              subst piece
              exact pieceZero }
    · have gcdDegreePositive : 0 < result.gcd.natDegree :=
        Nat.pos_of_ne_zero gcdDegreeZero
      have originalFactorization : Factorization factor.polynomial
          result.gcd result.pFactor := by
        apply Dense.Rational.Factorization.factorizationOfEvals
        exact result.pIdentity
      have remainingNonzero : result.pFactor.isZero = false :=
        Dense.Rational.Factorization.right_isZero_false factor.nonzero factor.normalized
          originalFactorization
      have degreeBalance : result.gcd.natDegree +
          result.pFactor.natDegree = factor.polynomial.natDegree :=
        Dense.Rational.Factorization.factor_natDegree_add factor.nonzero factor.normalized gcdNonzero
          remainingNonzero originalFactorization
      let equalityFactor : Dense.Rational.Squarefree.Factor :=
        { polynomial := result.gcd
          normalized := result.normalized
          nonzero := gcdNonzero
          degreePositive := gcdDegreePositive
          squarefree := Dense.Rational.Bezout.leftFactorSquarefree factor.squarefree gcdNonzero
            originalFactorization }
      have conditionFactorization : Factorization condition
          result.gcd result.qFactor := by
        apply Dense.Rational.Factorization.factorizationOfEvals
        exact result.qIdentity
      let equalityPiece : Dense.Rational.Factorization.ConditionPiece factor condition :=
        { factor := equalityFactor
          cofactor := result.pFactor
          factorization := originalFactorization
          relation := .equality result.qFactor conditionFactorization }
      by_cases remainingDegreeZero : result.pFactor.natDegree = 0
      · have remainingEvalNonzero :=
          Dense.Rational.eval_ne_zero_of_normalized_degree_zero
            result.pFactorNormalized remainingNonzero remainingDegreeZero
        exact
          { pieces := [equalityPiece]
            nonempty := List.cons_ne_nil _ _
            rootCoverage := by
              intro point
              constructor
              · intro factorZero
                rw [Dense.Rational.Factorization.eval_factorization originalFactorization point] at factorZero
                by_cases gcdZero : result.gcd.eval point = 0
                · refine ⟨equalityPiece, List.mem_cons_self, ?_⟩
                  change result.gcd.eval point = 0
                  exact gcdZero
                · exact (Fraction.Field.mul_ne_zero_direct gcdZero
                    (remainingEvalNonzero point) factorZero).elim
              · rintro ⟨piece, member, pieceZero⟩
                have equal : piece = equalityPiece :=
                  Membership.mem_singleton.mp member
                subst piece
                change result.gcd.eval point = 0 at pieceZero
                rw [Dense.Rational.Factorization.eval_factorization originalFactorization point, pieceZero,
                  Fraction.Field.zero_mul_direct]
                }
      · have remainingDegreePositive : 0 < result.pFactor.natDegree :=
          Nat.pos_of_ne_zero remainingDegreeZero
        let remainingFactor : Dense.Rational.Squarefree.Factor :=
          { polynomial := result.pFactor
            normalized := result.pFactorNormalized
            nonzero := remainingNonzero
            degreePositive := remainingDegreePositive
            squarefree := Dense.Rational.Bezout.rightFactorSquarefree factor.squarefree
              remainingNonzero originalFactorization }
        let factorCoprime :
            Dense.Rational.Bezout.Basic.CoprimeCertificate
              result.gcd result.pFactor :=
          Dense.Rational.Bezout.factorsCoprime factor.squarefree gcdNonzero originalFactorization
        let remainingGcdCoprime :
            Dense.Rational.Bezout.Basic.CoprimeCertificate
              result.pFactor result.gcd := factorCoprime.swap
        let remainingReducedCoprime :
            Dense.Rational.Bezout.Basic.CoprimeCertificate
              result.pFactor result.qFactor :=
          { left := result.factorLeft
            right := result.factorRight
            identity := result.factorIdentity }
        let remainingConditionCoprime := Dense.Rational.Bezout.coprimeWithProduct
          remainingGcdCoprime remainingReducedCoprime conditionFactorization
        let remainingPiece : Dense.Rational.Factorization.ConditionPiece factor condition :=
          { factor := remainingFactor
            cofactor := result.gcd
            factorization := Dense.Rational.Factorization.factorization_swap originalFactorization
            relation := .apart remainingConditionCoprime }
        exact
          { pieces := [equalityPiece, remainingPiece]
            nonempty := List.cons_ne_nil _ _
            rootCoverage := by
              intro point
              constructor
              · intro factorZero
                have productZero : result.gcd.eval point *
                    result.pFactor.eval point = 0 := by
                  rw [← Dense.Rational.Factorization.eval_factorization originalFactorization point]
                  exact factorZero
                by_cases gcdZero : result.gcd.eval point = 0
                · refine ⟨equalityPiece, List.mem_cons_self, ?_⟩
                  change result.gcd.eval point = 0
                  exact gcdZero
                · by_cases remainingZero : result.pFactor.eval point = 0
                  · refine ⟨remainingPiece,
                      List.mem_cons_of_mem equalityPiece List.mem_cons_self, ?_⟩
                    change result.pFactor.eval point = 0
                    exact remainingZero
                  · exact (Fraction.Field.mul_ne_zero_direct gcdZero
                      remainingZero productZero).elim
              · rintro ⟨piece, member, pieceZero⟩
                rw [Dense.Rational.Factorization.eval_factorization originalFactorization point]
                rcases Membership.mem_cons.mp member with equality | remaining
                · subst piece
                  change result.gcd.eval point = 0 at pieceZero
                  rw [pieceZero, Fraction.Field.zero_mul_direct]
                · have pieceEq : piece = remainingPiece :=
                    Membership.mem_singleton.mp remaining
                  subst piece
                  change result.pFactor.eval point = 0 at pieceZero
                  rw [pieceZero,
                    Fraction.Field.mul_zero_direct] }
end Purelib.Polynomial.Dense.Rational.Factorization

end
