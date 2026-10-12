module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.List.Fold
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.Bezout.GCD
public import Purelib.Polynomial.Dense.Rational.Derivative.Degree
public import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
public import Purelib.Polynomial.Dense.Rational.Squarefree.Locate
import Purelib.Polynomial.Dense.Rational.Squarefree.Product

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

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

set_option genInjectivity false in
/-- Complete positive-degree squarefree occurrence decomposition. -/
structure Decomposition (p :
  BoundaryFactorization.CoefficientPolynomial)
  where
  /-- The ordered finite list of normalized positive-degree squarefree factors, retaining multiplicities
  as occurrences. -/
  factors : List Dense.Rational.Squarefree.Factor
  /-- At least one squarefree factor is retained. -/ factorsNonempty : factors ≠ []
  /-- The source evaluates as the exact finite product of the retained factor occurrences. -/ evalIdentity : ∀ point :
    Fraction.Rational,
    p.eval point = (Dense.Rational.Squarefree.factorProduct factors).eval point
  /-- The sum of retained factor degrees is exactly the source degree. -/ degreeSum : (factors.map fun factor =>
    factor.polynomial.natDegree).sum =
    p.natDegree

constructive_injectivity Decomposition

namespace Decomposition

/-- Select a retained squarefree factor vanishing at the supplied root of the source polynomial. -/
@[expose] def locateRoot
    {p : BoundaryFactorization.CoefficientPolynomial} (decomposition : Decomposition p)
    (point : Fraction.Rational) (root : p.eval point = 0) :
    Dense.Rational.Squarefree.LocatedFactor decomposition.factors point := by
  apply Dense.Rational.Squarefree.locateFactor decomposition.factors point
  rw [← decomposition.evalIdentity point]
  exact root

/-- The source vanishes exactly where one of its retained squarefree factors vanishes. -/
theorem eval_eq_zero_iff
    {p : BoundaryFactorization.CoefficientPolynomial} (decomposition : Decomposition p)
    (point : Fraction.Rational) :
    p.eval point = 0 ↔
      ∃ factor ∈ decomposition.factors,
        factor.polynomial.eval point = 0 := by
  rw [decomposition.evalIdentity point]
  exact Dense.Rational.Squarefree.factorProduct_eval_eq_zero_iff decomposition.factors point

end Decomposition

/-- Construct the one-factor decomposition of a normalized nonzero positive-degree squarefree polynomial. -/
@[expose] def singletonDecomposition
    (p : BoundaryFactorization.CoefficientPolynomial) (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false) (pPositive : 0 < p.natDegree)
    (squarefree : Dense.Rational.Squarefree.SquarefreeCertificate p) : Decomposition p :=
  { factors :=
      [{ polynomial := p
         normalized := pNormalized
         nonzero := pNonzero
         degreePositive := pPositive
         squarefree := squarefree }]
    factorsNonempty := by intro impossible; exact List.cons_ne_nil _ _ impossible
    evalIdentity := by
      intro point
      simp only [Dense.Rational.Squarefree.factorProduct, DensePolynomial.eval_mul,
        DensePolynomial.eval_constant,
        Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      rfl
    degreeSum := by change p.natDegree + 0 = p.natDegree; exact Nat.add_zero _ }

/-- Combine two retained decompositions using their source factorization and exact degree balance.

The ordered factor lists are concatenated; evaluation and degree certificates are transported from the original divisor
and cofactor. -/
@[expose] def appendDecompositions
    (p divisor cofactor : BoundaryFactorization.CoefficientPolynomial)
    (factorization : Factorization p divisor cofactor)
    (degreeBalance :
      divisor.natDegree + cofactor.natDegree = p.natDegree)
    (leftDecomposition : Decomposition divisor)
    (rightDecomposition : Decomposition cofactor) : Decomposition p
      :=
  { factors := leftDecomposition.factors ++ rightDecomposition.factors
    factorsNonempty := by
      cases factorsEquation : leftDecomposition.factors with
      | nil => exact
          (leftDecomposition.factorsNonempty factorsEquation).elim
      | cons factor factors =>
          intro impossible
          exact List.cons_ne_nil _ _ impossible
    evalIdentity := by
      intro point
      calc
        p.eval point = divisor.eval point * cofactor.eval point :=
          Dense.Rational.Factorization.eval_factorization factorization point
        _ = (Dense.Rational.Squarefree.factorProduct leftDecomposition.factors).eval point *
            (Dense.Rational.Squarefree.factorProduct rightDecomposition.factors).eval point := by
          exact congrArg₂ (· * ·) (leftDecomposition.evalIdentity point)
            (rightDecomposition.evalIdentity point)
        _ = (Dense.Rational.Squarefree.factorProduct
            (leftDecomposition.factors ++
              rightDecomposition.factors)).eval point := by
          induction leftDecomposition.factors with
          | nil =>
              simp only [Dense.Rational.Squarefree.factorProduct,
                DensePolynomial.eval_constant, Fraction.Field.one_mul, -eq_self, -iff_self]
              rfl
          | cons factor factors inductionHypothesis =>
              simp only [List.cons_append, Dense.Rational.Squarefree.factorProduct,
                DensePolynomial.eval_mul, -eq_self, -iff_self]
              calc
                (factor.polynomial.eval point *
                    (Dense.Rational.Squarefree.factorProduct factors).eval point) *
                      (Dense.Rational.Squarefree.factorProduct rightDecomposition.factors).eval point =
                  factor.polynomial.eval point *
                    ((Dense.Rational.Squarefree.factorProduct factors).eval point *
                      (Dense.Rational.Squarefree.factorProduct rightDecomposition.factors).eval
                        point) := by ring1
                _ = factor.polynomial.eval point *
                    (Dense.Rational.Squarefree.factorProduct
                      (factors ++ rightDecomposition.factors)).eval point :=
                  congrArg (factor.polynomial.eval point * ·)
                    inductionHypothesis
    degreeSum := by
      simp only [Purelib.Data.List.Map.map_append, Purelib.Data.List.Fold.sum_append Nat.zero_add Nat.add_assoc,
        leftDecomposition.degreeSum, rightDecomposition.degreeSum, -eq_self, -iff_self]
      exact degreeBalance }

/-- Degree-recursive decomposition by the displayed derivative gcd. -/
@[expose] def decomposeNormalized
    (p : BoundaryFactorization.CoefficientPolynomial) (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false) (pPositive : 0 < p.natDegree) :
    Decomposition p := by
  let derivative := Dense.Derivative.derivative p
  let result := Dense.GCD.extendedGCD p derivative
  have derivativeNonzero : derivative.isZero = false := by
    exact Dense.Rational.Derivative.Degree.derivative_isZero_false
      pNonzero pPositive
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero (Or.inl pNonzero)
  if degreeZero : result.gcd.natDegree = 0 then
    let squarefree : Dense.Rational.Squarefree.SquarefreeCertificate p :=
      Dense.Rational.Bezout.certificateOfConstantGCD p derivative gcdNonzero degreeZero
    exact singletonDecomposition p pNormalized pNonzero pPositive squarefree
  else
    let divisor := result.gcd
    let cofactor := result.pFactor
    have derivativeDegree : derivative.natDegree < p.natDegree :=
      Dense.Derivative.derivative_natDegree_lt pNonzero pPositive
    have divisorProper : divisor.natDegree < p.natDegree :=
      (result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
    have divisorPositive : 0 < divisor.natDegree :=
      Nat.pos_of_ne_zero degreeZero
    have factorization : Factorization p divisor cofactor := by
      apply Dense.Rational.Factorization.factorizationOfEvals
      exact result.pIdentity
    have cofactorNonzero : cofactor.isZero = false :=
      Dense.Rational.Factorization.right_isZero_false pNonzero pNormalized factorization
    have degreeBalance :
        divisor.natDegree + cofactor.natDegree = p.natDegree :=
      Dense.Rational.Factorization.factor_natDegree_add pNonzero pNormalized gcdNonzero cofactorNonzero
        factorization
    have cofactorPositive : 0 < cofactor.natDegree := by
      apply Nat.pos_of_ne_zero
      intro cofactorZero
      rw [cofactorZero, Nat.add_zero] at degreeBalance
      exact (Nat.ne_of_lt divisorProper) degreeBalance
    have cofactorProper : cofactor.natDegree < p.natDegree := by
      calc
        cofactor.natDegree < divisor.natDegree + cofactor.natDegree :=
          Nat.lt_add_of_pos_left divisorPositive
        _ = p.natDegree := degreeBalance
    let leftDecomposition := decomposeNormalized divisor result.normalized
      gcdNonzero divisorPositive
    let rightDecomposition := decomposeNormalized cofactor
      result.pFactorNormalized cofactorNonzero cofactorPositive
    exact appendDecompositions p divisor cofactor factorization degreeBalance
      leftDecomposition rightDecomposition
termination_by p.natDegree
decreasing_by
  · exact divisorProper
  · exact cofactorProper

/-- Total decomposition of a represented nonzero positive-degree coordinate
polynomial. -/
@[expose] def decompose
    (p : BoundaryFactorization.CoefficientPolynomial) (pNonzero : p.isZero = false)
    (pPositive : 0 < p.natDegree) : Decomposition p.normalize :=
  decomposeNormalized p.normalize (DensePolynomial.normalize_normalize p)
    (by simpa only [DensePolynomial.isZero_normalize, -eq_self, -iff_self])
    (by simpa only [DensePolynomial.natDegree_normalize, -eq_self, -iff_self])

end Purelib.Polynomial.Dense.Rational.Squarefree

end
