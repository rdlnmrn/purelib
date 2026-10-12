module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Degree
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Data.Bool.Decide
public import Purelib.Data.List.Map
public import Purelib.Data.List.Fold
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

public section

/-!
# General finite squarefree-factor preprocessing

The executable squarefreeness decision either returns a finite Bézout
certificate or splits the input by its computed nonconstant gcd with the
derivative.  Both displayed factors then have strictly smaller positive
degree.  Recursing on those natural degrees produces a finite occurrence list
of squarefree factors whose evaluated product is the normalized input.

Repeated factors appear as repeated squarefree occurrences at this layer;
the following multiplicity layer canonically groups associates without
creating duplicate root-isolation machines.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute

open Purelib.Polynomial
open Purelib.Data.List
open Purelib.Data.Bool

/-- Degree-recursive decomposition by the computed gcd with the derivative.

The exact normalized input retains its finite squarefree occurrences in order.
A nonconstant common divisor splits into the original divisor and cofactor,
whose strictly smaller degrees bound the two recursive constructions. -/
@[expose] def decomposeNormalized
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false) (pPositive : 0 < p.natDegree) :
    Decomposition p := by
  match outcome : Dense.Gaussian.Squarefree.Decision.squarefreeOutcome p pNonzero with
  | .coprime certificate =>
      exact
        { factors :=
            [{ polynomial := p
               normalized := pNormalized
               nonzero := pNonzero
               degreePositive := pPositive
               squarefree := certificate }]
          factorsNonempty := by intro impossible; cases impossible
          evalIdentity := by
            intro point
            simp only [Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct,
              Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_constant,
              Purelib.Data.Gaussian.Basic.mul_one, -eq_self]
            rfl
          degreeSum := by change p.natDegree + 0 = p.natDegree; rfl }
  | .commonDivisor common =>
      let divisor := common.divisor
      let cofactor := common.leftFactor
      have derivativeNonzero :
          (Dense.Gaussian.GCD.derivative p).isZero = false :=
        Dense.Gaussian.Derivative.Degree.derivative_isZero_false pNonzero
          pPositive
      have derivativeDegree :
          (Dense.Gaussian.GCD.derivative p).natDegree < p.natDegree := by
        exact Dense.Derivative.derivative_natDegree_lt pNonzero pPositive
      have divisorProper : divisor.natDegree < p.natDegree :=
        (common.result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
      have factorization : Dense.Gaussian.Factorization.Identity.ProductIdentity p divisor cofactor := by
        apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
        intro point _
        exact common.leftIdentity point
      have cofactorNonzero : cofactor.isZero = false :=
        Dense.Gaussian.Factorization.Identity.right_isZero_false pNonzero pNormalized factorization
      have degreeBalance :
          divisor.natDegree + cofactor.natDegree = p.natDegree :=
        Dense.Gaussian.Factorization.Identity.factor_natDegree_add pNonzero pNormalized common.nonzero
          cofactorNonzero factorization
      have divisorPositive : 0 < divisor.natDegree := by
        exact common.positiveDegree
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
      let leftDecomposition := Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute.decomposeNormalized
        divisor
        common.result.normalized common.nonzero common.positiveDegree
      let rightDecomposition := Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute.decomposeNormalized
        cofactor
        common.result.pFactorNormalized cofactorNonzero cofactorPositive
      exact
        { factors := leftDecomposition.factors ++ rightDecomposition.factors
          factorsNonempty := by
            cases factorsEquation : leftDecomposition.factors with
            | nil => exact
                (leftDecomposition.factorsNonempty factorsEquation).elim
            | cons factor factors =>
                intro impossible
                cases impossible
          evalIdentity := by
            intro point
            calc
              p.eval point = divisor.eval point * cofactor.eval point :=
                common.leftIdentity point
              _ = (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct leftDecomposition.factors).eval point *
                    (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct rightDecomposition.factors).eval point
                      := by
                  rw [← leftDecomposition.evalIdentity,
                    ← rightDecomposition.evalIdentity]
              _ = (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct
                    (leftDecomposition.factors ++
                      rightDecomposition.factors)).eval point :=
                (Dense.Gaussian.Squarefree.Decomposition.Basic.factorProduct_append_eval _ _ point).symm
          degreeSum := by
            rw [Map.map_append,
              Fold.sum_append Nat.zero_add Nat.add_assoc,
              leftDecomposition.degreeSum, rightDecomposition.degreeSum]
            exact degreeBalance }
termination_by p.natDegree
decreasing_by
  all_goals first | exact divisorProper | exact cofactorProper

set_option genInjectivity false in
/-- Positive-degree branch of total general-polynomial preprocessing.

The original nonzero and degree certificates accompany the occurrence
decomposition of that same input's exact normalization. -/
structure PositivePreprocessing (p : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original polynomial has a nonzero coefficient. -/ nonzero : p.isZero = false
  /-- The original polynomial has positive represented degree. -/ degreePositive : 0 < p.natDegree
  /-- The squarefree occurrence decomposition of the exact normalized input. -/ decomposition :
    Decomposition p.normalize

constructive_injectivity PositivePreprocessing

set_option genInjectivity false in
/-- Total finite preprocessing distinguishes zero, constant and positive degree.

Each branch retains the original Boolean or degree certificate. Positive degree
retains the complete squarefree occurrence decomposition of the normalized input. -/
inductive Preprocessing (p : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The original coefficient representation evaluates as the zero polynomial. -/ | zero (certificate : p.isZero =
    true)
  /-- The original polynomial is nonzero and has degree zero. -/ | constant (nonzero : p.isZero = false) (degreeZero :
    p.natDegree = 0)
  /-- Retain the positive-degree certificate and complete squarefree occurrence decomposition. -/ | positive (result :
    PositivePreprocessing p)

constructive_injectivity Preprocessing

/-- Classify and preprocess a finite Gaussian-rational polynomial.

The zero and constant branches retain their exact tests; the positive-degree branch normalizes the input and recursively
decomposes it using derivative-gcd certificates. -/
@[expose] def preprocess (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : Preprocessing p := by
  if zero : p.isZero = true then
    exact .zero zero
  else
    have nonzero : p.isZero = false :=
      Decide.bool_eq_false_of_not_eq_true _ zero
    if degreeZero : p.natDegree = 0 then
      exact .constant nonzero degreeZero
    else
      have degreePositive : 0 < p.natDegree := Nat.pos_of_ne_zero degreeZero
      exact .positive
        { nonzero := nonzero
          degreePositive := degreePositive
          decomposition := decomposeNormalized p.normalize
            (Dense.Basic.DensePolynomial.normalize_normalize p)
            (by
              rw [Dense.Basic.DensePolynomial.isZero_normalize]; exact nonzero)
            (by
              rw [Dense.Basic.DensePolynomial.natDegree_normalize]; exact degreePositive) }
end Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute

end
