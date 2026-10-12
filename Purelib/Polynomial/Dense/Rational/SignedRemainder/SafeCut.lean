module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
public import Purelib.Polynomial.Dense.Rational.Product.List
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Reduced
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.SafeCut

/-- One guard polynomial vanishing wherever any member of the finite reduced
chain vanishes. -/
def chainGuard (numerator denominator :
  CoordinatePolynomial) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.Product.List.polynomialProduct (Dense.Rational.SignedRemainder.Reduced.reducedChain numerator
    denominator)

/-- The product guard of the reduced signed chain is nonzero when the original denominator is nonzero. -/
theorem chainGuard_isZero_false
    {numerator denominator : CoordinatePolynomial}
    (denominatorNonzero : denominator.isZero = false) :
    (chainGuard numerator denominator).isZero = false :=
  Dense.Rational.Product.List.polynomialProduct_isZero_false
    (Dense.Rational.SignedRemainder.Reduced.reducedChain_all_nonzero denominatorNonzero)

/-- Bounded central-third scan for a cut avoiding every reduced-chain
event. -/
def safeCut
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Data.Rat.Interval.Bounds) (proper : interval.lower < interval.upper) :
    Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero)
    (Nat.le_refl _)

/-- The selected safe cut lies strictly inside the interval and does not vanish on the chain guard. -/
theorem safeCut_spec
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Data.Rat.Interval.Bounds) (proper : interval.lower < interval.upper) :
    (chainGuard numerator denominator).eval
        (safeCut numerator denominator denominatorNonzero
          interval proper) ≠ 0 ∧
      interval.lower <
        safeCut numerator denominator denominatorNonzero
          interval proper ∧
      safeCut numerator denominator denominatorNonzero
          interval proper < interval.upper := by
  exact Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero)
    (Nat.le_refl _)

/-- Every retained member of the reduced signed chain is nonzero at the selected safe cut. -/
theorem safeCut_avoids_chain
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Data.Rat.Interval.Bounds) (proper : interval.lower < interval.upper)
    {member : CoordinatePolynomial} (membership :
      member ∈ Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator) :
    member.eval
        (safeCut numerator denominator denominatorNonzero
          interval proper) ≠ 0 :=
  Dense.Rational.Product.List.eval_ne_zero_of_mem_of_polynomialProduct membership
    (safeCut_spec numerator denominator denominatorNonzero
      interval proper).1

/-- Both children of the safe cut contract by the fixed central-third
factor, independently of coefficient degree. -/
theorem safeCut_contraction
    (numerator denominator : CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (interval : Data.Rat.Interval.Bounds) (proper : interval.lower < interval.upper) :
    safeCut numerator denominator denominatorNonzero interval proper -
          interval.lower <
        (2 / 3 : Fraction.Rational) * (interval.upper - interval.lower) ∧
      interval.upper -
          safeCut numerator denominator denominatorNonzero interval proper <
        (2 / 3 : Fraction.Rational) *
          (interval.upper - interval.lower) := by
  exact Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction
    (chainGuard numerator denominator)
    (chainGuard numerator denominator).natDegree proper
    (chainGuard_isZero_false denominatorNonzero) (Nat.le_refl _)

end Purelib.Polynomial.Dense.Rational.SignedRemainder.SafeCut

end
