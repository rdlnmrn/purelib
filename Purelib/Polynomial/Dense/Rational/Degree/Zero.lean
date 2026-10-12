module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

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

/-- If a polynomial is normalized, nonzero, and degree zero, every displayed
evaluation is nonzero. -/
theorem eval_ne_zero_of_normalized_degree_zero
    {polynomial : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial}
    (normalized : polynomial.normalize = polynomial)
    (nonzero : polynomial.isZero = false)
    (degreeZero : polynomial.natDegree = 0)
    (point : Fraction.Rational) : polynomial.eval point ≠ 0 := by
  have polynomialConstant :
      polynomial = DensePolynomial.constant polynomial.leadingCoeff := by
    calc
      polynomial = polynomial.normalize := normalized.symm
      _ = DensePolynomial.constant polynomial.leadingCoeff :=
        DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
  rw [polynomialConstant, DensePolynomial.eval_constant]
  exact DensePolynomial.leadingCoeff_ne_zero nonzero
end Purelib.Polynomial.Dense.Rational

end
