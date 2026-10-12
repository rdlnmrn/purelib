module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.GCD
public import Purelib.Polynomial.Dense.Rational.Bezout.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Algebra.Field

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

namespace Purelib.Polynomial.Dense.Rational.Bezout

/-- Normalize a checked constant Euclidean gcd into explicit coordinate
Bézout data. -/
def certificateOfConstantGCD
    (p q : Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (gcdNonzero : (Dense.GCD.extendedGCD p q).gcd.isZero = false)
    (degreeZero :
      (Dense.GCD.extendedGCD p q).gcd.natDegree = 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate p q := by
  let result := Dense.GCD.extendedGCD p q
  let unit := result.gcd.leadingCoeff
  have unitNonzero : unit ≠ 0 := DensePolynomial.leadingCoeff_ne_zero gcdNonzero
  have gcdConstant : result.gcd = DensePolynomial.constant unit := by
    calc
      result.gcd = result.gcd.normalize := result.normalized.symm
      _ = DensePolynomial.constant result.gcd.leadingCoeff :=
        DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero gcdNonzero degreeZero
  exact
    { left := DensePolynomial.scale unit⁻¹ result.left
      right := DensePolynomial.scale unit⁻¹ result.right
      identity := by
        intro point
        have raw := result.identity point
        rw [gcdConstant, DensePolynomial.eval_constant] at raw
        simp only [DensePolynomial.eval_scale]
        calc
          1 = unit⁻¹ * unit := by
            rw [Fraction.Field.mul_comm]
            exact (ExplicitField.mul_inv_cancel unit unitNonzero).symm
          _ = unit⁻¹ *
              (result.left.eval point * p.eval point +
                result.right.eval point * q.eval point) := by rw [← raw]
          _ = unit⁻¹ * (result.left.eval point * p.eval point) +
              unit⁻¹ * (result.right.eval point * q.eval point) :=
            Fraction.Field.left_distrib _ _ _
          _ = (unit⁻¹ * result.left.eval point) * p.eval point +
              (unit⁻¹ * result.right.eval point) * q.eval point := by
            rw [Fraction.Field.mul_assoc,
              Fraction.Field.mul_assoc] }
end Purelib.Polynomial.Dense.Rational.Bezout

end
