module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Affine substitution of the Gaussian coordinate polynomial

Substitution into the original coordinate polynomial returns its direction
and origin coefficients. A nonzero direction certifies normalization.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Coordinate

/-- Substituting an affine line into the coordinate polynomial yields exactly its direction and origin coefficient pair.

The direction is nonzero, so the resulting descending linear coefficient representation is already normalized. -/
public theorem
  composeLine_coordinate (origin
  direction : Gaussian.Basic.Canonical)
    (directionNonzero : direction ≠ 0) :
    composeLine Monomial.Coordinate.coordinatePolynomial origin
      direction =
      ⟨[direction, origin]⟩ := by
  rw [composeLine, composeLineCoeffs]
  simp only [Monomial.Coordinate.coordinatePolynomial, List.foldl_cons, List.foldl_nil]
  rw [mulLine_zero, Basic.DensePolynomial.zero_add_normalize,
    Basic.DensePolynomial.normalize_constant_of_ne one_ne_zero]
  rw [mulLine, Basic.DensePolynomial.scale_constant,
    Basic.DensePolynomial.scale_constant,
    Gaussian.Basic.mul_one,
    Gaussian.Basic.mul_one,
    Basic.DensePolynomial.normalize_constant_of_ne directionNonzero,
    Basic.DensePolynomial.shift_one_constant_of_ne directionNonzero]
  by_cases originZero : origin = 0
  · subst origin
    rw [Basic.DensePolynomial.normalize_constant_zero, Basic.DensePolynomial.zero_add_normalize,
      Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero,
      Basic.DensePolynomial.add_constant_zero,
      Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero]
  · rw [Basic.DensePolynomial.normalize_constant_of_ne originZero,
      Basic.DensePolynomial.constant_add_linear origin directionNonzero,
      Basic.DensePolynomial.add_constant_zero,
      Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero]

end Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Coordinate

end
