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
    Dense.Gaussian.Substitution.Affine.composeLine Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial origin
      direction =
      ⟨[direction, origin]⟩ := by
  rw [Dense.Gaussian.Substitution.Affine.composeLine, Dense.Gaussian.Substitution.Affine.composeLineCoeffs]
  simp only [Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial, List.foldl_cons, List.foldl_nil]
  rw [Dense.Gaussian.Substitution.Affine.mulLine_zero, Dense.Basic.DensePolynomial.zero_add_normalize,
    Dense.Basic.DensePolynomial.normalize_constant_of_ne one_ne_zero]
  rw [Dense.Gaussian.Substitution.Affine.mulLine, Dense.Basic.DensePolynomial.scale_constant,
    Dense.Basic.DensePolynomial.scale_constant,
    Gaussian.Basic.mul_one,
    Gaussian.Basic.mul_one,
    Dense.Basic.DensePolynomial.normalize_constant_of_ne directionNonzero,
    Dense.Basic.DensePolynomial.shift_one_constant_of_ne directionNonzero]
  by_cases originZero : origin = 0
  · subst origin
    rw [Dense.Basic.DensePolynomial.normalize_constant_zero, Dense.Basic.DensePolynomial.zero_add_normalize,
      Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero,
      Dense.Basic.DensePolynomial.add_constant_zero,
      Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero]
  · rw [Dense.Basic.DensePolynomial.normalize_constant_of_ne originZero,
      Dense.Basic.DensePolynomial.constant_add_linear origin directionNonzero,
      Dense.Basic.DensePolynomial.add_constant_zero,
      Dense.Basic.DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero]

end Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Coordinate

end
