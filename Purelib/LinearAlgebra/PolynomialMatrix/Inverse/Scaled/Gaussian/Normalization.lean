module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Resource
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Mathlib.Algebra.GroupWithZero.NeZero

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Normalization

open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Resource

section
/-- The scalar returned by the Gaussian polynomial inverse recursion is normalized.

The empty case is the unit polynomial and every positive-dimensional scalar is a normalized product. -/
private theorem
  scaledInverseScalar_normalized
  :
    ∀ (count : Nat) (matrix :
      Purelib.LinearAlgebra.PolynomialMatrix.Basic.Matrix Purelib.Data.Gaussian.Basic.Canonical
        count),
      ((Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count
        matrix).scalar
          ).normalize =
        (Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData count
          matrix).scalar
  | 0, _ => by
      simp only [Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData]
      exact Dense.Basic.DensePolynomial.normalize_constant_of_ne one_ne_zero
  | count + 1, matrix => by
      dsimp only [Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData]
      exact Dense.Basic.DensePolynomial.normalize_mul _ _
end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Normalization

end
