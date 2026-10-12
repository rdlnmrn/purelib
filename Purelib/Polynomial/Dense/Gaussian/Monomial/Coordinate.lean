module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

/-!
# The Gaussian coordinate polynomial

The original descending coefficient pair one and zero represents the coordinate
polynomial. Its evaluation, nonzero test and degree are direct finite statements.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate

open Purelib.Data
open Purelib.Polynomial

/-- The executable coordinate polynomial Z.

The original descending coefficient list is exactly one followed by zero. -/
@[expose] public def coordinatePolynomial : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) := ⟨[1, 0]⟩

/-- The coordinate polynomial evaluates to its input.

The two original Horner steps start at zero and retain the input point through
multiplication by one and addition of zero. -/
@[simp] public theorem coordinatePolynomial_eval (z : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial.eval z = z := by
  change ((0 : Gaussian.Basic.Canonical) * z + 1) * z + 0 = z
  rewrite [Gaussian.Basic.zero_mul, Gaussian.Basic.zero_add,
    Gaussian.Basic.one_mul, Gaussian.Basic.add_zero]
  exact Eq.refl _

section
/-- The Gaussian coordinate polynomial is not zero. -/
public theorem coordinatePolynomial_isZero_false :
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial.isZero = false := by decide
/-- The Gaussian coordinate polynomial has degree one. -/
public theorem coordinatePolynomial_natDegree :
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial.natDegree = 1 := by decide
end

end Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
