module
public import Purelib.Polynomial.Dense.Gaussian.Coefficients.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic

/-!
# Multiplication by the Gaussian coordinate polynomial

The two-term polynomial [2, 0] multiplies the retained Gaussian polynomial.
Its scalar readback is twice the parameter times the same polynomial value.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate

open Purelib.Data
open Purelib.Polynomial

/-- Multiply a Gaussian polynomial by twice the coordinate polynomial.

The retained two-term coordinate polynomial [2, 0] multiplies the supplied
finite coefficient polynomial. -/
@[expose] def SeparatedVariables.twiceShift (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Coefficients.Constants.SeparatedVariables.twiceParameter * p

/-- Twice-coordinate multiplication evaluates to twice the argument times the original polynomial value.

Horner evaluation of [2, 0] gives twice the supplied argument. Evaluation
then multiplies the same retained polynomial value. -/
@[simp] theorem eval_twiceShift (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (t :
  Gaussian.Basic.Canonical) :
    (Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift p).eval t = 2 * t * p.eval t := by
  rw [Dense.Gaussian.Multiplication.Coordinate.SeparatedVariables.twiceShift, Dense.Basic.DensePolynomial.eval_mul]
  change ((⟨[2, 0]⟩ : Basic.CanonicalCoefficients.CoefficientPolynomial).eval t) * p.eval t = _
  change ((0 * t + 2) * t + 0) * p.eval t = 2 * t * p.eval t
  rw [zero_mul, zero_add, add_zero]

end Purelib.Polynomial.Dense.Gaussian.Multiplication.Coordinate

end
