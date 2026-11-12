module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Composition
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition

/-- Gaussian evaluation commutes with Horner substitution of a finite outer table.

Evaluate the inner polynomial first, then use that Gaussian value as the argument of the outer coefficient list. -/
theorem eval_composeCoefficients (inner :
  Basic.CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    ∀ outer,
      eval (Composition.composeCoefficients outer inner) z =
        evalCoefficients (eval inner z)
          outer
  | [] => rfl
  | coefficient :: remaining => by
      rw [Composition.composeCoefficients, eval_add,
        eval_mul,
        eval_composeCoefficients inner z remaining]
      change
        (Gaussian.Scale.scale coefficient 1 + z * 0) +
            eval inner z * evalCoefficients
              (eval inner z) remaining =
          Gaussian.Scale.scale coefficient 1 +
            eval inner z * evalCoefficients
              (eval inner z) remaining
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1

/-- Evaluating a composition equals evaluating the outer polynomial at the inner value. -/
@[simp] theorem eval_compose (outer inner :
  Basic.CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    eval (Composition.compose outer inner) z =
      eval outer (eval inner z) :=
  eval_composeCoefficients inner z outer.coefficients
end Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition

end
