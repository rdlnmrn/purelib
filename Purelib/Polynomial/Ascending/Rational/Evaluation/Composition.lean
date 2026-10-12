module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.Composition
public import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat

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

namespace Purelib.Polynomial.Ascending.Rational.Evaluation.Composition

/-- Rational scalar evaluation commutes with finite polynomial composition. -/
theorem scalarEval_compose (radius :
  Fraction.Rational) (outer inner : Ascending.Rational.Basic.CoefficientPolynomial) :
    Ascending.Rational.Evaluation.scalarEval radius (Ascending.Rational.Composition.compose outer inner) =
      Ascending.Rational.Evaluation.scalarEval (Ascending.Rational.Evaluation.scalarEval radius inner) outer := open
        Purelib.Data in by
  have evaluated := Ascending.Rational.GaussianEvaluation.Composition.eval_compose outer inner
    (Gaussian.RationalEmbedding.ComplexLog.scalar radius)
  rw [Ascending.Rational.GaussianEvaluation.eval_scalar, Ascending.Rational.GaussianEvaluation.eval_scalar,
    Ascending.Rational.GaussianEvaluation.eval_scalar] at evaluated
  exact congrArg Gaussian.Basic.re evaluated
end Purelib.Polynomial.Ascending.Rational.Evaluation.Composition

end
