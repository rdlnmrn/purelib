module

public import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Negating the argument of a finite Gaussian coefficient polynomial -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Negation

open Purelib
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Substitute the negative coordinate using two retained finite quarter-turn folds.

Both folds consume their actual coefficient tables. Their certified composition
sends the argument to its negative, preserves the original natural degree and
requires no matrix elimination or root selection.
-/
@[expose] def negateVariable (polynomial : CoefficientPolynomial) : CoefficientPolynomial :=
  QuarterTurn.quarterTurn (QuarterTurn.quarterTurn polynomial)

/-- Two quarter turns send the same original Gaussian argument to its negative. -/
private theorem twice (point : Canonical) :
    (point * Data.Gaussian.Constants.imaginaryUnit) * Data.Gaussian.Constants.imaginaryUnit = -point := by
  apply Data.Gaussian.Basic.ext
  · change (point.re * 0 - point.im * 1) * 0 - (point.re * 1 + point.im * 0) * 1 = -point.re
    ring1
  · change (point.re * 0 - point.im * 1) * 1 + (point.re * 1 + point.im * 0) * 0 = -point.im
    ring1

/-- The substituted polynomial evaluates the original polynomial at the negative argument. -/
theorem eval (polynomial : CoefficientPolynomial) (point : Canonical) :
    (negateVariable polynomial).eval point = polynomial.eval (-point) := by
  rewrite [negateVariable, QuarterTurn.eval_quarterTurn, QuarterTurn.eval_quarterTurn, twice]
  rfl

/-- The transformed polynomial at a negative sample has the original polynomial residual reading. -/
theorem eval_neg (polynomial : CoefficientPolynomial) (point : Canonical) :
    (negateVariable polynomial).eval (-point) = polynomial.eval point := by
  rewrite [eval, neg_neg]
  rfl

/-- Negating the argument preserves natural degree for every retained polynomial, including zero. -/
theorem natDegree (polynomial : CoefficientPolynomial) :
    (negateVariable polynomial).natDegree = polynomial.natDegree := by
  cases coefficients : polynomial.normalize.coeffs with
  | nil =>
      unfold negateVariable QuarterTurn.quarterTurn
      rewrite [coefficients]
      change 0 = polynomial.normalize.coeffs.length - 1
      rewrite [coefficients]
      rfl
  | cons leading remaining =>
      have nonzero : polynomial.isZero = false := by
        change polynomial.normalize.coeffs.isEmpty = false
        rewrite [coefficients]
        rfl
      exact (QuarterTurn.quarterTurn_natDegree (QuarterTurn.quarterTurn polynomial)
        (QuarterTurn.quarterTurn_nonzero polynomial nonzero)).trans
        (QuarterTurn.quarterTurn_natDegree polynomial nonzero)

end Purelib.Polynomial.Dense.Gaussian.Substitution.Negation

end
