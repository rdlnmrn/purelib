module
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Data.List.Fold
import Purelib.Tactic.Ring

/-! Finite Horner readback between ascending and descending rational coefficient lists. -/

public section

namespace Purelib.Polynomial.Dense.Rational.Evaluation.Ascending

open Purelib.Data.Rat

/-- Reversing an ascending rational coefficient list preserves its finite Horner reading. -/
theorem eval_reverse (point : Fraction.Rational) : ∀ coefficients : List Fraction.Rational,
    Basic.DensePolynomial.evalCoeffs point coefficients.reverse =
      Purelib.Polynomial.Ascending.Rational.Evaluation.scalarEvalCoefficients point coefficients := by
  intro coefficients
  unfold Basic.DensePolynomial.evalCoeffs
  rw [Purelib.Data.List.Fold.foldl_reverse]
  induction coefficients with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (tail.foldr (fun value state => state * point + value) 0) * point + head =
        head + point * Purelib.Polynomial.Ascending.Rational.Evaluation.scalarEvalCoefficients point tail
      rw [inductionHypothesis]
      ring1

end Purelib.Polynomial.Dense.Rational.Evaluation.Ascending

end
