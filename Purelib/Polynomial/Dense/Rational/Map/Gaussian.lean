module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Cast
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Rational.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Taylor orientation for coordinate polynomials

A coordinate polynomial is embedded coefficientwise into the existing
Gaussian-polynomial Taylor program.  Restricting that finite program to the
degenerate real box over a rational interval gives a square-root-free Taylor
bound for the original coordinate polynomial.  The intended consumer is the
squarefree Sturm-event classifier: a displayed rational zero in a sufficiently
small cell has an oriented endpoint crossing, without a root set, an ordered
completion, or a mean-value theorem.
-/

namespace Purelib.Polynomial.Dense.Rational.Map.Gaussian

/-- Coefficientwise real-axis inclusion of a coordinate polynomial. -/
def gaussianPolynomial (p :
  CoordinatePolynomial) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical)
  :=
  ⟨p.coeffs.map Gaussian.Cast.CoordinateTaylor.ofCoordinate⟩

end Purelib.Polynomial.Dense.Rational.Map.Gaussian

section
namespace Purelib.Polynomial.Dense.Rational.Map.Gaussian

open _root_.Purelib.RootIsolation.Sturm.CoordinateTaylor
/-- Real-axis inclusion commutes with a Horner evaluation fold.

Both the evaluation point and initial accumulator are included coefficientwise into the Gaussian field. -/
private theorem foldl_eval_map
    (coefficients : List Fraction.Rational) (point accumulator : Fraction.Rational) :
    (coefficients.map Gaussian.Cast.CoordinateTaylor.ofCoordinate).foldl
        (fun value coefficient => value * Gaussian.Cast.CoordinateTaylor.ofCoordinate point + coefficient)
        (Gaussian.Cast.CoordinateTaylor.ofCoordinate accumulator) =
      Gaussian.Cast.CoordinateTaylor.ofCoordinate (coefficients.foldl
        (fun value coefficient => value * point + coefficient) accumulator) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons]
      rw [← Gaussian.Cast.ofCoordinate_mul, ← Gaussian.Cast.ofCoordinate_add]
      exact inductionHypothesis (accumulator * point + coefficient)
end Purelib.Polynomial.Dense.Rational.Map.Gaussian
end

namespace Purelib.Polynomial.Dense.Rational.Map.Gaussian

/-- Evaluate the Gaussian coefficient embedding on the real axis.

The result is the inclusion of the original rational polynomial value. -/
@[simp] theorem eval_gaussianPolynomial
    (p : CoordinatePolynomial) (point : Fraction.Rational) :
    (gaussianPolynomial p).eval (Gaussian.Cast.CoordinateTaylor.ofCoordinate point) =
      Gaussian.Cast.CoordinateTaylor.ofCoordinate (p.eval point) := by
  exact foldl_eval_map p.coeffs point 0

end Purelib.Polynomial.Dense.Rational.Map.Gaussian

section
namespace Purelib.Polynomial.Dense.Rational.Map.Gaussian

open _root_.Purelib.RootIsolation.Sturm.CoordinateTaylor
/-- Real-axis inclusion commutes with the paired value and derivative fold.

The identity retains both accumulators, so either component can be projected after evaluation. -/
private theorem foldl_evalDerivative_map
    (coefficients : List Fraction.Rational) (point value derivativeValue : Fraction.Rational) :
    (coefficients.map Gaussian.Cast.CoordinateTaylor.ofCoordinate).foldl
        (Dense.Derivative.evalDerivativeStep (Gaussian.Cast.CoordinateTaylor.ofCoordinate point))
        (Gaussian.Cast.CoordinateTaylor.ofCoordinate value, Gaussian.Cast.CoordinateTaylor.ofCoordinate derivativeValue)
          =
      let result := coefficients.foldl
        (Dense.Derivative.evalDerivativeStep point)
        (value, derivativeValue)
      (Gaussian.Cast.CoordinateTaylor.ofCoordinate result.1, Gaussian.Cast.CoordinateTaylor.ofCoordinate result.2) := by
  induction coefficients generalizing value derivativeValue with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.map_cons, List.foldl_cons,
        Dense.Derivative.evalDerivativeStep]
      rw [← Gaussian.Cast.ofCoordinate_mul, ← Gaussian.Cast.ofCoordinate_add,
        ← Gaussian.Cast.ofCoordinate_mul, ← Gaussian.Cast.ofCoordinate_add]
      exact inductionHypothesis
        (value * point + coefficient) (derivativeValue * point + value)
end Purelib.Polynomial.Dense.Rational.Map.Gaussian
end

namespace Purelib.Polynomial.Dense.Rational.Map.Gaussian

/-- Evaluate the derivative of the embedded polynomial on the real axis.

Its Gaussian value is the inclusion of the rational derivative value. -/
@[simp] theorem eval_derivative_gaussianPolynomial
    (p : CoordinatePolynomial) (point : Fraction.Rational) :
    (Dense.Derivative.derivative (gaussianPolynomial p)).eval
        (Gaussian.Cast.CoordinateTaylor.ofCoordinate point) =
      Gaussian.Cast.CoordinateTaylor.ofCoordinate ((Dense.Derivative.derivative p).eval point) := by
  rw [Dense.Derivative.eval_derivative,
    Dense.Derivative.eval_derivative]
  exact congrArg Prod.snd
    (foldl_evalDerivative_map p.coeffs point 0 0)
end Purelib.Polynomial.Dense.Rational.Map.Gaussian

end
