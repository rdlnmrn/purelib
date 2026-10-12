module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Arithmetic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite interval Horner enclosures

Interval arithmetic retains signs and exact constant terms instead of
introducing a factor of two at every squared Horner step.  Four endpoint
products enclose multiplication; a finite coefficient fold then encloses
every displayed parameter in the retained interval.  A failed positive gap
is only an inconclusive enclosure, not a claim that the polynomial has a root.

This module adds no dependencies beyond the existing finite path-clearance
algebra.  It uses neither extrema over a completed interval nor a root search.
-/

namespace Purelib.Polynomial.Dense.Rational.Enclosure.Basic

/-- One interval Horner step: multiply by the parameter interval and add the exact coefficient. -/
def step (parameters accumulator :
  Data.Rat.Interval.Bounds) (coefficient : Fraction.Rational) : Data.Rat.Interval.Bounds :=
  Interval.Arithmetic.addConstant (Interval.Arithmetic.mul accumulator parameters) coefficient

/-- An interval Horner step contains the corresponding scalar step.

The scalar parameter and accumulator must lie in their respective input intervals. -/
theorem step_contains (parameters accumulator :
  Data.Rat.Interval.Bounds) (coefficient : Fraction.Rational)
    {parameter value : Fraction.Rational} (parameterInside : parameters.Contains parameter)
    (valueInside : accumulator.Contains value) :
    (step parameters accumulator coefficient).Contains (value * parameter + coefficient)
      :=
  Interval.Arithmetic.addConstant_contains _ _ (Interval.Arithmetic.mul_contains accumulator
    parameters valueInside parameterInside)

/-- Horner evaluation of the coefficient list in the finite interval algebra.
The caller can retain this result and reuse it for both upper and lower bounds. -/
def evaluate (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial) (parameters : Data.Rat.Interval.Bounds) :
  Data.Rat.Interval.Bounds :=
  polynomial.coeffs.foldl (step parameters) (Interval.Arithmetic.constant 0)

end Purelib.Polynomial.Dense.Rational.Enclosure.Basic

section
namespace Purelib.Polynomial.Dense.Rational.Enclosure.Basic

open _root_.Purelib.Polynomial.Geometry.PolynomialEnclosures
/-- A finite interval Horner fold encloses its scalar fold.

The parameter stays in the retained parameter interval and the initial scalar value lies in the initial accumulator
interval. -/
private theorem fold_contains
  (coefficients : List Fraction.Rational) (parameters : Data.Rat.Interval.Bounds)
    {parameter : Fraction.Rational} (parameterInside : parameters.Contains parameter)
    (accumulator : Data.Rat.Interval.Bounds) {value : Fraction.Rational} (valueInside : accumulator.Contains
      value) :
    (coefficients.foldl (step parameters) accumulator).Contains
      (coefficients.foldl (fun current coefficient => current * parameter + coefficient) value) := by
  induction coefficients generalizing accumulator value with
  | nil => exact valueInside
  | cons coefficient rest inductionHypothesis =>
      exact inductionHypothesis (step parameters accumulator coefficient)
        (step_contains parameters accumulator coefficient parameterInside valueInside)
end Purelib.Polynomial.Dense.Rational.Enclosure.Basic
end

namespace Purelib.Polynomial.Dense.Rational.Enclosure.Basic

/-- The computed Horner interval contains every polynomial value over the parameter interval. -/
theorem evaluate_contains (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial) (parameters : Data.Rat.Interval.Bounds)
    {parameter : Fraction.Rational} (inside : parameters.Contains parameter) :
    (evaluate polynomial parameters).Contains (polynomial.eval parameter) :=
  fold_contains polynomial.coeffs parameters inside
    (Interval.Arithmetic.constant 0) ⟨le_rfl, le_rfl⟩
end Purelib.Polynomial.Dense.Rational.Enclosure.Basic

end
