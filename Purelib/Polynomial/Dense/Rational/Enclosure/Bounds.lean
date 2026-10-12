module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Arithmetic
import Purelib.Data.Rat.Interval.Arithmetic.Bounds
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
public import Purelib.Polynomial.Dense.Rational.Enclosure.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Bounds

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

namespace Purelib.Polynomial.Dense.Rational.Enclosure.Bounds

/-- One interval Horner step is bounded by the squared scalar Horner step.

The accumulator enclosure may already be bounded by a larger retained scalar ceiling. -/
theorem step_squareBound_le (parameters accumulator :
  Data.Rat.Interval.Bounds) (coefficient : Fraction.Rational)
    {bound : Fraction.Rational} (accumulatorBound : accumulator.squareBound ≤ bound) :
    (Dense.Rational.Enclosure.Basic.step parameters accumulator coefficient).squareBound ≤
      Dense.Rational.Bounds.Horner.evalSqBoundStep parameters.squareBound bound coefficient := by
  have productBound := (Interval.Arithmetic.Bounds.mul_squareBound_le accumulator parameters).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      accumulatorBound parameters.squareBound_nonneg)
  exact (Interval.Arithmetic.Bounds.addConstant_squareBound_le _ coefficient).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add productBound le_rfl) (by decide))

end Purelib.Polynomial.Dense.Rational.Enclosure.Bounds

section
namespace Purelib.Polynomial.Dense.Rational.Enclosure.Bounds

open _root_.Purelib.Polynomial.Geometry.PolynomialEnclosures
/-- Transport a squared accumulator bound through the entire finite interval Horner fold. -/
private theorem fold_squareBound_le
  (coefficients : List Fraction.Rational) (parameters accumulator : Data.Rat.Interval.Bounds)
    {bound : Fraction.Rational} (accumulatorBound : accumulator.squareBound ≤ bound) :
    (coefficients.foldl (Dense.Rational.Enclosure.Basic.step parameters) accumulator).squareBound ≤
      coefficients.foldl (Dense.Rational.Bounds.Horner.evalSqBoundStep parameters.squareBound) bound := by
  induction coefficients generalizing accumulator bound with
  | nil => exact accumulatorBound
  | cons coefficient rest inductionHypothesis =>
      exact inductionHypothesis (Dense.Rational.Enclosure.Basic.step parameters accumulator coefficient)
        (step_squareBound_le parameters accumulator coefficient accumulatorBound)
end Purelib.Polynomial.Dense.Rational.Enclosure.Bounds
end

namespace Purelib.Polynomial.Dense.Rational.Enclosure.Bounds

/-- The interval enclosure never worsens the old squared Horner ceiling.
Downstream executable code may therefore drop that redundant calculation,
rather than compute both estimates merely to choose their minimum. -/
theorem evaluate_squareBound_le (polynomial :
  Dense.Rational.Basic.CoordinatePolynomial) (parameters : Data.Rat.Interval.Bounds) :
    (Dense.Rational.Enclosure.Basic.evaluate polynomial parameters).squareBound ≤
      Dense.Rational.Bounds.Horner.evalSqBound polynomial parameters :=
  fold_squareBound_le polynomial.coeffs parameters
    (Interval.Arithmetic.constant 0) (show (Interval.Arithmetic.constant 0).squareBound ≤ 0 by decide)
end Purelib.Polynomial.Dense.Rational.Enclosure.Bounds

end
