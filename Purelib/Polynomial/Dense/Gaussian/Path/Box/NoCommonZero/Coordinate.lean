module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Components.Nonzero
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Rational.Affine.Axis
public import Purelib.Geometry.Rational.Box.Subdivision
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Pair.NoCommonZero
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Coordinate

/-- Every positive coordinate power is pointwise nonzero on the boundary of
a positive symmetric constructive square. -/
theorem
  coordinatePositivePower_symmetric_boundaryCoprime
    {R : Fraction.Rational} (positive : 0 < R) (n : Nat) :
    Dense.Gaussian.Path.Box.NoCommonZero.BoundaryCoprime (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
      (Box.symmetric R positive.le) := open Purelib.Data in by
  have rNonzero : R ≠ 0 := positive.ne'
  have negativeRNonzero : -R ≠ 0 := by
    intro negativeZero
    have positiveZero := congrArg Neg.neg negativeZero
    simp only [_root_.neg_neg, neg_zero] at positiveZero
    exact rNonzero positiveZero
  constructor
  · change (PolynomialEdge.ofLine
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
      (Gaussian.Cast.Imaginary.horizontalBase (-R)) Gaussian.Constants.horizontalDirection (-R) R).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Affine.Axis.line_horizontal, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _
      (Purelib.Data.Gaussian.Components.Nonzero.point_ne_zero_of_im_ne_zero t (-R) negativeRNonzero) _
  · change (PolynomialEdge.ofLine
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
      (Gaussian.Cast.Winding.verticalBase R) Gaussian.Constants.imaginaryUnit (-R) R).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Affine.Axis.line_vertical, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _
      (Purelib.Data.Gaussian.Components.Nonzero.point_ne_zero_of_re_ne_zero R t rNonzero) _
  · change (PolynomialEdge.ofLine
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
      (Gaussian.Cast.Imaginary.horizontalBase R) Gaussian.Constants.horizontalDirection R (-R)).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Affine.Axis.line_horizontal, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _
      (Purelib.Data.Gaussian.Components.Nonzero.point_ne_zero_of_im_ne_zero t R rNonzero) _
  · change (PolynomialEdge.ofLine
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower n)
      (Gaussian.Cast.Winding.verticalBase (-R)) Gaussian.Constants.imaginaryUnit R (-R)).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Affine.Axis.line_vertical, Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval]
    exact Gaussian.Power.pow_ne_zero_direct _
      (Purelib.Data.Gaussian.Components.Nonzero.point_ne_zero_of_re_ne_zero (-R) t negativeRNonzero) _
end Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Coordinate

end
