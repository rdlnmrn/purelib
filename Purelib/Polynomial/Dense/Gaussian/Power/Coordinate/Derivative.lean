module

public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Algebra.Ring.IntCast
import Purelib.Tactic.Ring

/-! # The original coordinate-power polynomial's spatial derivative

The original finite multiplication construction and executable Horner
derivative give the degree times the preceding coordinate power. The integer
coefficient uses the original Gaussian cast and its owned scalar laws.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Power.Coordinate

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense

/-- The original coordinate polynomial's executable derivative is the original constant-one polynomial. -/
private theorem coordinate_derivative :
    GCD.derivative Monomial.Coordinate.coordinatePolynomial = Basic.constantOnePolynomial := by decide +kernel

/-- The positive coordinate-power derivative evaluates to its exact degree coefficient times the previous power.

The proof follows the retained multiplication program with the original
Horner product rule. Every coefficient increment uses the owned integer cast
law on the original Gaussian coefficient field.
-/
theorem derivative_eval (degree : Nat) (point : Canonical) :
    (GCD.derivative (coordinatePositivePower degree)).eval point =
      (Int.ofNat (degree + 1) : Canonical) * point ^ degree := by
  induction degree with
  | zero =>
      change (GCD.derivative Monomial.Coordinate.coordinatePolynomial).eval point = _
      rewrite [coordinate_derivative, Evaluation.constantOnePolynomial_eval, pow_zero, Data.Gaussian.Basic.mul_one]
      exact (show (Int.ofNat 1 : Canonical) = 1 from by decide +kernel).symm
  | succ degree inductionHypothesis =>
      rewrite [coordinatePositivePower]
      change (Derivative.derivative (coordinatePositivePower degree * Monomial.Coordinate.coordinatePolynomial)).eval
        point = _
      rewrite [Derivative.eval_derivative_mul]
      change (GCD.derivative (coordinatePositivePower degree)).eval point *
        Monomial.Coordinate.coordinatePolynomial.eval point +
        (coordinatePositivePower degree).eval point * (GCD.derivative Monomial.Coordinate.coordinatePolynomial).eval
          point = _
      rewrite [inductionHypothesis, Monomial.Coordinate.coordinatePolynomial_eval, coordinatePositivePower_eval,
        coordinate_derivative, Evaluation.constantOnePolynomial_eval]
      have degreeCoefficient : (Int.ofNat (degree + 1 + 1) : Canonical) = (Int.ofNat (degree + 1) : Canonical) + 1 := by
        change ((Int.ofNat (degree + 1) + 1 : Int) : Canonical) = _
        exact (Algebra.Ring.IntCast.add (Int.ofNat (degree + 1)) 1).trans
          (congrArg (fun coefficient : Canonical => (Int.ofNat (degree + 1) : Canonical) + coefficient)
            (show ((1 : Int) : Canonical) = 1 from by decide +kernel))
      rewrite [degreeCoefficient, pow_succ]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
