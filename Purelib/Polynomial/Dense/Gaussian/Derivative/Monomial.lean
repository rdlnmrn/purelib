module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Derivatives of Gaussian coordinate powers

The original polynomial derivative and scalar Horner programs evaluate the
coordinate polynomial and its retained positive powers. The original power
indices and Gaussian natural casts appear in the resulting scalar identities.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Derivative.Monomial

open Purelib.Data
open Purelib.Polynomial

/-- The formal derivative of the coordinate polynomial evaluates to one.

The original two-entry scalar derivative fold retains a zero initial state
and the original coefficients one and zero. -/
public theorem derivative_coordinatePolynomial_eval (point : Gaussian.Basic.Canonical) :
    (Dense.Derivative.derivative
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial).eval point = 1 := by
  rewrite [Dense.Derivative.eval_derivative]
  change ((0 : Gaussian.Basic.Canonical) * point + 0) * point +
    (0 * point + 1) = 1
  ring1

open Purelib.Algebra in
/-- The derivative of the positive coordinate power evaluates to its index times the preceding power.

The product rule follows the original recursive multiplication program. Its
Gaussian natural cast increments through the original additive cast certificate. -/
public theorem derivative_coordinatePositivePower_eval : ∀ exponent : Nat,
    ∀ point : Gaussian.Basic.Canonical,
    (Dense.Derivative.derivative
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower exponent)).eval point =
      ((exponent + 1 : Nat) : Gaussian.Basic.Canonical) * point ^ exponent
  | 0, point => by
      change
        (Dense.Derivative.derivative
          Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial).eval point =
            (1 : Gaussian.Basic.Canonical) * point ^ 0
      rewrite [Dense.Gaussian.Derivative.Monomial.derivative_coordinatePolynomial_eval, pow_zero]
      exact (Gaussian.Basic.mul_one (1 : Gaussian.Basic.Canonical)).symm
  | exponent + 1, point => by
      rw [Dense.Gaussian.Power.Coordinate.coordinatePositivePower,
        Dense.Derivative.eval_derivative_mul,
        Purelib.Polynomial.Dense.Gaussian.Derivative.Monomial.derivative_coordinatePositivePower_eval exponent,
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval,
        Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval,
        Dense.Gaussian.Derivative.Monomial.derivative_coordinatePolynomial_eval]
      change
        (((exponent + 1 : Nat) : Gaussian.Basic.Canonical) * point ^ exponent) * point +
            point ^ (exponent + 1) * 1 =
          ((exponent + 1 + 1 : Nat) : Gaussian.Basic.Canonical) * point ^ (exponent + 1)
      rw [Gaussian.Basic.mul_one, pow_succ]
      have increment : ((exponent + 1 + 1 : Nat) : Gaussian.Basic.Canonical) =
          ((exponent + 1 : Nat) : Gaussian.Basic.Canonical) + 1 := by
        rewrite [NatCast.add (exponent + 1) 1, Nat.cast_one]
        exact Eq.refl _
      rewrite [increment]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Derivative.Monomial
