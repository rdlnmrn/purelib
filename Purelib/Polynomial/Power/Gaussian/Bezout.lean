module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Gaussian.Derivative.Degree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
public import Purelib.Polynomial.Power.Gaussian
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Bézout identities for Gaussian power polynomials

The two finite cofactor polynomials certify coprimality of Z^degree minus
a nonzero parameter with its formal derivative. The supplied positive degree
and Gaussian inverse operations determine the same coefficient tables.
-/

namespace Purelib.Polynomial.Power.Gaussian.Bezout

open Purelib.Data
open Purelib.Polynomial
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The constant left Bézout cofactor is the negated inverse parameter.

Its singleton descending coefficient table is retained directly, including
the zero-parameter case where the inverse has its usual field value. -/
@[expose] public def bezoutLeft (parameter : Canonical) : (Dense.Basic.DensePolynomial Canonical) :=
  Dense.Basic.DensePolynomial.constant (-parameter⁻¹)

/-- The right Bézout cofactor scales the coordinate by inverse parameter and degree.

The supplied positive degree remains the exponent owner. Its Gaussian cast
and the parameter use the retained inverse and scalar-multiplication operations. -/
@[expose] public def bezoutRight (parameter : Canonical) (degree : Nat.Positive.RootDegree) :
    (Dense.Basic.DensePolynomial Canonical) :=
  Dense.Basic.DensePolynomial.scale (parameter⁻¹ * (degree.value : Canonical)⁻¹)
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial

/-- The displayed cofactors give a Bézout identity for a nonzero power-family parameter.

At every Gaussian point, their products with the positive-degree power
polynomial and its formal derivative sum to one. The degree and parameter
nonvanishing certificates justify the two scalar inverse cancellations. -/
public theorem bezout_identity
    {parameter : Canonical} (parameterNonzero : parameter ≠ 0)
    (degree : Nat.Positive.RootDegree) (point : Canonical) :
    (bezoutLeft parameter).eval point *
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).eval point +
      (bezoutRight parameter degree).eval point *
        (Dense.Gaussian.GCD.derivative
          (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree)).eval point = 1 := open
            Purelib.Algebra.Field in
            by
  have degreeNonzero : (degree.value : Canonical) ≠ 0 :=
    Dense.Gaussian.Derivative.Degree.gaussian_natCast_ne_zero degree.positive
  have parameterCancel : parameter⁻¹ * parameter = 1 := by
    rw [Gaussian.Basic.mul_comm]
    exact ExplicitField.mul_inv_cancel parameter parameterNonzero
  have degreeCancel :
      (degree.value : Canonical)⁻¹ * (degree.value : Canonical) = 1 := by
    rw [Gaussian.Basic.mul_comm]
    exact ExplicitField.mul_inv_cancel _ degreeNonzero
  simp only [bezoutLeft, bezoutRight, Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_scale,
    Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
    Power.Gaussian.derivative_eval]
  have powerStep :
      point ^ (degree.value - 1) * point = point ^ degree.value := by
    have predecessor : degree.value - 1 + 1 = degree.value :=
      (Nat.add_comm _ _).trans (Nat.Subtraction.add_sub_of_le degree.positive)
    rw [← pow_succ, predecessor]
  calc
    -parameter⁻¹ * (point ^ degree.value - parameter) +
          parameter⁻¹ * (degree.value : Canonical)⁻¹ * point *
            ((degree.value : Canonical) * point ^ (degree.value - 1)) =
        parameter⁻¹ * parameter +
          parameter⁻¹ *
            ((degree.value : Canonical)⁻¹ * (degree.value : Canonical)) *
              point ^ degree.value -
          parameter⁻¹ * point ^ degree.value := by
      rw [← powerStep]
      ring1
    _ = 1 := by rw [parameterCancel, degreeCancel]; ring1

/-- A positive-degree power polynomial fails the executable zero test.

Its retained degree certificate is strictly positive for every parameter,
so its normalized descending coefficient list cannot be empty. -/
public theorem polynomial_nonzero (parameter : Canonical) (degree : Nat.Positive.RootDegree) :
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree).isZero = false :=
  Dense.Gaussian.Degree.Linear.isZero_false_of_natDegree_pos (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact degree.positive)

end Purelib.Polynomial.Power.Gaussian.Bezout
