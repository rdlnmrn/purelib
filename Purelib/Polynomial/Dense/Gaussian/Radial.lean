module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Gaussian.Cast
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Composition
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

public section

/-!
# Finite radial bounds for a primitive factor

Integrate the finite polynomial u G(w u^e) on the displayed unit segment,
where e is one or two. The existing finite subdivision estimate gives a
bound for G(w) from its Euler differential expression. The auxiliary
polynomial is used only in the proof; executable callers retain their
original factor and a refinement-independent numerical ceiling.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Radial

open Purelib.Data
open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity (degree)

/-- The scaled coordinate monomial of degree one or two, selected by the ramification flag.

The point is the constant coefficient of one or two successive shifts, according to the retained Boolean branch. -/
@[expose] def monomial (point : Gaussian.Basic.Canonical) (ramified : Bool) : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical) :=
  if ramified then DensePolynomial.shift 1 (DensePolynomial.shift 1
    (DensePolynomial.constant point)) else DensePolynomial.shift 1
    (DensePolynomial.constant point)

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense in
/-- The retained monomial evaluates to the point times the selected power of its argument. -/
private theorem monomial_eval (point parameter : Gaussian.Basic.Canonical) (ramified : Bool) :
    (monomial point ramified).eval parameter = point * parameter ^ degree ramified := by
  cases ramified
  · change (DensePolynomial.shift 1 (DensePolynomial.constant point)).eval parameter = point *
      parameter ^ 1
    rw [DensePolynomial.eval_shift, DensePolynomial.eval_constant]
  · change (DensePolynomial.shift 1 (DensePolynomial.shift 1
      (DensePolynomial.constant point))).eval parameter = point * parameter ^ 2
    rw [DensePolynomial.eval_shift, DensePolynomial.eval_shift,
      DensePolynomial.eval_constant]
    ring1

/-- A Gaussian constant polynomial has zero evaluated derivative. -/
private theorem derivative_constant (point parameter : Gaussian.Basic.Canonical) :
    (Dense.Derivative.derivative (DensePolynomial.constant point)).eval parameter = 0 := by
  rw [Dense.Derivative.eval_derivative]
  change 0 * parameter + 0 = 0
  rw [Gaussian.Basic.zero_mul, Gaussian.Basic.add_zero]

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense in
/-- The monomial derivative times its argument equals the selected degree times its value. -/
private theorem monomial_euler (point parameter : Gaussian.Basic.Canonical) (ramified : Bool) :
    (Dense.Derivative.derivative (monomial point ramified)).eval parameter * parameter =
      (degree ramified : Gaussian.Basic.Canonical) * (monomial point ramified).eval parameter :=
        by
  cases ramified
  · change (Dense.Derivative.derivative (DensePolynomial.shift 1
        (DensePolynomial.constant point))).eval parameter * parameter =
      (1 : Gaussian.Basic.Canonical) *
        (DensePolynomial.shift 1 (DensePolynomial.constant point)).eval parameter
    rw [Dense.Derivative.eval_derivative_shift_one, derivative_constant,
      DensePolynomial.eval_shift, DensePolynomial.eval_constant]
    change (0 * parameter + point) * parameter = 1 * (point * parameter ^ 1)
    ring1
  · change (Dense.Derivative.derivative (DensePolynomial.shift 1
        (DensePolynomial.shift 1 (DensePolynomial.constant point)))).eval parameter * parameter
          =
      (2 : Gaussian.Basic.Canonical) *
        (DensePolynomial.shift 1 (DensePolynomial.shift 1
          (DensePolynomial.constant point))).eval parameter
    rw [Dense.Derivative.eval_derivative_shift_one, Dense.Derivative.eval_derivative_shift_one,
      derivative_constant, DensePolynomial.eval_shift,
      DensePolynomial.eval_shift, DensePolynomial.eval_constant]
    rw [DensePolynomial.eval_shift, DensePolynomial.eval_constant]
    change ((0 * parameter + point) * parameter + point * parameter ^ 1) * parameter =
      2 * (point * parameter ^ 1 * parameter ^ 1)
    ring1

/-- The radial polynomial u times G(point times u to the selected exponent).

Composition with the retained scaled monomial is followed by one coordinate shift. -/
@[expose] def radial (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
  (ramified : Bool)
  : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  DensePolynomial.shift 1 (Dense.Gaussian.Substitution.Composition.compose factor
    (monomial point ramified))

open Purelib.Polynomial.Dense.Gaussian.Primitive.Parity in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CanonicalScalar -> Gaussian in
open _root_.Purelib.Polynomial.Dense.Gaussian.Primitive.Parity renaming CoefficientPolynomial -> Dense in
/-- The radial derivative evaluates to the factor's Euler expression at the scaled power argument.

The selected exponent is one or two, and the finite composition derivative retains the same factor, point and parameter.
-/
theorem radial_derivative (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point parameter :
  Gaussian.Basic.Canonical)
  (ramified : Bool) :
    (Dense.Derivative.derivative (radial factor point ramified)).eval parameter =
      factor.eval (point * parameter ^ degree ramified) + (degree ramified : Gaussian.Basic.Canonical) *
        (point * parameter ^ degree ramified) * (Dense.Derivative.derivative factor).eval (point * parameter ^ degree
          ramified) := by
  rw [radial, Dense.Derivative.eval_derivative_shift_one,
    Dense.Gaussian.Substitution.Composition.derivative_compose, Dense.Gaussian.Substitution.Composition.eval_compose]
  calc
    _ = factor.eval ((monomial point ramified).eval parameter) +
        ((Dense.Derivative.derivative (monomial point ramified)).eval parameter * parameter) *
          (Dense.Derivative.derivative factor).eval ((monomial point ramified).eval parameter) :=
            by ring1
    _ = _ := by rw [monomial_euler, monomial_eval]

/-- The radial polynomial vanishes at zero.

Its outer coordinate shift forces this value independently of the retained factor and ramification flag. -/
theorem radial_zero (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
  (ramified : Bool)
  :
    (radial factor point ramified).eval 0 = 0 := by
  rw [radial, DensePolynomial.eval_shift, pow_one, Gaussian.Basic.mul_zero]

/-- At one, the radial polynomial recovers the factor evaluated at the retained point.

The scaled monomial at unit argument is the supplied point for either retained degree. -/
theorem radial_one (factor : Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical)
  (ramified : Bool) :
    (radial factor point ramified).eval 1 = factor.eval point := by
  rw [radial, DensePolynomial.eval_shift, pow_one, Gaussian.Basic.mul_one,
    Dense.Gaussian.Substitution.Composition.eval_compose, monomial_eval, one_pow,
    Gaussian.Basic.mul_one]

end Purelib.Polynomial.Dense.Gaussian.Radial
