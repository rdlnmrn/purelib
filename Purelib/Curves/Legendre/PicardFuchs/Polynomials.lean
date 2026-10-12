module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Curves.Legendre.Paths
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Legendre

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

section
@[expose] public section

/-!
# Finite Legendre Gauss--Manin reduction

The parameter derivatives of the Legendre differential are reduced here by
literal dense-polynomial arithmetic.  All denominators are cleared before an
identity is stated.  The exact terms retain their displayed primitive
numerators, so the later period layer can discharge them using finite endpoint
telescoping rather than differentiation under a completed integral sign.
-/

namespace Purelib.Curves.Legendre.PicardFuchs.Polynomials

/-! ## Displayed polynomial data -/

/-- The parameter-independent factor `g(x) = x(x-1)`. -/
def basePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[1,
  -1, 0]⟩

/-- The numerator `x g(x)` of the parameter derivative of `x dx/y`. -/
def weightedBasePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  := ⟨[1, -1, 0, 0]⟩

/-- The explicit spatial derivative of the Legendre cubic. -/
def spatialDerivativePolynomial (parameter :
  Data.Gaussian.Basic.Canonical) :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[3, -2 * (1 + parameter), parameter]⟩

/-- The exact primitive numerator used in the first connection row. -/
def firstPrimitivePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial := ⟨[2, -2, 0]⟩

/-- The exact primitive numerator used in the second connection row. -/
def secondPrimitivePolynomial (parameter :
  Data.Gaussian.Basic.Canonical) :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[2 * parameter, -2 * parameter, 0]⟩

/-- The exact primitive numerator for the second-order scalar equation. -/
def picardFuchsPrimitivePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[2, -4, 2, 0, 0]⟩

/-- The base polynomial evaluates to x times x minus one. -/
@[simp] theorem basePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.basePolynomial.eval point = point * (point - 1) := by
  unfold PicardFuchs.Polynomials.basePolynomial DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The weighted base polynomial evaluates to x times the base quadratic. -/
@[simp] theorem weightedBasePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.weightedBasePolynomial.eval point =
      point * (point * (point - 1)) := by
  unfold PicardFuchs.Polynomials.weightedBasePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The displayed spatial derivative evaluates to the explicit quadratic in the point and parameter. -/
@[simp] theorem spatialDerivativePolynomial_eval
    (parameter point : Data.Gaussian.Basic.Canonical) :
    (spatialDerivativePolynomial parameter).eval point =
      3 * point * point - 2 * (1 + parameter) * point + parameter := by
  unfold spatialDerivativePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The displayed quadratic agrees pointwise with the finite automatic derivative of the displayed Legendre cubic.
Pointwise equality is the exact interface consumed by finite quadrature and avoids any appeal to polynomial function
extensionality. -/
theorem spatialDerivativePolynomial_matches_automatic
    (parameter point : Data.Gaussian.Basic.Canonical) :
    (spatialDerivativePolynomial parameter).eval point =
      (Purelib.Polynomial.Dense.Gaussian.GCD.derivative (Purelib.Curves.Legendre.Paths.polynomial parameter)).eval point
        := by
  rw [spatialDerivativePolynomial_eval]
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold Paths.polynomial Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The first primitive numerator evaluates to twice the base quadratic. -/
@[simp] theorem firstPrimitivePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.firstPrimitivePolynomial.eval point = 2 * (point * (point - 1)) := by
  unfold PicardFuchs.Polynomials.firstPrimitivePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The second primitive numerator evaluates to twice the parameter times the base quadratic. -/
@[simp] theorem secondPrimitivePolynomial_eval
    (parameter point : Data.Gaussian.Basic.Canonical) :
    (secondPrimitivePolynomial parameter).eval point =
      2 * parameter * (point * (point - 1)) := by
  unfold PicardFuchs.Polynomials.secondPrimitivePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The scalar-equation primitive numerator evaluates to twice the square of the base quadratic. -/
@[simp] theorem picardFuchsPrimitivePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial.eval point =
      2 * (point * (point - 1)) ^ 2 := by
  unfold PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the first exact primitive is the displayed linear polynomial. -/
theorem firstPrimitiveDerivative_eval (point :
  Data.Gaussian.Basic.Canonical) :
    (Purelib.Polynomial.Dense.Gaussian.GCD.derivative
      firstPrimitivePolynomial).eval point =
      4 * point - 2 := by
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold PicardFuchs.Polynomials.firstPrimitivePolynomial
    Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the second exact primitive retains its displayed parameter factor. -/
theorem secondPrimitiveDerivative_eval (parameter point :
  Data.Gaussian.Basic.Canonical) :
    (Purelib.Polynomial.Dense.Gaussian.GCD.derivative
      (secondPrimitivePolynomial parameter)).eval point =
        parameter * (4 * point - 2) := by
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold PicardFuchs.Polynomials.secondPrimitivePolynomial
    Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Automatic differentiation of the scalar-equation primitive numerator. -/
theorem picardFuchsPrimitiveDerivative_eval (point :
  Data.Gaussian.Basic.Canonical) :
    (Purelib.Polynomial.Dense.Gaussian.GCD.derivative
      picardFuchsPrimitivePolynomial).eval point =
        4 * (point * (point - 1)) * (2 * point - 1) := by
  unfold GCD.derivative
  rw [Derivative.eval_derivative]
  unfold PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial
    Derivative.evalDerivativeCoeffs
    Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-! ## Fraction-free connection identities -/

/-- Evaluate the factored Legendre cubic at the exact parameter and point. -/
def curveValue (parameter point : Data.Gaussian.Basic.Canonical)
  : Data.Gaussian.Basic.Canonical :=
  point * (point - 1) * (point - parameter)

/-- Evaluate the parameter-independent quadratic x times x minus one. -/
def baseValue (point : Data.Gaussian.Basic.Canonical) :
  Data.Gaussian.Basic.Canonical := point * (point - 1)

/-- Evaluate the explicit spatial derivative of the Legendre cubic. -/
def spatialDerivativeValue (parameter point :
  Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  3 * point * point - 2 * (1 + parameter) * point + parameter
end Purelib.Curves.Legendre.PicardFuchs.Polynomials

end

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Curves.Legendre.PicardFuchs.Polynomials

/-- The dense polynomial square of x times x minus one. -/
def squaredBasePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  := ⟨[1, -2, 1, 0, 0]⟩

/-- The dense polynomial x times the square of x times x minus one. -/
def weightedSquaredBasePolynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[1, -2, 1, 0, 0, 0]⟩

/-- The squared base polynomial evaluates to the square of the base quadratic. -/
@[simp] theorem squaredBasePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.squaredBasePolynomial.eval point = (point * (point - 1)) ^ 2 := by
  unfold PicardFuchs.Polynomials.squaredBasePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The weighted squared base polynomial evaluates to x times the squared base quadratic. -/
@[simp] theorem weightedSquaredBasePolynomial_eval (point :
  Data.Gaussian.Basic.Canonical) :
    Curves.Legendre.PicardFuchs.Polynomials.weightedSquaredBasePolynomial.eval point =
      point * (point * (point - 1)) ^ 2 := by
  unfold PicardFuchs.Polynomials.weightedSquaredBasePolynomial
    DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

end Purelib.Curves.Legendre.PicardFuchs.Polynomials

end
