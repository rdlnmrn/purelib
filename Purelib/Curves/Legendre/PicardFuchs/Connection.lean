module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.PicardFuchs.Clearance
public import Purelib.Curves.Legendre.PicardFuchs.Polynomials
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Legendre

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Basic

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

namespace Purelib.Curves.Legendre.PicardFuchs.Connection

/-- First row of the fraction-free Gauss--Manin connection. After division by `2 y^3`, this is `D ∂λ(dx/y) = λ dx/y - x
dx/y + d(2x(x-1)/y)`. -/
theorem firstConnection_cleared (parameter point :
  Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Legendre.PicardFuchs.Clearance.connectionDenominator parameter * Polynomials.baseValue point =
      2 * (parameter - point) * Polynomials.curveValue parameter point +
        2 * (4 * point - 2) * Polynomials.curveValue parameter point -
          (2 * Polynomials.baseValue point) * Polynomials.spatialDerivativeValue parameter point := by
  unfold Clearance.connectionDenominator Clearance.ParameterClearance.connectionDenominator
    Polynomials.baseValue Polynomials.curveValue Polynomials.spatialDerivativeValue
  ring1

/-- Second row of the same connection, with primitive numerator `2 λ x(x-1)`. -/
theorem secondConnection_cleared (parameter point :
  Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Legendre.PicardFuchs.Clearance.connectionDenominator parameter * (point * Polynomials.baseValue
      point) =
      2 * (parameter - parameter * point) * Polynomials.curveValue parameter point +
        2 * (parameter * (4 * point - 2)) *
          Polynomials.curveValue parameter point -
        (2 * parameter * Polynomials.baseValue point) *
          Polynomials.spatialDerivativeValue parameter point := by
  unfold Clearance.connectionDenominator Clearance.ParameterClearance.connectionDenominator
    Polynomials.baseValue Polynomials.curveValue Polynomials.spatialDerivativeValue
  ring1

set_option genInjectivity false in
/-- One fully displayed row of the fraction-free connection reduction. The left side is twice the usual
parameter-derivative numerator; the right side is the basis contribution plus the numerator of `d(R/y)`, with all powers
of `y` cleared using `y² = f`. -/
structure ConnectionReduction (parameter :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained dense polynomial numerator of the parameter derivative row. -/ parameterDerivativeNumerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The constant coefficient of the retained basis contribution. -/ basisConstant : Data.Gaussian.Basic.Canonical
  /-- The linear coefficient of the retained basis contribution. -/ basisLinear : Data.Gaussian.Basic.Canonical
  /-- The retained dense numerator of the exact spatial primitive. -/ primitiveNumerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The retained polynomials satisfy the pointwise connection identity after clearing the common denominator and sheet
    powers. -/ clearedIdentity : forall point : Data.Gaussian.Basic.Canonical,
    Clearance.connectionDenominator parameter *
        parameterDerivativeNumerator.eval point =
      2 * (basisConstant + basisLinear * point) *
          (Paths.polynomial parameter).eval point +
        2 * (GCD.derivative primitiveNumerator).eval point *
          (Paths.polynomial parameter).eval point -
        primitiveNumerator.eval point *
          (GCD.derivative
            (Paths.polynomial parameter)).eval point

constructive_injectivity Purelib.Curves.Legendre.PicardFuchs.Connection.ConnectionReduction

/-- The first retained primitive and basis coefficients satisfy the exact denominator-cleared polynomial connection row.
-/
theorem firstConnectionPolynomialIdentity (parameter point :
  Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Legendre.PicardFuchs.Clearance.connectionDenominator parameter * Polynomials.basePolynomial.eval
      point =
      2 * (parameter + (-1) * point) *
          (Paths.polynomial parameter).eval point +
        2 * (GCD.derivative
          Polynomials.firstPrimitivePolynomial).eval point *
            (Paths.polynomial parameter).eval point -
        Polynomials.firstPrimitivePolynomial.eval point *
          (GCD.derivative
            (Paths.polynomial parameter)).eval point := by
  rw [Polynomials.basePolynomial_eval, Paths.polynomial_eval,
    Polynomials.firstPrimitiveDerivative_eval, Polynomials.firstPrimitivePolynomial_eval,
    ← Polynomials.spatialDerivativePolynomial_matches_automatic parameter point,
    Polynomials.spatialDerivativePolynomial_eval]
  unfold Clearance.connectionDenominator Clearance.ParameterClearance.connectionDenominator
  ring1

/-- The second retained primitive and basis coefficients satisfy the exact denominator-cleared polynomial connection
row. -/
theorem secondConnectionPolynomialIdentity (parameter point :
  Data.Gaussian.Basic.Canonical) :
    Purelib.Curves.Legendre.PicardFuchs.Clearance.connectionDenominator parameter *
      Polynomials.weightedBasePolynomial.eval point =
      2 * (parameter + (-parameter) * point) *
          (Paths.polynomial parameter).eval point +
        2 * (GCD.derivative
          (Polynomials.secondPrimitivePolynomial parameter)).eval point *
            (Paths.polynomial parameter).eval point -
        (Polynomials.secondPrimitivePolynomial parameter).eval point *
          (GCD.derivative
            (Paths.polynomial parameter)).eval point := by
  rw [Polynomials.weightedBasePolynomial_eval, Paths.polynomial_eval,
    Polynomials.secondPrimitiveDerivative_eval, Polynomials.secondPrimitivePolynomial_eval,
    ← Polynomials.spatialDerivativePolynomial_matches_automatic parameter point,
    Polynomials.spatialDerivativePolynomial_eval]
  unfold Clearance.connectionDenominator Clearance.ParameterClearance.connectionDenominator
  ring1

/-- The first row `D ∂λ ω₀ = λ ω₀ - ω₁ + d(2g/y)` as finite polynomial data. -/
def firstConnectionReduction (parameter :
  Data.Gaussian.Basic.Canonical) :
    ConnectionReduction parameter where
  parameterDerivativeNumerator := Polynomials.basePolynomial
  basisConstant := parameter
  basisLinear := -1
  primitiveNumerator := Polynomials.firstPrimitivePolynomial
  clearedIdentity := firstConnectionPolynomialIdentity parameter

/-- The second row `D ∂λ ω₁ = λ ω₀ - λ ω₁ + d(2λg/y)` as finite polynomial data. -/
def secondConnectionReduction (parameter :
  Data.Gaussian.Basic.Canonical) :
    ConnectionReduction parameter where
  parameterDerivativeNumerator := Polynomials.weightedBasePolynomial
  basisConstant := parameter
  basisLinear := -parameter
  primitiveNumerator := Polynomials.secondPrimitivePolynomial parameter
  clearedIdentity := secondConnectionPolynomialIdentity parameter

namespace ConnectionReduction

open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The retained connection basis coefficients as one exact finite polynomial. -/
def basisNumerator {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[reduction.basisLinear, reduction.basisConstant]⟩

/-- The basis polynomial reads back as the original constant and linear coefficients. -/
theorem basisNumerator_eval {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) (point : Data.Gaussian.Basic.Canonical) :
    reduction.basisNumerator.eval point = reduction.basisConstant + reduction.basisLinear * point := by
  change (0 * point + reduction.basisLinear) * point + reduction.basisConstant = _
  ring1

/-- The exact parameter-derivative differential retains the original half-scaled numerator and original curve. -/
def parameterDifferential {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) : Expression (Paths.polynomial parameter) :=
  (Expression.oddReciprocal (Paths.polynomial parameter) 1 reduction.parameterDerivativeNumerator).scale
    (constant (⟨1 / 2, 0⟩ : Data.Gaussian.Basic.Canonical))

/-- The exact connection basis differential uses the retained original basis polynomial over the original sheet. -/
def basisDifferential {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddReciprocal (Paths.polynomial parameter) 0 reduction.basisNumerator

/-- The exact connection primitive retains the original stored numerator over the original sheet. -/
def primitiveExpression {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddReciprocal (Paths.polynomial parameter) 0 reduction.primitiveNumerator

/-- The exact spatial primitive differential is constructed by the shared odd-power calculus. -/
def primitiveDifferential {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddPrimitiveDerivative (Paths.polynomial parameter) 0 reduction.primitiveNumerator

/-- Formal differentiation of the retained original primitive gives the constructed primitive differential. -/
theorem primitive_derivative {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) :
    reduction.primitiveExpression.derivative.Equal reduction.primitiveDifferential :=
  Expression.derivative_oddReciprocal _ _ _

/-- A scalar cleared connection identity survives multiplication by the common odd-power denominator. -/
private theorem connection_cross {D S B P R dR dP : Data.Gaussian.Basic.Canonical}
    (cleared : D * S = 2 * B * P + 2 * dR * P - R * dP) :
    D * ((⟨1 / 2, 0⟩ : Data.Gaussian.Basic.Canonical) * S) * (P * (2 * P ^ 2)) =
      (2 * P ^ 2 * B + P * (2 * (P * dR) - R * dP)) * P ^ 2 := by
  have halfTwice : (⟨1 / 2, 0⟩ : Data.Gaussian.Basic.Canonical) * 2 = 1 := by decide
  calc
    _ = (D * S) * P ^ 3 * ((⟨1 / 2, 0⟩ : Data.Gaussian.Basic.Canonical) * 2) := by ring1
    _ = (D * S) * P ^ 3 := by rw [halfTwice, mul_one]
    _ = (2 * B * P + 2 * dR * P - R * dP) * P ^ 3 := congrArg (fun value => value * P ^ 3) cleared
    _ = _ := by ring1

/-- The original denominator-scaled connection row is an exact coefficient identity with its retained primitive.

The certificate is constructed from the reduction's actual polynomial data
and the shared odd-power derivative formula. No period observation,
quadrature schedule or caller-provided differential identity is needed. -/
theorem differential_identity {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : ConnectionReduction parameter) :
    (reduction.parameterDifferential.scale (constant (Clearance.connectionDenominator parameter))).Equal
      (reduction.basisDifferential.add reduction.primitiveDifferential) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [parameterDifferential, basisDifferential, primitiveDifferential,
      Expression.scale, Expression.add, Expression.oddReciprocal, Expression.oddPrimitiveDerivative,
      Purelib.Algebra.Quadratic.Pair.scale, Purelib.Algebra.Quadratic.Pair.add_re,
      eval_mul, eval_add, eval_zero]
    ring1
  · intro point
    have cleared := reduction.clearedIdentity point
    rw [GCD.derivative, GCD.derivative] at cleared
    rw [← reduction.basisNumerator_eval point] at cleared
    simp only [parameterDifferential, basisDifferential, primitiveDifferential,
      Expression.scale, Expression.add, Expression.oddReciprocal, Expression.oddPrimitiveDerivative,
      Expression.oddPrimitiveNumerator, Purelib.Algebra.Quadratic.Pair.scale,
      Purelib.Algebra.Quadratic.Pair.add_im, eval_mul, eval_add, eval_sub, eval_scale, eval_constant,
      Power.eval_power, Nat.cast_zero, mul_zero, zero_add, one_mul, pow_one]
    exact connection_cross
      (D := Clearance.connectionDenominator parameter)
      (S := reduction.parameterDerivativeNumerator.eval point)
      (B := reduction.basisNumerator.eval point)
      (P := (Paths.polynomial parameter).eval point)
      (R := reduction.primitiveNumerator.eval point)
      (dR := (Derivative.derivative reduction.primitiveNumerator).eval point)
      (dP := (Derivative.derivative (Paths.polynomial parameter)).eval point) cleared

end ConnectionReduction
end Purelib.Curves.Legendre.PicardFuchs.Connection

end
