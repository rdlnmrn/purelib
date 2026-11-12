module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.PicardFuchs.Polynomials
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
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

open Purelib.Curves.Legendre.PicardFuchs

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

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

namespace Purelib.Curves.Legendre.PicardFuchs.Residual

/-- Numerator of the fraction-free scalar Picard--Fuchs residual over `y^5`. -/
def picardFuchsResidualNumerator
    (parameter point : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  3 * parameter * (1 - parameter) * Polynomials.baseValue point ^ 2 +
    2 * (1 - 2 * parameter) * Polynomials.baseValue point *
      Polynomials.curveValue parameter point - Polynomials.curveValue parameter point ^ 2

/-- The same residual numerator as a literal high-to-low dense polynomial. -/
def picardFuchsResidualPolynomial (parameter :
  Data.Gaussian.Basic.Canonical) :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  ⟨[-1, 4 - 2 * parameter, 5 * parameter - 5,
    2 - 4 * parameter, parameter, 0, 0]⟩

/-- The displayed dense residual polynomial evaluates to the exact scalar Picard-Fuchs residual numerator. -/
@[simp] theorem picardFuchsResidualPolynomial_eval
    (parameter point : Data.Gaussian.Basic.Canonical) :
    (picardFuchsResidualPolynomial parameter).eval point =
      picardFuchsResidualNumerator parameter point := by
  unfold picardFuchsResidualPolynomial Residual.picardFuchsResidualNumerator
    Polynomials.baseValue Polynomials.curveValue DensePolynomial.eval
    DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The residual is the spatial derivative of `2 x^2 (x-1)^2 / y^3`, after clearing the factor `2` introduced by the
half-power derivative. -/
theorem picardFuchsResidual_cleared (parameter point :
  Data.Gaussian.Basic.Canonical) :
    2 * picardFuchsResidualNumerator parameter point =
      2 * (4 * Purelib.Curves.Legendre.PicardFuchs.Polynomials.baseValue point * (2 * point - 1)) *
          Purelib.Curves.Legendre.PicardFuchs.Polynomials.curveValue parameter point -
        3 * (2 * Purelib.Curves.Legendre.PicardFuchs.Polynomials.baseValue point ^ 2) *
          Polynomials.spatialDerivativeValue parameter point := by
  unfold Residual.picardFuchsResidualNumerator Polynomials.baseValue Polynomials.curveValue
    Polynomials.spatialDerivativeValue
  ring1

set_option genInjectivity false in
/-- The full finite symbolic certificate for the scalar equation. Its identity is between evaluations of explicit dense
polynomials and their finite automatic derivatives. -/
structure PicardFuchsReduction (parameter :
  Data.Gaussian.Basic.Canonical) where
  /-- The retained dense polynomial numerator of the scalar equation residual. -/ residualNumerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The retained dense numerator of the exact spatial primitive over the sheet cube. -/ primitiveNumerator :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The exact residual is the retained primitive derivative expression after clearing all sheet powers and the factor
    two. -/ clearedIdentity : forall point : Data.Gaussian.Basic.Canonical,
    2 * residualNumerator.eval point =
      2 * (GCD.derivative primitiveNumerator).eval point *
          (Paths.polynomial parameter).eval point -
        3 * primitiveNumerator.eval point *
          (GCD.derivative
            (Paths.polynomial parameter)).eval point

constructive_injectivity Purelib.Curves.Legendre.PicardFuchs.Residual.PicardFuchsReduction

/-- The Legendre scalar reduction with no remembered analytic formula: every field is executable polynomial data and the
identity is proved directly. -/
def picardFuchsReduction (parameter : Data.Gaussian.Basic.Canonical)
  :
    PicardFuchsReduction parameter where
  residualNumerator := picardFuchsResidualPolynomial parameter
  primitiveNumerator := Polynomials.picardFuchsPrimitivePolynomial
  clearedIdentity := by
    intro point
    rw [picardFuchsResidualPolynomial_eval,
      Polynomials.picardFuchsPrimitiveDerivative_eval,
      Polynomials.picardFuchsPrimitivePolynomial_eval, Paths.polynomial_eval,
      ← Polynomials.spatialDerivativePolynomial_matches_automatic parameter point,
      Polynomials.spatialDerivativePolynomial_eval]
    exact picardFuchsResidual_cleared parameter point

namespace PicardFuchsReduction

open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The exact scalar residual retains its original numerator over the original sheet's fifth power. -/
def residualExpression {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : PicardFuchsReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddReciprocal (Paths.polynomial parameter) 2 reduction.residualNumerator

/-- The exact scalar primitive retains its original numerator over the original sheet's cube. -/
def primitiveExpression {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : PicardFuchsReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddReciprocal (Paths.polynomial parameter) 1 reduction.primitiveNumerator

/-- Construct the original scalar primitive differential through the shared odd-power calculus. -/
def primitiveDifferential {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : PicardFuchsReduction parameter) : Expression (Paths.polynomial parameter) :=
  Expression.oddPrimitiveDerivative (Paths.polynomial parameter) 1 reduction.primitiveNumerator

/-- Formal differentiation gives the constructed scalar primitive differential. -/
theorem primitive_derivative {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : PicardFuchsReduction parameter) :
    reduction.primitiveExpression.derivative.Equal reduction.primitiveDifferential :=
  Expression.derivative_oddReciprocal _ _ _

/-- A scalar cleared primitive identity survives multiplication by its retained cubic denominator. -/
private theorem residual_cross {E P R dR dP : Data.Gaussian.Basic.Canonical}
    (cleared : 2 * E = 2 * dR * P - 3 * R * dP) :
    E * (2 * P ^ 3) = (2 * (P * dR) - 3 * (R * dP)) * P ^ 3 := by
  calc
    _ = (2 * E) * P ^ 3 := by ring1
    _ = (2 * dR * P - 3 * R * dP) * P ^ 3 := congrArg (fun value => value * P ^ 3) cleared
    _ = _ := by ring1

/-- The original scalar residual is the exact spatial primitive differential as finite coefficient data.

The original stored numerators and the shared odd-power rule construct the
certificate internally, without a period program or caller-supplied
coefficient or numerical relation. -/
theorem differential_identity {parameter : Data.Gaussian.Basic.Canonical}
    (reduction : PicardFuchsReduction parameter) :
    reduction.residualExpression.Equal reduction.primitiveDifferential := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [residualExpression, primitiveDifferential, Expression.oddReciprocal,
      Expression.oddPrimitiveDerivative, eval_zero]
    ring1
  · intro point
    have cleared := reduction.clearedIdentity point
    rw [GCD.derivative, GCD.derivative] at cleared
    simp only [residualExpression, primitiveDifferential, Expression.oddReciprocal,
      Expression.oddPrimitiveDerivative, Expression.oddPrimitiveNumerator,
      eval_mul, eval_sub, eval_scale, Power.eval_power, Nat.cast_one]
    have three : 2 * (1 : Data.Gaussian.Basic.Canonical) + 1 = 3 := by decide
    rw [three]
    exact residual_cross cleared


end PicardFuchsReduction

end Purelib.Curves.Legendre.PicardFuchs.Residual

end
