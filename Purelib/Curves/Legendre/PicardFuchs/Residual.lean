module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.PicardFuchs.Polynomials
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

end Purelib.Curves.Legendre.PicardFuchs.Residual

end
