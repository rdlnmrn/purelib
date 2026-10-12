module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication

public import Purelib.Polynomial.Dense.Derivative
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

public section

/-!
# Finite Gaussian polynomial composition and its derivative

Composition is a finite Horner fold. The derivative identity follows from
the same fold's two-component value/derivative state, without evaluation
over an infinite carrier or any coefficient extensionality principle.
-/

-- Retain exact public scalar/carrier shorthand names after subject placement.

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Composition

open Purelib.Data
open Purelib.Polynomial

/-- Canonical Gaussian rational coefficients for composition. -/
abbrev CanonicalScalar := Gaussian.Basic.Canonical
/-- Dense Gaussian rational polynomials for composition. -/
abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Polynomial.Dense.Basic.DensePolynomial

open Purelib.Data.Gaussian.Basic.Canonical

/-- One polynomial Horner step using the retained substitution polynomial. -/
private def step (substitution accumulator : CoefficientPolynomial) (coefficient :
  CanonicalScalar) : CoefficientPolynomial :=
  accumulator * substitution + Dense.Basic.DensePolynomial.constant coefficient

/-- Compose two Gaussian polynomials by a finite Horner fold.

The original coefficient table is traversed in descending order, multiplying by the substitution and adding each
constant coefficient. -/
@[expose] def compose (polynomial substitution : CoefficientPolynomial) : CoefficientPolynomial :=
  polynomial.coeffs.foldl
    (fun accumulator coefficient => accumulator * substitution + Dense.Basic.DensePolynomial.constant coefficient) 0

/-- A constant polynomial has zero derivative at every Gaussian point. -/
private theorem derivative_constant (coefficient point : CanonicalScalar) :
    (Dense.Derivative.derivative (Dense.Basic.DensePolynomial.constant coefficient)).eval point = 0 := by
  rw [Dense.Derivative.eval_derivative]
  change 0 * point + 0 = 0
  rw [Gaussian.Basic.zero_mul, Gaussian.Basic.add_zero]

/-- Advance a composition value and derivative using the substitution value and slope. -/
private def jetStep (value slope : CanonicalScalar) (state :
  CanonicalScalar × CanonicalScalar) (coefficient :
  CanonicalScalar) : CanonicalScalar × CanonicalScalar :=
  (state.1 * value + coefficient, state.2 * value + state.1 * slope)

/-- Evaluation and differentiation of a polynomial Horner fold equal its scalar jet fold.

Each coefficient advances the retained value and derivative pair, while scalar transport leaves the remaining finite
fold unchanged. -/
private theorem fold_jet (substitution : CoefficientPolynomial) (point :
  CanonicalScalar) (coefficients : List
  CanonicalScalar) (initial : CoefficientPolynomial) :
    ((coefficients.foldl (Dense.Gaussian.Substitution.Composition.step substitution) initial).eval point,
      (Dense.Derivative.derivative (coefficients.foldl (Dense.Gaussian.Substitution.Composition.step substitution)
        initial)).eval point) =
    coefficients.foldl (Dense.Gaussian.Substitution.Composition.jetStep (substitution.eval point)
      ((Dense.Derivative.derivative substitution).eval point))
      (initial.eval point, (Dense.Derivative.derivative initial).eval point) := by
  induction coefficients generalizing initial with
  | nil => rfl
  | cons coefficient remaining previous =>
      rw [List.foldl_cons, previous, List.foldl_cons]
      apply congrArg (fun state => remaining.foldl
        (Dense.Gaussian.Substitution.Composition.jetStep (substitution.eval point)
          ((Dense.Derivative.derivative substitution).eval point)) state)
      apply Prod.ext
      · dsimp only [Dense.Gaussian.Substitution.Composition.step,
          Dense.Gaussian.Substitution.Composition.jetStep]
        rw [Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_mul,
          Dense.Basic.DensePolynomial.eval_constant]
      · dsimp only [Dense.Gaussian.Substitution.Composition.step,
          Dense.Gaussian.Substitution.Composition.jetStep]
        rw [Dense.Derivative.eval_derivative_add, Dense.Derivative.eval_derivative_mul,
          Dense.Gaussian.Substitution.Composition.derivative_constant, Gaussian.Basic.add_zero]

/-- Factor the substitution slope out of the derivative component of the finite jet fold. -/
private theorem chain_fold (value slope : CanonicalScalar) (coefficients : List
  CanonicalScalar) (initial tangent : CanonicalScalar)
  :
    coefficients.foldl (Dense.Gaussian.Substitution.Composition.jetStep value slope) (initial, tangent * slope) =
      let result := coefficients.foldl (Dense.Derivative.evalDerivativeStep value) (initial, tangent)
      (result.1, result.2 * slope) := by
  induction coefficients generalizing initial tangent with
  | nil => rfl
  | cons coefficient remaining previous =>
      rw [List.foldl_cons]
      have identity : Dense.Gaussian.Substitution.Composition.jetStep value slope (initial, tangent * slope) coefficient
        =
          (initial * value + coefficient, (tangent * value + initial) * slope) := by
        apply Prod.ext
        · rfl
        · change tangent * slope * value + initial * slope = (tangent * value + initial) * slope
          ring1
      rw [identity, previous]
      rfl

/-- Composition evaluation and its derivative satisfy the finite chain rule together. -/
private theorem composition_jet (polynomial substitution : CoefficientPolynomial) (point :
  CanonicalScalar) :
    ((Dense.Gaussian.Substitution.Composition.compose polynomial substitution).eval point, (Dense.Derivative.derivative
      (Dense.Gaussian.Substitution.Composition.compose polynomial substitution)).eval point) =
      (polynomial.eval (substitution.eval point),
        (Dense.Derivative.derivative polynomial).eval (substitution.eval point) * (Dense.Derivative.derivative
          substitution).eval point) := by
  have result := Dense.Gaussian.Substitution.Composition.fold_jet substitution point polynomial.coeffs 0
  have zeroDerivative : (Dense.Derivative.derivative (0 : CoefficientPolynomial)).eval point = 0
    := rfl
  rw [Dense.Basic.DensePolynomial.eval_zero, zeroDerivative] at result
  have chain := Dense.Gaussian.Substitution.Composition.chain_fold (substitution.eval point)
    ((Dense.Derivative.derivative substitution).eval point) polynomial.coeffs 0 0
  rw [Gaussian.Basic.zero_mul] at chain
  rw [chain] at result
  change ((Dense.Gaussian.Substitution.Composition.compose polynomial substitution).eval point,
    (Dense.Derivative.derivative (Dense.Gaussian.Substitution.Composition.compose polynomial substitution)).eval point)
    =
    ((Dense.Derivative.evalDerivativeCoeffs (substitution.eval point) polynomial.coeffs).1,
      (Dense.Derivative.evalDerivativeCoeffs (substitution.eval point) polynomial.coeffs).2 *
        (Dense.Derivative.derivative substitution).eval point) at result
  rw [Dense.Derivative.eval_original, ← Dense.Derivative.eval_derivative] at result
  exact result

/-- Evaluating composition equals nested evaluation at the substitution value. -/
theorem eval_compose (polynomial substitution : CoefficientPolynomial) (point :
  CanonicalScalar) :
    (Dense.Gaussian.Substitution.Composition.compose polynomial substitution).eval point = polynomial.eval
      (substitution.eval point) :=
  congrArg Prod.fst (Dense.Gaussian.Substitution.Composition.composition_jet polynomial substitution point)

/-- The derivative of composition evaluates by the polynomial chain rule. -/
theorem derivative_compose (polynomial substitution : CoefficientPolynomial) (point :
  CanonicalScalar) :
    (Dense.Derivative.derivative (Dense.Gaussian.Substitution.Composition.compose polynomial substitution)).eval point =
      (Dense.Derivative.derivative polynomial).eval (substitution.eval point) * (Dense.Derivative.derivative
        substitution).eval point :=
  congrArg Prod.snd (Dense.Gaussian.Substitution.Composition.composition_jet polynomial substitution point)

end Purelib.Polynomial.Dense.Gaussian.Substitution.Composition
