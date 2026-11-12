module

public import Purelib.Polynomial.Dense.Derivative
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Displayed parameter families of dense polynomials

An outer coefficient table uses polynomial coefficients in one retained
parameter. Specialization and both partial derivatives are executable finite
Horner calculations. The mixed derivative law follows the same original
tables and does not assert any numerical moving-path derivative.
-/

public section

namespace Purelib.Polynomial.Dense.Parameter

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Polynomial.Dense

/-- A dense spatial coefficient table whose coefficients are dense polynomials in one parameter. -/
abbrev Family (K : Type*) := DensePolynomial (DensePolynomial K)

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Evaluate each original parameter coefficient without changing the spatial coefficient order. -/
@[expose] def specialize (family : Family K) (parameter : K) : DensePolynomial K :=
  ⟨family.coeffs.map (fun coefficient => coefficient.eval parameter)⟩

/-- Differentiate each original parameter coefficient using its finite Horner derivative. -/
@[expose] def derivative (family : Family K) : Family K :=
  ⟨family.coeffs.map Derivative.derivative⟩

/-- Evaluate the spatial variable while retaining a polynomial in the original parameter. -/
@[expose] def atPoint (family : Family K) (point : K) : DensePolynomial K :=
  family.coeffs.foldl (fun accumulator coefficient => accumulator.scale point + coefficient) 0

/-- One spatial Horner step retains both the parameter polynomial and its spatial derivative. -/
@[expose] def spatialStep (point : K) (state : DensePolynomial K × DensePolynomial K)
    (coefficient : DensePolynomial K) : DensePolynomial K × DensePolynomial K :=
  (state.1.scale point + coefficient, state.2.scale point + state.1)

/-- Retain the original parameter-polynomial first derivative in the spatial coordinate. -/
@[expose] def spatialAtPoint (family : Family K) (point : K) : DensePolynomial K :=
  (family.coeffs.foldl (spatialStep point) (0, 0)).2

/-- Polynomial parameter evaluation commutes with the retained spatial Horner fold. -/
private theorem eval_fold (coefficients : List (DensePolynomial K)) (accumulator : DensePolynomial K)
    (parameter point : K) :
    (coefficients.foldl (fun value coefficient => value.scale point + coefficient) accumulator).eval parameter =
      (coefficients.map (fun coefficient => coefficient.eval parameter)).foldl
        (fun value coefficient => value * point + coefficient) (accumulator.eval parameter) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining previous =>
      simp only [List.foldl_cons, List.map_cons]
      rewrite [previous, eval_add, eval_scale]
      exact congrArg
        (fun value => (remaining.map (fun coefficient => coefficient.eval parameter)).foldl
          (fun accumulator coefficient => accumulator * point + coefficient) value)
        (congrArg (· + coefficient.eval parameter) (mul_comm point (accumulator.eval parameter)))

/-- Either order of evaluating the two original finite coefficient tables gives the same value. -/
theorem eval_atPoint (family : Family K) (parameter point : K) :
    (atPoint family point).eval parameter = (specialize family parameter).eval point := by
  rewrite [atPoint, eval_fold, eval_zero]
  exact Eq.refl _

/-- The derivative of the spatial Horner fold reads the original parameter derivative coefficients. -/
private theorem derivative_eval_fold (coefficients : List (DensePolynomial K)) (accumulator : DensePolynomial K)
    (parameter point : K) :
    (Derivative.derivative
      (coefficients.foldl (fun value coefficient => value.scale point + coefficient) accumulator)).eval parameter =
      (coefficients.map (fun coefficient => (Derivative.derivative coefficient).eval parameter)).foldl
        (fun value coefficient => value * point + coefficient)
        ((Derivative.derivative accumulator).eval parameter) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient remaining previous =>
      simp only [List.foldl_cons, List.map_cons]
      rewrite [previous, Derivative.eval_derivative_add, Derivative.eval_derivative_scale]
      exact congrArg
        (fun value => (remaining.map (fun coefficient => (Derivative.derivative coefficient).eval parameter)).foldl
          (fun accumulator coefficient => accumulator * point + coefficient) value)
        (congrArg (· + (Derivative.derivative coefficient).eval parameter)
          (mul_comm point ((Derivative.derivative accumulator).eval parameter)))

/-- Parameter differentiation of the displayed family agrees with differentiating its retained point polynomial. -/
theorem eval_derivative (family : Family K) (parameter point : K) :
    (specialize (derivative family) parameter).eval point =
      (Derivative.derivative (atPoint family point)).eval parameter := by
  have derivativeZero : (Derivative.derivative (0 : DensePolynomial K)).eval parameter = 0 := rfl
  rewrite [atPoint, derivative_eval_fold, derivativeZero]
  change ((family.coeffs.map Derivative.derivative).map
      (fun coefficient => coefficient.eval parameter)).foldl
        (fun value coefficient => value * point + coefficient) 0 = _
  have mapped : (family.coeffs.map Derivative.derivative).map (fun coefficient => coefficient.eval parameter) =
      family.coeffs.map (fun coefficient => (Derivative.derivative coefficient).eval parameter) := by
    induction family.coeffs with
    | nil => rfl
    | cons coefficient remaining previous =>
        change (Derivative.derivative coefficient).eval parameter :: _ = _ :: _
        exact congrArg ((Derivative.derivative coefficient).eval parameter :: ·) previous
  rewrite [mapped]
  exact Eq.refl _

/-- Evaluation of the retained spatial value-and-derivative fold agrees with the scalar automatic derivative. -/
private theorem spatial_eval_fold (coefficients : List (DensePolynomial K))
    (state : DensePolynomial K × DensePolynomial K) (parameter point : K) :
    let result := coefficients.foldl (spatialStep point) state
    (result.1.eval parameter, result.2.eval parameter) =
      (coefficients.map (fun coefficient => coefficient.eval parameter)).foldl
        (Derivative.evalDerivativeStep point) (state.1.eval parameter, state.2.eval parameter) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient remaining previous =>
      simp only [List.foldl_cons, List.map_cons]
      rewrite [previous]
      have step : ((spatialStep point state coefficient).1.eval parameter,
          (spatialStep point state coefficient).2.eval parameter) =
          Derivative.evalDerivativeStep point (state.1.eval parameter, state.2.eval parameter)
            (coefficient.eval parameter) := by
        apply Prod.ext
        · change (state.1.scale point + coefficient).eval parameter = _
          rewrite [eval_add, eval_scale]
          change point * state.1.eval parameter + coefficient.eval parameter =
            state.1.eval parameter * point + coefficient.eval parameter
          ring1
        · change (state.2.scale point + state.1).eval parameter = _
          rewrite [eval_add, eval_scale]
          change point * state.2.eval parameter + state.1.eval parameter =
            state.2.eval parameter * point + state.1.eval parameter
          ring1
      exact congrArg (fun initial => (remaining.map (fun coefficient => coefficient.eval parameter)).foldl
        (Derivative.evalDerivativeStep point) initial) step

/-- The retained spatial derivative specializes to the original automatic derivative of the spatial table. -/
theorem eval_spatialAtPoint (family : Family K) (parameter point : K) :
    (spatialAtPoint family point).eval parameter =
      (Derivative.derivative (specialize family parameter)).eval point := by
  have equation := congrArg Prod.snd (spatial_eval_fold family.coeffs (0, 0) parameter point)
  exact equation.trans (Derivative.eval_derivative _ _).symm

/-- Parameter differentiation commutes with the original spatial value-and-derivative fold. -/
private theorem mixed_eval_fold (coefficients : List (DensePolynomial K))
    (state : DensePolynomial K × DensePolynomial K) (parameter point : K) :
    let result := coefficients.foldl (spatialStep point) state
    ((Derivative.derivative result.1).eval parameter, (Derivative.derivative result.2).eval parameter) =
      (coefficients.map (fun coefficient => (Derivative.derivative coefficient).eval parameter)).foldl
        (Derivative.evalDerivativeStep point)
        ((Derivative.derivative state.1).eval parameter, (Derivative.derivative state.2).eval parameter) := by
  induction coefficients generalizing state with
  | nil => rfl
  | cons coefficient remaining previous =>
      simp only [List.foldl_cons, List.map_cons]
      rewrite [previous]
      have step : ((Derivative.derivative (spatialStep point state coefficient).1).eval parameter,
          (Derivative.derivative (spatialStep point state coefficient).2).eval parameter) =
          Derivative.evalDerivativeStep point
            ((Derivative.derivative state.1).eval parameter, (Derivative.derivative state.2).eval parameter)
              ((Derivative.derivative coefficient).eval parameter) := by
        apply Prod.ext
        · change (Derivative.derivative (state.1.scale point + coefficient)).eval parameter = _
          rewrite [Derivative.eval_derivative_add, Derivative.eval_derivative_scale]
          change point * (Derivative.derivative state.1).eval parameter +
              (Derivative.derivative coefficient).eval parameter =
            (Derivative.derivative state.1).eval parameter * point +
              (Derivative.derivative coefficient).eval parameter
          ring1
        · change (Derivative.derivative (state.2.scale point + state.1)).eval parameter = _
          rewrite [Derivative.eval_derivative_add, Derivative.eval_derivative_scale]
          change point * (Derivative.derivative state.2).eval parameter +
              (Derivative.derivative state.1).eval parameter =
            (Derivative.derivative state.2).eval parameter * point +
              (Derivative.derivative state.1).eval parameter
          ring1
      exact congrArg
        (fun initial => (remaining.map (fun coefficient => (Derivative.derivative coefficient).eval parameter)).foldl
          (Derivative.evalDerivativeStep point) initial) step

/-- The two formal partial derivatives commute on the same retained finite family.

The left side differentiates the original spatial derivative as a polynomial
in the parameter. The right side first differentiates every retained parameter
coefficient and then runs the original spatial derivative. -/
theorem eval_mixed_derivative (family : Family K) (parameter point : K) :
    (Derivative.derivative (spatialAtPoint family point)).eval parameter =
      (Derivative.derivative (specialize (derivative family) parameter)).eval point := by
  have equation := congrArg Prod.snd (mixed_eval_fold family.coeffs (0, 0) parameter point)
  have derivativeZero : (Derivative.derivative (0 : DensePolynomial K)).eval parameter = 0 := rfl
  rewrite [derivativeZero] at equation
  have mapped : (family.coeffs.map Derivative.derivative).map (fun coefficient => coefficient.eval parameter) =
      family.coeffs.map (fun coefficient => (Derivative.derivative coefficient).eval parameter) := by
    induction family.coeffs with
    | nil => rfl
    | cons coefficient remaining previous =>
        change (Derivative.derivative coefficient).eval parameter :: _ = _ :: _
        exact congrArg ((Derivative.derivative coefficient).eval parameter :: ·) previous
  rewrite [Derivative.eval_derivative (specialize (derivative family) parameter) point]
  change _ = (((family.coeffs.map Derivative.derivative).map
    (fun coefficient => coefficient.eval parameter)).foldl (Derivative.evalDerivativeStep point) (0, 0)).2
  rewrite [mapped]
  exact equation

end Purelib.Polynomial.Dense.Parameter
