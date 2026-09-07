import FTA.PathPolynomial
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Executable dense Gaussian-polynomial derivative

Automatic differentiation is propagated through the same finite Horner scan
as polynomial evaluation.  The executable Gaussian-rational output is proved
equal to the formal derivative of the sparse specification, but no sparse
polynomial is used by the program itself.
-/

namespace FTA.GaussianDerivative

open Polynomial
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial

/-- One automatic-differentiation Horner step. -/
def derivativeStep
    (state : GaussianPolynomial × GaussianPolynomial) (a : QI) :
    GaussianPolynomial × GaussianPolynomial :=
  (shift 1 state.1 + constant a, shift 1 state.2 + state.1)

/-- Simultaneously construct the polynomial and its formal derivative. -/
def derivativeState (cs : List QI) :
    GaussianPolynomial × GaussianPolynomial :=
  cs.foldl derivativeStep (0, 0)

/-- Executable formal derivative of a dense Gaussian-rational polynomial. -/
def derivative (p : GaussianPolynomial) : GaussianPolynomial :=
  (derivativeState p.coeffs).2

private theorem fold_value_spec (cs : List QI)
    (state : GaussianPolynomial × GaussianPolynomial) :
    (cs.foldl derivativeStep state).1.toPolynomial =
      cs.foldl (fun P a => P * X + C a) state.1.toPolynomial := by
  induction cs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      dsimp only [derivativeStep]
      rw [toPolynomial_add (K := QI), toPolynomial_shift (K := QI),
        toPolynomial_constant (K := QI), pow_one]

private theorem fold_derivative_invariant (cs : List QI)
    (state : GaussianPolynomial × GaussianPolynomial)
    (hstate : state.2.toPolynomial = state.1.toPolynomial.derivative) :
    (cs.foldl derivativeStep state).2.toPolynomial =
      (cs.foldl derivativeStep state).1.toPolynomial.derivative := by
  induction cs generalizing state with
  | nil => exact hstate
  | cons a as ih =>
      simp only [List.foldl_cons]
      apply ih
      dsimp only [derivativeStep]
      rw [toPolynomial_add (K := QI), toPolynomial_shift (K := QI),
        toPolynomial_add (K := QI), toPolynomial_shift (K := QI),
        toPolynomial_constant (K := QI), hstate]
      simp [Polynomial.derivative_add, Polynomial.derivative_mul, pow_one]

/-- The executable derivative is exactly the formal derivative of the sparse
specification polynomial. -/
theorem toPolynomial_derivative (p : GaussianPolynomial) :
    (derivative p).toPolynomial = p.toPolynomial.derivative := by
  have hinitial : (0 : GaussianPolynomial).toPolynomial =
      (0 : GaussianPolynomial).toPolynomial.derivative := by
    rw [toPolynomial_zero (K := QI), Polynomial.derivative_zero]
  have hinvariant := fold_derivative_invariant p.coeffs (0, 0) hinitial
  have hvalue := fold_value_spec p.coeffs (0, 0)
  dsimp only [derivative, derivativeState] at hinvariant ⊢
  have hvalue' : (p.coeffs.foldl derivativeStep (0, 0)).1.toPolynomial =
      p.toPolynomial := by
    rw [toPolynomial_zero (K := QI)] at hvalue
    exact hvalue.trans (toPolynomial_eq_foldl_horner p).symm
  exact hinvariant.trans (congrArg Polynomial.derivative hvalue')

/-- Pointwise evaluation specification for the executable derivative. -/
theorem eval_derivative (p : GaussianPolynomial) (z : QI) :
    (derivative p).eval z = Polynomial.eval z p.toPolynomial.derivative := by
  rw [← eval_toPolynomial, toPolynomial_derivative]

/-! ## Native computation regression -/

/-- Automatic differentiation of `Z²-2` returns the dense program `2Z`. -/
theorem derivative_quadratic_example :
    derivative ⟨[(1 : QI), 0, -2]⟩ = ⟨[(2 : QI), 0]⟩ := by
  native_decide

end FTA.GaussianDerivative
