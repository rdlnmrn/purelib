import FTA.DensePolynomialBridge
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Executable dense formal derivative

The derivative is computed by automatic differentiation of the same finite
Horner fold used for evaluation.  A state `(P,D)` represents a polynomial and
its derivative; consuming coefficient `a` sends it to
`(P X + a, D X + P)`.  The resulting dense program is proved exactly equal to
Mathlib's formal polynomial derivative through the semantic bridge.
-/

namespace FTA.DenseDerivative

open Polynomial
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial

abbrev RatPolynomial := DensePolynomial ℚ

/-- One automatic-differentiation Horner step. -/
def derivativeStep (state : RatPolynomial × RatPolynomial) (a : ℚ) :
    RatPolynomial × RatPolynomial :=
  (shift 1 state.1 + constant a, shift 1 state.2 + state.1)

/-- Simultaneously construct a polynomial and its formal derivative. -/
def derivativeState (cs : List ℚ) : RatPolynomial × RatPolynomial :=
  cs.foldl derivativeStep (0, 0)

/-- Executable formal derivative of a dense rational polynomial. -/
def derivative (p : RatPolynomial) : RatPolynomial :=
  (derivativeState p.coeffs).2

private theorem fold_value_spec (cs : List ℚ)
    (state : RatPolynomial × RatPolynomial) :
    (cs.foldl derivativeStep state).1.toPolynomial =
      cs.foldl (fun P a => P * X + C a) state.1.toPolynomial := by
  induction cs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [derivativeStep, toPolynomial_add, toPolynomial_shift, pow_one]

private theorem fold_derivative_invariant (cs : List ℚ)
    (state : RatPolynomial × RatPolynomial)
    (hstate : state.2.toPolynomial = state.1.toPolynomial.derivative) :
    (cs.foldl derivativeStep state).2.toPolynomial =
      (cs.foldl derivativeStep state).1.toPolynomial.derivative := by
  induction cs generalizing state with
  | nil => exact hstate
  | cons a as ih =>
      simp only [List.foldl_cons]
      apply ih
      dsimp only [derivativeStep]
      rw [toPolynomial_add, toPolynomial_shift, toPolynomial_add,
        toPolynomial_shift, toPolynomial_constant, hstate]
      simp [Polynomial.derivative_add, Polynomial.derivative_mul, pow_one]

/-- The executable derivative is exactly the formal derivative of the sparse
specification polynomial. -/
theorem toPolynomial_derivative (p : RatPolynomial) :
    (derivative p).toPolynomial = p.toPolynomial.derivative := by
  have hinvariant := fold_derivative_invariant p.coeffs (0, 0) (by simp)
  have hvalue := fold_value_spec p.coeffs (0, 0)
  dsimp only [derivative, derivativeState] at hinvariant ⊢
  have hvalue' : (p.coeffs.foldl derivativeStep (0, 0)).1.toPolynomial =
      p.toPolynomial := by
    rw [toPolynomial_zero] at hvalue
    exact hvalue.trans (toPolynomial_eq_foldl_horner p).symm
  exact hinvariant.trans (congrArg Polynomial.derivative hvalue')

/-- Pointwise evaluation specification for the executable derivative. -/
theorem eval_derivative (p : RatPolynomial) (x : ℚ) :
    (derivative p).eval x = Polynomial.eval x p.toPolynomial.derivative := by
  rw [← eval_toPolynomial, toPolynomial_derivative]

theorem derivative_isZero_false {p : RatPolynomial} (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) : (derivative p).isZero = false := by
  have hspecDegree : p.toPolynomial.natDegree ≠ 0 := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  have hspec : p.toPolynomial.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hspecDegree
  cases hd : (derivative p).isZero with
  | false => rfl
  | true =>
      have hzero := (toPolynomial_eq_zero_iff_isZero (derivative p)).mpr hd
      rw [toPolynomial_derivative] at hzero
      exact (hspec hzero).elim

/-- A nonconstant dense polynomial has a nonzero executable derivative of
strictly smaller natural degree. -/
theorem derivative_natDegree_lt {p : RatPolynomial} (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) :
    (derivative p).natDegree < p.natDegree := by
  have hd := derivative_isZero_false hp hdegree
  have hspecDegree : p.toPolynomial.natDegree ≠ 0 := by
    rw [natDegree_toPolynomial hp]
    exact hdegree
  have hlt := Polynomial.natDegree_derivative_lt hspecDegree
  rw [← toPolynomial_derivative, natDegree_toPolynomial hd,
    natDegree_toPolynomial hp] at hlt
  exact hlt

theorem derivative_degreeCount_lt {p : RatPolynomial} (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) :
    (derivative p).degreeCount < p.degreeCount := by
  have hd := derivative_isZero_false hp hdegree
  have hlt := derivative_natDegree_lt hp hdegree
  have hdCount := natDegree_add_one_eq_degreeCount hd
  have hpCount := natDegree_add_one_eq_degreeCount hp
  omega

end FTA.DenseDerivative
