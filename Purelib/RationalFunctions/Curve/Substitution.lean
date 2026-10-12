module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Multiplication
public import Purelib.RationalFunctions.Curve.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Finite rational curves and denominator-cleared polynomial evaluation

A rationally parameterized Gaussian curve is represented by two finite dense
Gaussian polynomials `N(t)` and `D(t)`.  Evaluation means `N(t) / D(t)` only
at an explicitly supplied nonzero denominator.  A Horner fold computes
`D(t)^n p(N(t)/D(t))` without division; its real and imaginary coefficient
polynomials are therefore suitable for finite gcd and Sturm calculations.
-/

namespace Purelib.RationalFunctions.Curve

open Purelib.Data
open Purelib.Polynomial

set_option genInjectivity false in
/-- Polynomial accumulators for denominator-cleared Horner evaluation.

The value accumulator represents the cleared partial substitution, and the denominator-power accumulator retains the
factor used to clear it. Both are finite dense Gaussian polynomials. -/
structure ClearingState where
  /-- The accumulated denominator-cleared polynomial value. -/ value :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The accumulated power of the displayed denominator polynomial. -/ denominatorPower :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

constructive_injectivity ClearingState

/-- Initialize cleared Horner evaluation with zero value and unit denominator power.

Both accumulators retain the original constant dense polynomials. This is
the initial state of the finite coefficient fold. -/
@[expose] def ClearingState.initial : ClearingState :=
  ⟨0, Dense.Basic.DensePolynomial.constant 1⟩

/-- Advance denominator-cleared Horner evaluation by one Gaussian coefficient.

Multiply the retained denominator power by the denominator polynomial. The next value is the old value times the
numerator plus the coefficient times that next denominator power. -/
@[expose] def ClearingState.step
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (state : ClearingState) (coefficient : Gaussian.Basic.Canonical) : ClearingState :=
  let nextPower := state.denominatorPower * denominator
  { value := state.value * numerator + Dense.Basic.DensePolynomial.scale coefficient nextPower
    denominatorPower := nextPower }

/-- Fold the cleared Horner step over the polynomial's retained coefficient list.

The fold uses the curve's exact numerator and denominator polynomials, starting with zero value and unit denominator
power. -/
@[expose] def clearingState
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve) :
      ClearingState :=
  p.coeffs.foldl
    (ClearingState.step curve.numerator curve.denominator)
    ClearingState.initial

/-- Read the polynomial value from denominator-cleared Horner substitution. -/
@[expose] def clearedEval
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve) :
      (Dense.Basic.DensePolynomial
      Gaussian.Basic.Canonical) :=
  (clearingState p curve).value

/-- The cleared Horner fold preserves its evaluation invariant.

Assume the numerator evaluation equals the displayed affine value times the denominator evaluation. An initial
cleared-value identity then transports through the coefficient list to the corresponding scalar Horner fold. -/
private theorem fold_clearing_spec
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (parameterValue parameter : Gaussian.Basic.Canonical)
    (numeratorIdentity : numerator.eval parameter =
      parameterValue * denominator.eval parameter) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (state : ClearingState)
      (accumulator : Gaussian.Basic.Canonical),
      state.value.eval parameter =
          state.denominatorPower.eval parameter * accumulator →
      let final := coefficients.foldl
        (ClearingState.step numerator denominator) state
      final.value.eval parameter =
        final.denominatorPower.eval parameter *
          coefficients.foldl
            (fun value coefficient => value * parameterValue + coefficient)
            accumulator
  | [], state, accumulator, invariant => invariant
  | coefficient :: coefficients, state, accumulator, invariant => by
      simp only [List.foldl_cons]
      apply fold_clearing_spec numerator denominator parameterValue parameter
        numeratorIdentity coefficients
        (ClearingState.step numerator denominator state coefficient)
        (accumulator * parameterValue + coefficient)
      simp only [ClearingState.step, Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_mul,
        Dense.Basic.DensePolynomial.eval_scale]
      rw [invariant, numeratorIdentity]
      ring1

/-- At a nonzero curve denominator, cleared substitution equals the retained denominator power times polynomial
evaluation.

Both polynomial accumulators are evaluated at the Gaussian embedding of the same rational parameter. The scalar
polynomial is evaluated at the curve's affine point. -/
theorem eval_clearedEval
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve)
    (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedEval p curve).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) =
      (clearingState p curve).denominatorPower.eval
          (Gaussian.Cast.Path.ofCoordinate parameter) *
        p.eval (curve.point parameter) := by
  let parameterGaussian :=
    Gaussian.Cast.Path.ofCoordinate parameter
  have numeratorIdentity : curve.numerator.eval parameterGaussian =
      curve.point parameter * curve.denominator.eval parameterGaussian := by
    change curve.numeratorAt parameter =
      (curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹) *
        curve.denominatorAt parameter
    symm
    calc
      (curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹) *
          curve.denominatorAt parameter =
          curve.numeratorAt parameter *
            ((curve.denominatorAt parameter)⁻¹ *
              curve.denominatorAt parameter) :=
        Gaussian.Basic.mul_assoc _ _ _
      _ = curve.numeratorAt parameter * 1 := by
        rw [Gaussian.Basic.Canonical.inv_mul_cancel _
          denominatorNonzero]
      _ = curve.numeratorAt parameter :=
        Gaussian.Basic.mul_one _
  have initialInvariant :
      ClearingState.initial.value.eval parameterGaussian =
        ClearingState.initial.denominatorPower.eval parameterGaussian * 0 := by
    rw [ClearingState.initial, Dense.Basic.DensePolynomial.eval_zero, Dense.Basic.DensePolynomial.eval_constant,
      Gaussian.Basic.mul_zero]
  exact fold_clearing_spec curve.numerator curve.denominator
    (curve.point parameter) parameterGaussian numeratorIdentity p.coeffs
    ClearingState.initial 0 initialInvariant

/-- A cleared Horner fold multiplies the initial denominator-power value by one denominator value per coefficient.

The exponent is the exact length of the retained coefficient list; numerator values and coefficient values do not affect
this accumulator. -/
private theorem fold_denominatorPower_eval
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (parameter :
      Gaussian.Basic.Canonical) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (state : ClearingState),
      (coefficients.foldl
          (ClearingState.step numerator denominator) state).denominatorPower.eval
            parameter =
        state.denominatorPower.eval parameter *
          denominator.eval parameter ^ coefficients.length
  | [], _state => by
      change _ = _ * 1
      exact (Gaussian.Basic.mul_one _).symm
  | _coefficient :: coefficients, state => by
      simp only [List.foldl_cons, List.length_cons]
      rw [fold_denominatorPower_eval numerator denominator parameter
        coefficients
          (ClearingState.step numerator denominator state _coefficient)]
      simp only [ClearingState.step, Dense.Basic.DensePolynomial.eval_mul, pow_succ]
      ring1

/-- The final denominator accumulator evaluates to the denominator value raised to the coefficient-list length. -/
theorem eval_denominatorPower
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve)
    (parameter : Rat.Fraction.Rational) :
    (clearingState p curve).denominatorPower.eval
        (Gaussian.Cast.Path.ofCoordinate parameter) =
      curve.denominatorAt parameter ^ p.coeffs.length := by
  change
    (p.coeffs.foldl
        (ClearingState.step curve.numerator curve.denominator)
          ClearingState.initial).denominatorPower.eval
          (Gaussian.Cast.Path.ofCoordinate parameter) = _
  rw [fold_denominatorPower_eval]
  simp only [ClearingState.initial, Dense.Basic.DensePolynomial.eval_constant,
    Gaussian.Basic.one_mul]
  rfl

/-- A nonzero initial denominator-power value remains nonzero throughout the fold.

The denominator evaluation is assumed nonzero at the fixed Gaussian parameter. Every step multiplies the accumulator by
that same nonzero value. -/
private theorem fold_denominatorPower_ne
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (parameter :
      Gaussian.Basic.Canonical)
    (denominatorNonzero : denominator.eval parameter ≠ 0) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (state : ClearingState),
      state.denominatorPower.eval parameter ≠ 0 →
      (coefficients.foldl
        (ClearingState.step numerator denominator) state).denominatorPower.eval
          parameter ≠ 0
  | [], _state, stateNonzero => stateNonzero
  | _coefficient :: coefficients, state, stateNonzero => by
      simp only [List.foldl_cons]
      apply fold_denominatorPower_ne numerator denominator parameter
        denominatorNonzero coefficients
        (ClearingState.step numerator denominator state _coefficient)
      simp only [ClearingState.step, Dense.Basic.DensePolynomial.eval_mul]
      exact Gaussian.Field.mul_ne_zero_direct
        stateNonzero denominatorNonzero

/-- At a nonzero curve denominator, the final denominator-power evaluation is nonzero. -/
theorem denominatorPower_eval_ne
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve)
    (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearingState p curve).denominatorPower.eval
        (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0 := by
  apply fold_denominatorPower_ne curve.numerator curve.denominator
    (Gaussian.Cast.Path.ofCoordinate parameter)
    denominatorNonzero p.coeffs ClearingState.initial
  simp only [ClearingState.initial, Dense.Basic.DensePolynomial.eval_constant]
  intro oneZero
  have realOneZero := congrArg Gaussian.Basic.re oneZero
  exact Rat.Fraction.Field.zero_ne_one realOneZero.symm

/-- Extract the real coordinate polynomial of the cleared substitution. -/
@[expose] def clearedReal
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve) :
      (Dense.Basic.DensePolynomial
      Rat.Fraction.Rational) :=
  Dense.Gaussian.Components.realPart (clearedEval p curve)

/-- Extract the imaginary coordinate polynomial of the cleared substitution. -/
@[expose] def clearedImag
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve) :
      (Dense.Basic.DensePolynomial
      Rat.Fraction.Rational) :=
  Dense.Gaussian.Components.imagPart (clearedEval p curve)

/-- At a nonzero denominator, both cleared coordinates vanish exactly when the original polynomial vanishes on the
curve.

The nonzero denominator-power evaluation can be cancelled from the exact cleared-substitution identity. The two
coordinate equalities express vanishing of the Gaussian cleared value. -/
theorem cleared_pair_zero_iff
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : RationalCurve)
    (parameter : Rat.Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedReal p curve).eval parameter = 0 ∧
        (clearedImag p curve).eval parameter = 0 ↔
      p.eval (curve.point parameter) = 0 := by
  have semantics := eval_clearedEval p curve parameter denominatorNonzero
  have powerNonzero :=
    denominatorPower_eval_ne p curve parameter denominatorNonzero
  constructor
  · rintro ⟨realZero, imaginaryZero⟩
    have clearedZero : (clearedEval p curve).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) = 0 := by
      apply Gaussian.Basic.ext
      · change ((clearedEval p curve).eval
          (Gaussian.Cast.Path.ofCoordinate parameter)).re =
          (0 : Rat.Fraction.Rational)
        simpa only [clearedReal,
          Dense.Gaussian.Components.eval_realPart] using realZero
      · change ((clearedEval p curve).eval
          (Gaussian.Cast.Path.ofCoordinate parameter)).im =
          (0 : Rat.Fraction.Rational)
        simpa only [clearedImag,
          Dense.Gaussian.Components.eval_imagPart] using imaginaryZero
    rw [clearedZero] at semantics
    by_cases root : p.eval (curve.point parameter) = 0
    · exact root
    · have productNonzero :=
        Gaussian.Field.mul_ne_zero_direct
          powerNonzero root
      exact (productNonzero semantics.symm).elim
  · intro root
    have clearedZero : (clearedEval p curve).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) = 0 := by
      rw [semantics, root,
        Gaussian.Basic.mul_zero]
    constructor
    · rw [clearedReal,
        Dense.Gaussian.Components.eval_realPart, clearedZero, Gaussian.Basic.zero_re]
    · rw [clearedImag,
        Dense.Gaussian.Components.eval_imagPart, clearedZero, Gaussian.Basic.zero_im]

end Purelib.RationalFunctions.Curve

end
