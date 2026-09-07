import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Path
import CCL.Encoding.RawParser

/-!
# Finite rational curves and denominator-cleared polynomial evaluation

A rationally parameterized Gaussian curve is represented by two finite dense
Gaussian polynomials `N(t)` and `D(t)`.  Evaluation means `N(t) / D(t)` only
at an explicitly supplied nonzero denominator.  A Horner fold computes
`D(t)^n p(N(t)/D(t))` without division; its real and imaginary coefficient
polynomials are therefore suitable for finite gcd and Sturm calculations.
-/

namespace CCL.RationalCurve

/- The doubled public name `CCL.RationalCurve.RationalCurve` is intentional:
the outer component names the module and the inner component names its main
finite data type. -/
set_option linter.dupNamespace false

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Mat2 := CCL.GaussianProjective.Mat2

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- Two finite Gaussian coefficient lists representing `N(t) / D(t)`. -/
structure RationalCurve where
  numerator : GaussianPolynomial
  denominator : GaussianPolynomial

namespace RationalCurve

def numeratorAt (curve : RationalCurve) (parameter : Coordinate) : Gaussian :=
  curve.numerator.eval (RFAP.PathPolynomial.ofCoordinate parameter)

def denominatorAt
    (curve : RationalCurve) (parameter : Coordinate) : Gaussian :=
  curve.denominator.eval
    (RFAP.PathPolynomial.ofCoordinate parameter)

def point (curve : RationalCurve) (parameter : Coordinate) : Gaussian :=
  curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹

/-- Compose a rational curve with one finite decoder homography by clearing
its old denominator in the four affine matrix entries. -/
def transform (matrix : Mat2) (curve : RationalCurve) : RationalCurve where
  numerator := scale matrix.a curve.numerator +
    scale matrix.b curve.denominator
  denominator := scale matrix.c curve.numerator +
    scale matrix.d curve.denominator

@[simp] theorem numeratorAt_transform
    (matrix : Mat2) (curve : RationalCurve) (parameter : Coordinate) :
    (curve.transform matrix).numeratorAt parameter =
      matrix.a * curve.numeratorAt parameter +
        matrix.b * curve.denominatorAt parameter := by
  simp only [transform, numeratorAt, eval_add, eval_scale]
  rfl

@[simp] theorem denominatorAt_transform
    (matrix : Mat2) (curve : RationalCurve) (parameter : Coordinate) :
    (curve.transform matrix).denominatorAt parameter =
      matrix.c * curve.numeratorAt parameter +
        matrix.d * curve.denominatorAt parameter := by
  simp only [transform, denominatorAt, eval_add, eval_scale]
  rfl

/-- At a non-pole parameter the homogeneous numerator is the affine point
times its displayed denominator. -/
theorem numeratorAt_eq_point_mul_denominatorAt
    (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    curve.numeratorAt parameter =
      curve.point parameter * curve.denominatorAt parameter := by
  unfold point
  symm
  calc
    (curve.numeratorAt parameter * (curve.denominatorAt parameter)⁻¹) *
        curve.denominatorAt parameter =
      curve.numeratorAt parameter *
        ((curve.denominatorAt parameter)⁻¹ *
          curve.denominatorAt parameter) :=
      RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
    _ = curve.numeratorAt parameter * 1 := by
      rw [RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel _
        denominatorNonzero]
    _ = curve.numeratorAt parameter :=
      RFAP.ConstructiveGaussian.Gaussian.mul_one _

/-- The transformed homogeneous denominator factors into the affine matrix
denominator and the old curve denominator. -/
theorem denominatorAt_transform_eq
    (matrix : Mat2) (curve : RationalCurve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (curve.transform matrix).denominatorAt parameter =
      CCL.RawParser.denominator matrix (curve.point parameter) *
        curve.denominatorAt parameter := by
  rw [denominatorAt_transform,
    curve.numeratorAt_eq_point_mul_denominatorAt parameter
      denominatorNonzero]
  unfold CCL.RawParser.denominator
  ring1

/-- Homogeneous curve transformation agrees exactly with affine homographic
evaluation wherever both displayed denominators are nonzero. -/
theorem point_transform
    (matrix : Mat2) (curve : RationalCurve) (parameter : Coordinate)
    (curveDenominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (matrixDenominatorNonzero :
      CCL.RawParser.denominator matrix (curve.point parameter) ≠
        0) :
    (curve.transform matrix).point parameter =
      CCL.RawParser.homographic matrix (curve.point parameter) := by
  have transformedDenominator :
      (curve.transform matrix).denominatorAt parameter =
        CCL.RawParser.denominator matrix
            (curve.point parameter) * curve.denominatorAt parameter :=
    denominatorAt_transform_eq matrix curve parameter
      curveDenominatorNonzero
  have transformedDenominatorNonzero :
      (curve.transform matrix).denominatorAt parameter ≠ 0 := by
    rw [transformedDenominator]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      matrixDenominatorNonzero curveDenominatorNonzero
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    transformedDenominatorNonzero
  calc
    (curve.transform matrix).point parameter *
        (curve.transform matrix).denominatorAt parameter =
      (curve.transform matrix).numeratorAt parameter := by
        unfold point
        rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        rw [RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel _
            transformedDenominatorNonzero,
          RFAP.ConstructiveGaussian.Gaussian.mul_one]
    _ = CCL.RawParser.numerator matrix (curve.point parameter) *
        curve.denominatorAt parameter := by
      rw [numeratorAt_transform,
        curve.numeratorAt_eq_point_mul_denominatorAt parameter
          curveDenominatorNonzero]
      unfold CCL.RawParser.numerator
      calc
        matrix.a *
              (curve.point parameter * curve.denominatorAt parameter) +
            matrix.b * curve.denominatorAt parameter =
          (matrix.a * curve.point parameter) *
              curve.denominatorAt parameter +
            matrix.b * curve.denominatorAt parameter := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        _ = (matrix.a * curve.point parameter + matrix.b) *
              curve.denominatorAt parameter :=
          (RFAP.ConstructiveGaussian.Gaussian.right_distrib _ _ _).symm
    _ = CCL.RawParser.homographic matrix
          (curve.point parameter) *
        (curve.transform matrix).denominatorAt parameter := by
      rw [transformedDenominator]
      unfold CCL.RawParser.homographic
      let numerator := CCL.RawParser.numerator matrix (curve.point parameter)
      let denominator :=
        CCL.RawParser.denominator matrix (curve.point parameter)
      let curveDenominator := curve.denominatorAt parameter
      change numerator * curveDenominator =
        (numerator * denominator⁻¹) * (denominator * curveDenominator)
      calc
        numerator * curveDenominator =
            numerator * 1 * curveDenominator := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
        _ = numerator * (denominator⁻¹ * denominator) *
            curveDenominator := by
          rw [RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel denominator
            matrixDenominatorNonzero]
        _ = numerator * ((denominator⁻¹ * denominator) *
            curveDenominator) :=
          RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
        _ = numerator * (denominator⁻¹ *
            (denominator * curveDenominator)) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        _ = (numerator * denominator⁻¹) *
            (denominator * curveDenominator) :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm

end RationalCurve

/-- The two polynomial accumulators carried by denominator-cleared Horner
evaluation. -/
structure ClearingState where
  value : GaussianPolynomial
  denominatorPower : GaussianPolynomial

def ClearingState.initial : ClearingState :=
  ⟨0, constant 1⟩

def ClearingState.step
    (numerator denominator : GaussianPolynomial)
    (state : ClearingState) (coefficient : Gaussian) : ClearingState :=
  let nextPower := state.denominatorPower * denominator
  { value := state.value * numerator + scale coefficient nextPower
    denominatorPower := nextPower }

def clearingState
    (p : GaussianPolynomial) (curve : RationalCurve) : ClearingState :=
  p.coeffs.foldl
    (ClearingState.step curve.numerator curve.denominator)
    ClearingState.initial

/-- Gaussian polynomial equal to the denominator-cleared rational
substitution. -/
def clearedEval
    (p : GaussianPolynomial) (curve : RationalCurve) : GaussianPolynomial :=
  (clearingState p curve).value

private theorem fold_clearing_spec
    (numerator denominator : GaussianPolynomial)
    (parameterValue parameter : Gaussian)
    (numeratorIdentity : numerator.eval parameter =
      parameterValue * denominator.eval parameter) :
    ∀ (coefficients : List Gaussian) (state : ClearingState)
      (accumulator : Gaussian),
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
      simp only [ClearingState.step, eval_add, eval_mul, eval_scale]
      rw [invariant, numeratorIdentity]
      ring1

/-- Exact semantics of denominator-cleared substitution at every parameter
where the curve denominator is explicitly nonzero. -/
theorem eval_clearedEval
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearedEval p curve).eval
        (RFAP.PathPolynomial.ofCoordinate parameter) =
      (clearingState p curve).denominatorPower.eval
          (RFAP.PathPolynomial.ofCoordinate parameter) *
        p.eval (curve.point parameter) := by
  let parameterGaussian :=
    RFAP.PathPolynomial.ofCoordinate parameter
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
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
      _ = curve.numeratorAt parameter * 1 := by
        rw [RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel _
          denominatorNonzero]
      _ = curve.numeratorAt parameter :=
        RFAP.ConstructiveGaussian.Gaussian.mul_one _
  have initialInvariant :
      ClearingState.initial.value.eval parameterGaussian =
        ClearingState.initial.denominatorPower.eval parameterGaussian * 0 := by
    simp only [ClearingState.initial, eval_zero, eval_constant,
      RFAP.ConstructiveGaussian.Gaussian.mul_zero]
  exact fold_clearing_spec curve.numerator curve.denominator
    (curve.point parameter) parameterGaussian numeratorIdentity p.coeffs
    ClearingState.initial 0 initialInvariant

private theorem fold_denominatorPower_eval
    (numerator denominator : GaussianPolynomial) (parameter : Gaussian) :
    ∀ (coefficients : List Gaussian) (state : ClearingState),
      (coefficients.foldl
          (ClearingState.step numerator denominator) state).denominatorPower.eval
            parameter =
        state.denominatorPower.eval parameter *
          denominator.eval parameter ^ coefficients.length
  | [], _state => by
      simp only [List.foldl_nil, List.length_nil, pow_zero,
        RFAP.ConstructiveGaussian.Gaussian.mul_one]
  | _coefficient :: coefficients, state => by
      simp only [List.foldl_cons, List.length_cons]
      rw [fold_denominatorPower_eval numerator denominator parameter
        coefficients
          (ClearingState.step numerator denominator state _coefficient)]
      simp only [ClearingState.step, eval_mul, pow_succ]
      ring1

/-- The denominator accumulator is exactly the displayed curve denominator
raised to the finite coefficient-list length. -/
theorem eval_denominatorPower
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate) :
    (clearingState p curve).denominatorPower.eval
        (RFAP.PathPolynomial.ofCoordinate parameter) =
      curve.denominatorAt parameter ^ p.coeffs.length := by
  change
    (p.coeffs.foldl
        (ClearingState.step curve.numerator curve.denominator)
          ClearingState.initial).denominatorPower.eval
          (RFAP.PathPolynomial.ofCoordinate parameter) = _
  rw [fold_denominatorPower_eval]
  simp only [ClearingState.initial, eval_constant,
    RFAP.ConstructiveGaussian.Gaussian.one_mul]
  rfl

private theorem fold_denominatorPower_ne
    (numerator denominator : GaussianPolynomial) (parameter : Gaussian)
    (denominatorNonzero : denominator.eval parameter ≠ 0) :
    ∀ (coefficients : List Gaussian) (state : ClearingState),
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
      simp only [ClearingState.step, eval_mul]
      exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
        stateNonzero denominatorNonzero

theorem denominatorPower_eval_ne
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (clearingState p curve).denominatorPower.eval
        (RFAP.PathPolynomial.ofCoordinate parameter) ≠ 0 := by
  apply fold_denominatorPower_ne curve.numerator curve.denominator
    (RFAP.PathPolynomial.ofCoordinate parameter)
    denominatorNonzero p.coeffs ClearingState.initial
  simp only [ClearingState.initial, eval_constant]
  intro oneZero
  have realOneZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re oneZero
  exact RFAP.ConstructiveFraction.zero_ne_one realOneZero.symm

/-- Real coordinate polynomial of the cleared substitution. -/
def clearedReal
    (p : GaussianPolynomial) (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.realPart (clearedEval p curve)

/-- Imaginary coordinate polynomial of the cleared substitution. -/
def clearedImag
    (p : GaussianPolynomial) (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.PathPolynomial.imagPart (clearedEval p curve)

theorem cleared_pair_zero_iff
    (p : GaussianPolynomial) (curve : RationalCurve)
    (parameter : Coordinate)
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
        (RFAP.PathPolynomial.ofCoordinate parameter) = 0 := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · change ((clearedEval p curve).eval
          (RFAP.PathPolynomial.ofCoordinate parameter)).re =
          (0 : Coordinate)
        simpa only [clearedReal,
          RFAP.PathPolynomial.eval_realPart] using realZero
      · change ((clearedEval p curve).eval
          (RFAP.PathPolynomial.ofCoordinate parameter)).im =
          (0 : Coordinate)
        simpa only [clearedImag,
          RFAP.PathPolynomial.eval_imagPart] using imaginaryZero
    rw [clearedZero] at semantics
    by_cases root : p.eval (curve.point parameter) = 0
    · exact root
    · have productNonzero :=
        RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
          powerNonzero root
      exact (productNonzero semantics.symm).elim
  · intro root
    have clearedZero : (clearedEval p curve).eval
        (RFAP.PathPolynomial.ofCoordinate parameter) = 0 := by
      rw [semantics, root,
        RFAP.ConstructiveGaussian.Gaussian.mul_zero]
    constructor
    · simp only [clearedReal,
        RFAP.PathPolynomial.eval_realPart, clearedZero, zero_re]
    · simp only [clearedImag,
        RFAP.PathPolynomial.eval_imagPart, clearedZero, zero_im]

end CCL.RationalCurve
