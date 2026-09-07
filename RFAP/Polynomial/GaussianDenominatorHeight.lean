import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.DenominatorHeight
import RFAP.Approximation.ReducedGaussianFraction

/-!
# Intrinsic Gaussian-denominator residual bounds

This module repeats the finite homogeneous-evaluation argument with a
displayed Gaussian-integer denominator.  It also gives exact conversions in
both directions between Gaussian-denominator records and the older positive
natural common-denominator records.
-/

namespace RFAP.GaussianDenominatorHeight

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev CommonFraction := RFAP.ConstructiveGaussianHeight.Fraction
abbrev GaussianFraction := RFAP.HurwitzRational.Fraction
abbrev ReducedGaussianFraction :=
  RFAP.ReducedGaussianFraction.CanonicalFraction
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.ComputablePolynomial.DensePolynomial

/-- High-to-low homogeneous evaluation with a Gaussian-integer denominator. -/
def homogeneousEval (numerator denominator : GaussianInt) :
    List GaussianInt → GaussianInt
  | [] => 0
  | coefficient :: remaining =>
      coefficient * numerator ^ remaining.length +
        denominator * homogeneousEval numerator denominator remaining

/-- Gaussian homogeneous evaluation is ordinary evaluation multiplied by the
exact Gaussian denominator power. -/
theorem homogeneousEval_cons_eq_scaled
    (fraction : GaussianFraction) (coefficient : GaussianInt)
    (remaining : List GaussianInt) :
    toGaussian
        (homogeneousEval fraction.numerator fraction.denominator
          (coefficient :: remaining)) =
      toGaussian fraction.denominator ^ remaining.length *
        RFAP.DenominatorHeight.evalIntegers fraction.value
          (coefficient :: remaining) := by
  induction remaining generalizing coefficient with
  | nil =>
      simp [homogeneousEval, RFAP.DenominatorHeight.evalIntegers]
  | cons next remaining inductionHypothesis =>
      have cleared := fraction.value_mul_denominator
      rw [homogeneousEval, toGaussian_add, toGaussian_mul]
      rw [RFAP.DenominatorHeight.GaussianInt.toGaussian_pow,
        toGaussian_mul, inductionHypothesis]
      rw [RFAP.DenominatorHeight.evalIntegers_cons fraction.value coefficient
        (next :: remaining), List.length_cons, pow_succ]
      rw [← cleared]
      rw [mul_pow, pow_succ]
      ring1

/-- Explicit Gaussian-integer residual numerator for a displayed Gaussian
fraction. -/
def residualNumerator (p : GaussianPolynomial) (fraction : GaussianFraction) :
    GaussianInt :=
  homogeneousEval fraction.numerator fraction.denominator
    (RFAP.DenominatorHeight.lcmClear p.normalize.coeffs).coefficients

theorem residualNumerator_identity
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) :
    toGaussian (residualNumerator p fraction) =
      toGaussian fraction.denominator ^ p.natDegree *
        (⟨(RFAP.DenominatorHeight.coefficientScale p : Coordinate), 0⟩ *
          p.eval fraction.value) := by
  obtain ⟨tail, coefficients, tailLength⟩ :=
    normalized_coeffs_shape nonzero
  unfold residualNumerator RFAP.DenominatorHeight.coefficientScale
  rw [show p.normalize.coeffs = p.leadingCoeff :: tail from coefficients]
  change
    toGaussian
        (homogeneousEval fraction.numerator fraction.denominator
          (RFAP.DenominatorHeight.lcmClear
            (p.leadingCoeff :: tail)).coefficients) = _
  rw [show (RFAP.DenominatorHeight.lcmClear
      (p.leadingCoeff :: tail)).coefficients =
        RFAP.DenominatorHeight.scaledGaussianCoefficient
            (RFAP.DenominatorHeight.lcmScale (p.leadingCoeff :: tail))
            p.leadingCoeff ::
          tail.map (RFAP.DenominatorHeight.scaledGaussianCoefficient
            (RFAP.DenominatorHeight.lcmScale (p.leadingCoeff :: tail)))
    from rfl]
  rw [homogeneousEval_cons_eq_scaled]
  have remainingLength :
      (tail.map (RFAP.DenominatorHeight.scaledGaussianCoefficient
        (RFAP.DenominatorHeight.lcmScale
          (p.leadingCoeff :: tail)))).length = p.natDegree := by
    simp only [List.length_map, tailLength]
  rw [remainingLength]
  change
    toGaussian fraction.denominator ^ p.natDegree *
        RFAP.DenominatorHeight.evalIntegers fraction.value
          (RFAP.DenominatorHeight.lcmClear
            (p.leadingCoeff :: tail)).coefficients = _
  rw [RFAP.DenominatorHeight.eval_lcmClear]
  rw [← eval_normalize]
  unfold eval
  rw [coefficients]

/-- The intrinsic Gaussian-denominator scaled residual is exactly the norm of
the displayed integral numerator. -/
theorem scaled_height_mul_residual_eq_normNat
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) :
    (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
          (fraction.height : Coordinate) ^ p.natDegree *
        normSq (p.eval fraction.value) =
      (normNat (residualNumerator p fraction) : Coordinate) := by
  have denominatorNorm :
      normSq (toGaussian fraction.denominator) =
        (fraction.height : Coordinate) := by
    exact normSq_toGaussian fraction.denominator
  have scaleNorm :
      normSq
          (⟨(RFAP.DenominatorHeight.coefficientScale p : Coordinate), 0⟩ :
            Gaussian) =
        (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 := by
    change
      (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 + 0 ^ 2 = _
    ring1
  rw [← normSq_toGaussian, residualNumerator_identity p nonzero fraction,
    normSq_mul, normSq_mul, normSq_pow, denominatorNorm, scaleNorm]
  ring1

theorem residualNumerator_ne_zero
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    residualNumerator p fraction ≠ 0 := by
  intro numeratorZero
  have embeddedZero := congrArg toGaussian numeratorZero
  rw [toGaussian_zero, residualNumerator_identity p nonzero fraction]
    at embeddedZero
  have denominatorNonzero := fraction.denominatorGaussianNonzero
  have scalePositive := RFAP.DenominatorHeight.coefficientScale_pos p
  have scaleNonzero :
      (⟨(RFAP.DenominatorHeight.coefficientScale p : Coordinate), 0⟩ :
        Gaussian) ≠ 0 := by
    intro zero
    have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re zero
    have scaleZero := RFAP.ConstructiveFraction.natCast_injective_direct
      (realZero.trans (Nat.cast_zero).symm)
    exact (Nat.ne_of_gt scalePositive) scaleZero
  have productNonzero := RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct _
      denominatorNonzero p.natDegree)
    (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct scaleNonzero
      residualNonzero)
  exact productNonzero embeddedZero

/-- Intrinsic Gaussian-denominator height obstruction. -/
theorem one_le_scaled_height_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
        (fraction.height : Coordinate) ^ p.natDegree *
          normSq (p.eval fraction.value) := by
  have numeratorPositive := normNat_pos
    (residualNumerator_ne_zero p nonzero fraction residualNonzero)
  have castLower : (1 : Coordinate) ≤
      (normNat (residualNumerator p fraction) : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct numeratorPositive
  rw [← scaled_height_mul_residual_eq_normNat p nonzero fraction]
    at castLower
  exact castLower

/-! ## Canonically reduced denominator height -/

/-- Execute Gaussian Euclidean reduction and deterministic unit
canonicalisation on a displayed fraction. -/
def canonicalReduction (fraction : GaussianFraction) :
    ReducedGaussianFraction :=
  RFAP.ReducedGaussianFraction.reduceCanonical fraction

/-- Denominator quadrance after executable Gaussian Euclidean reduction.
This is independent of the displayed numerator--denominator presentation. -/
def intrinsicHeight (fraction : GaussianFraction) : Nat :=
  (canonicalReduction fraction).height

/-- Homogeneous residual numerator evaluated at the canonical reduced
coordinates. -/
def intrinsicResidualNumerator
    (p : GaussianPolynomial) (fraction : GaussianFraction) : GaussianInt :=
  residualNumerator p (canonicalReduction fraction).displayed

theorem canonicalReduction_value (fraction : GaussianFraction) :
    (canonicalReduction fraction).value = fraction.value :=
  RFAP.ReducedGaussianFraction.reduceCanonical_value fraction

theorem intrinsicHeight_pos (fraction : GaussianFraction) :
    0 < intrinsicHeight fraction := by
  unfold intrinsicHeight canonicalReduction
  exact normNat_pos
    (RFAP.ReducedGaussianFraction.reduceCanonical fraction).denominatorNonzero

/-- Canonical reduction never increases displayed denominator quadrance. -/
theorem intrinsicHeight_le_height (fraction : GaussianFraction) :
    intrinsicHeight fraction ≤ fraction.height :=
  RFAP.ReducedGaussianFraction.reduceCanonical_height_le fraction

/-- Equal exact values have equal canonical reduced denominator heights. -/
theorem intrinsicHeight_eq_of_value_eq
    (left right : GaussianFraction) (valueEqual : left.value = right.value) :
    intrinsicHeight left = intrinsicHeight right :=
  RFAP.ReducedGaussianFraction.reduceCanonical_height_eq_of_value_eq
    left right valueEqual

/-- The residual obstruction computed at canonical reduced coordinates is an
exact Gaussian-integer norm identity. -/
theorem scaled_intrinsicHeight_mul_residual_eq_normNat
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction) :
    (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
          (intrinsicHeight fraction : Coordinate) ^ p.natDegree *
        normSq (p.eval fraction.value) =
      (normNat (intrinsicResidualNumerator p fraction) : Coordinate) := by
  have identity := scaled_height_mul_residual_eq_normNat p nonzero
    (canonicalReduction fraction).displayed
  change
    (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
          ((canonicalReduction fraction).height : Coordinate) ^ p.natDegree *
        normSq (p.eval fraction.value) =
      (normNat
        (residualNumerator p (canonicalReduction fraction).displayed) :
          Coordinate)
  rw [← canonicalReduction_value fraction]
  exact identity

/-- Intrinsic reduced Gaussian-denominator height obstruction. -/
theorem one_le_scaled_intrinsicHeight_mul_residual
    (p : GaussianPolynomial) (nonzero : p.isZero = false)
    (fraction : GaussianFraction)
    (residualNonzero : p.eval fraction.value ≠ 0) :
    (1 : Coordinate) ≤
      (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
        (intrinsicHeight fraction : Coordinate) ^ p.natDegree *
          normSq (p.eval fraction.value) := by
  have reducedResidualNonzero :
      p.eval (canonicalReduction fraction).displayed.value ≠ 0 := by
    change p.eval (canonicalReduction fraction).value ≠ 0
    rw [canonicalReduction_value]
    exact residualNonzero
  have bound := one_le_scaled_height_mul_residual p nonzero
    (canonicalReduction fraction).displayed reducedResidualNonzero
  change
    (1 : Coordinate) ≤
      (RFAP.DenominatorHeight.coefficientScale p : Coordinate) ^ 2 *
        ((canonicalReduction fraction).height : Coordinate) ^ p.natDegree *
          normSq (p.eval fraction.value)
  rw [← canonicalReduction_value fraction]
  exact bound

/-! ## Exact presentation conversions -/

/-- Regard a positive natural common denominator as a real Gaussian-integer
denominator. -/
def ofCommon (fraction : CommonFraction) : GaussianFraction :=
  { numerator := fraction.numerator
    denominator := ofNat fraction.denominator
    denominatorNonzero := by
      intro zero
      have realZero := congrArg (fun value : GaussianInt => value.re) zero
      exact (Nat.ne_of_gt fraction.denominatorPositive)
        (Int.ofNat.inj realZero) }

@[simp] theorem ofCommon_height (fraction : CommonFraction) :
    (ofCommon fraction).height = fraction.height := by
  exact normNat_ofNat fraction.denominator

theorem ofCommon_value (fraction : CommonFraction) :
    (ofCommon fraction).value = fraction.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    (show toGaussian (ofNat fraction.denominator) ≠ 0 by
      intro zero
      exact (ofCommon fraction).denominatorNonzero
        (toGaussian_eq_zero.mp zero))
  calc
    (ofCommon fraction).value * toGaussian (ofNat fraction.denominator) =
        toGaussian fraction.numerator := by
      simpa only [ofCommon] using (ofCommon fraction).value_mul_denominator
    _ = fraction.value * toGaussian (ofNat fraction.denominator) :=
      fraction.value_mul_denominator.symm

/-- Rationalize a Gaussian denominator by multiplication with its displayed
conjugate. -/
def toCommon (fraction : GaussianFraction) : CommonFraction :=
  { numerator := fraction.numerator *
      RFAP.ConstructiveGaussianHeight.GaussianInt.conj fraction.denominator
    denominator := normNat fraction.denominator
    denominatorPositive := normNat_pos fraction.denominatorNonzero }

@[simp] theorem toCommon_height (fraction : GaussianFraction) :
    (toCommon fraction).height = fraction.height ^ 2 := by
  rfl

theorem toCommon_value (fraction : GaussianFraction) :
    (toCommon fraction).value = fraction.value := by
  let denominatorNorm := normNat fraction.denominator
  have denominatorGaussianNonzero : toGaussian (ofNat denominatorNorm) ≠ 0 := by
    intro zero
    have integerZero := toGaussian_eq_zero.mp zero
    have realZero := congrArg (fun value : GaussianInt => value.re) integerZero
    exact (Nat.ne_of_gt (normNat_pos fraction.denominatorNonzero))
      (Int.ofNat.inj realZero)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    denominatorGaussianNonzero
  calc
    (toCommon fraction).value * toGaussian (ofNat denominatorNorm) =
        toGaussian
          (fraction.numerator *
            RFAP.ConstructiveGaussianHeight.GaussianInt.conj
              fraction.denominator) :=
      (toCommon fraction).value_mul_denominator
    _ = toGaussian fraction.numerator *
          toGaussian
            (RFAP.ConstructiveGaussianHeight.GaussianInt.conj
              fraction.denominator) :=
      toGaussian_mul _ _
    _ = (fraction.value * toGaussian fraction.denominator) *
          toGaussian
            (RFAP.ConstructiveGaussianHeight.GaussianInt.conj
              fraction.denominator) := by
      rw [fraction.value_mul_denominator]
    _ = fraction.value *
          (toGaussian fraction.denominator *
            toGaussian
              (RFAP.ConstructiveGaussianHeight.GaussianInt.conj
                fraction.denominator)) := by
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
    _ = fraction.value * toGaussian (ofNat denominatorNorm) := by
      rw [← toGaussian_mul,
        RFAP.ConstructiveGaussianHeight.GaussianInt.mul_conj]

end RFAP.GaussianDenominatorHeight
