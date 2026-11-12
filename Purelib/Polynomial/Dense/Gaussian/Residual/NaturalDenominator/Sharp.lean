module
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Fraction.NaturalDenominator.LeastDenominator
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Nat.LCM
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Replicate
public import Purelib.Data.Rat.Fraction.Constants
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.UnitNumerator
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.LCM
public import Purelib.Polynomial.Dense.Gaussian.Denominator.Clearing.Polynomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

section
public section

/-!
# Sharpness witnesses for the denominator-height obstruction

For every positive coefficient scale `S`, positive common denominator `D`,
and degree `d`, the displayed monomial `(1/S) Z^d` evaluated at `1/D`
attains equality in the lower residual bound.  Thus the unit constant and the
exponents of both `S²` and `H^d` cannot be uniformly improved using only
these displayed parameters.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator.Sharp

/-- The real Gaussian coefficient 1/scale for a positive natural scale. -/
@[expose] def leadingCoefficient (scale : Nat) (positive : 0 < scale) : Gaussian.Basic.Canonical :=
  ⟨Fraction.UnitNumerator.unitCoordinate scale positive, 0⟩

/-- The reciprocal-scale leading coefficient is nonzero. -/
theorem leadingCoefficient_ne_zero (scale : Nat) (positive : 0 < scale) :
    leadingCoefficient scale positive ≠ 0 := by
  intro zero
  exact Fraction.UnitNumerator.unitCoordinate_ne_zero scale positive
    (congrArg Gaussian.Basic.re zero)

/-- Degree-`degree` monomial `(1 / scale) Z^degree`. -/
@[expose] def sharpPolynomial (degree scale : Nat) (scalePositive : 0 < scale) :
    (Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  ⟨leadingCoefficient scale scalePositive :: List.replicate degree 0⟩

/-- The reciprocal-scale monomial already has a normalized coefficient table. -/
@[simp] theorem sharpPolynomial_normalize (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).normalize =
      sharpPolynomial degree scale scalePositive := by
  apply Basic.DensePolynomial.ext
  change (leadingCoefficient scale scalePositive :: List.replicate degree 0).dropWhile
      (fun value => decide (value = 0)) = _
  exact Data.List.DropWhile.cons_of_false _ _ _
    (decide_eq_false (leadingCoefficient_ne_zero scale scalePositive))

/-- The reciprocal-scale monomial is nonzero. -/
@[simp] theorem sharpPolynomial_isZero (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).isZero = false := by
  change (sharpPolynomial degree scale scalePositive).normalize.coeffs.isEmpty =
    false
  rw [sharpPolynomial_normalize]
  rfl

/-- The reciprocal-scale monomial has exactly its supplied natural degree. -/
@[simp] theorem sharpPolynomial_natDegree (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).natDegree = degree := by
  unfold Basic.DensePolynomial.natDegree Basic.DensePolynomial.degreeCount
  rw [sharpPolynomial_normalize]
  simp only [sharpPolynomial, List.length_cons, Data.List.Replicate.length_replicate]
  omega

/-- The reciprocal-scale monomial evaluates to its leading coefficient times the supplied power. -/
theorem sharpPolynomial_eval (degree scale : Nat)
    (scalePositive : 0 < scale) (point : Gaussian.Basic.Canonical) :
    (sharpPolynomial degree scale scalePositive).eval point =
      leadingCoefficient scale scalePositive * point ^ degree := by
  unfold sharpPolynomial Basic.DensePolynomial.eval
  rw [show leadingCoefficient scale scalePositive :: List.replicate degree 0 =
      [leadingCoefficient scale scalePositive] ++ List.replicate degree 0
    from rfl]
  rw [Basic.DensePolynomial.evalCoeffs_append_replicate_zero]
  simp only [Basic.DensePolynomial.evalCoeffs, List.foldl_cons, List.foldl_nil, Gaussian.Basic.zero_mul,
    Gaussian.Basic.zero_add, -eq_self, -iff_self]
  rfl

section
/-- The least common denominator of the reciprocal-scale Gaussian coefficient is exactly the scale. -/
private theorem coefficientDenominator_leading (scale : Nat)
    (positive : 0 < scale) :
    Gaussian.Fraction.NaturalDenominator.LeastDenominator.coefficientDenominator
      (leadingCoefficient scale positive) = scale := by
  unfold Gaussian.Fraction.NaturalDenominator.LeastDenominator.coefficientDenominator leadingCoefficient
  rw [Fraction.UnitNumerator.representative_unitCoordinate scale positive,
    Fraction.Constants.representative_zero]
  simp only [Fraction.UnitNumerator.unitReduced, Fraction.Constants.zeroReduced]
  exact Data.Nat.LCM.lcm_one_right scale
/-- An all-zero coefficient table has least-common-multiple clearance scale one. -/
private theorem lcmScale_replicate_zero (count : Nat) :
    Denominator.Clearing.LCM.lcmScale
      (List.replicate count (0 : Gaussian.Basic.Canonical)) = 1 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, Denominator.Clearing.LCM.lcmScale,
        Gaussian.Fraction.NaturalDenominator.LeastDenominator.coefficientDenominator_zero,
          inductionHypothesis]
      exact Data.Nat.LCM.lcm_one_right 1
end

/-- The coefficient clearance scale of the sharpness monomial is exactly its supplied scale. -/
@[simp] theorem sharpPolynomial_coefficientScale (degree scale : Nat)
    (scalePositive : 0 < scale) :
    Denominator.Clearing.coefficientScale
      (sharpPolynomial degree scale scalePositive) = scale := by
  unfold Denominator.Clearing.coefficientScale
  rw [sharpPolynomial_normalize]
  change Denominator.Clearing.LCM.lcmScale
    (leadingCoefficient scale scalePositive :: List.replicate degree 0) = scale
  rw [Denominator.Clearing.LCM.lcmScale,
    coefficientDenominator_leading scale
      scalePositive,
    lcmScale_replicate_zero]
  exact Data.Nat.LCM.lcm_one_right scale

/-- Displayed sample `1 / denominator` with a real positive common
denominator. -/
@[expose] def sharpFraction (denominator : Nat) (positive : 0 < denominator) :
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator :=
  Gaussian.Basic.Canonical.Fraction.NaturalDenominator.grid 1 0 denominator positive

section
/-- The displayed sample's denominator height times its value quadrance equals one. -/
private theorem sharpFraction_norm_identity (denominator : Nat)
    (positive : 0 < denominator) :
    ((sharpFraction denominator positive).height : Fraction.Rational) *
        Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value = 1 := by
  have clearance :=
    (sharpFraction denominator positive).value_mul_denominator
  have normClearance := congrArg Gaussian.Norm.Basic.normSq clearance
  rw [Gaussian.Norm.Basic.normSq_mul,
    GaussianInt.normSq_toGaussian,
    GaussianInt.normSq_toGaussian] at normClearance
  change
    Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value *
        (GaussianInt.normNat
          (GaussianInt.ofNat denominator) :
            Fraction.Rational) =
      (GaussianInt.normNat
        (GaussianInt.ofNat 1) : Fraction.Rational)
    at normClearance
  rw [GaussianInt.normNat_ofNat,
    GaussianInt.normNat_ofNat] at normClearance
  have castOne : ((1 ^ 2 : Nat) : Fraction.Rational) = 1 := by
    rewrite [Fraction.Cast.natCast_eq_fromInt]
    decide +kernel
  have height : (sharpFraction denominator positive).height = denominator ^ 2 :=
    Gaussian.Basic.Canonical.Fraction.NaturalDenominator.grid_height 1 0 denominator positive
  calc
    ((sharpFraction denominator positive).height : Fraction.Rational) *
        Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value =
        ((denominator ^ 2 : Nat) : Fraction.Rational) *
          Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value :=
      congrArg (fun retained : Nat => (retained : Fraction.Rational) *
        Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value) height
    _ = Gaussian.Norm.Basic.normSq (sharpFraction denominator positive).value *
        ((denominator ^ 2 : Nat) : Fraction.Rational) := Fraction.Field.mul_comm _ _
    _ = 1 := normClearance.trans castOne
end

/-- The reciprocal-denominator sharpness sample is nonzero. -/
theorem sharpFraction_value_ne_zero (denominator : Nat)
    (positive : 0 < denominator) :
    (sharpFraction denominator positive).value ≠ 0 := by
  intro zero
  have identity := sharpFraction_norm_identity
    denominator positive
  rw [zero, Gaussian.Norm.Basic.normSq_zero, Fraction.Field.mul_zero_direct] at identity
  exact Fraction.Field.zero_ne_one identity

section
/-- The scale squared times the reciprocal-scale coefficient quadrance equals one. -/
private theorem leadingCoefficient_norm_identity (scale : Nat)
    (positive : 0 < scale) :
    (scale : Fraction.Rational) ^ 2 *
        Gaussian.Norm.Basic.normSq (leadingCoefficient scale positive) = 1 := by
  have clearance := Fraction.UnitNumerator.unitCoordinate_mul_scale scale positive
  calc
    (scale : Fraction.Rational) ^ 2 *
        Gaussian.Norm.Basic.normSq (leadingCoefficient scale positive) =
        (Fraction.UnitNumerator.unitCoordinate scale positive * (scale : Fraction.Rational)) ^ 2 := by
      change (scale : Fraction.Rational) ^ 2 *
        (Fraction.UnitNumerator.unitCoordinate scale positive ^ 2 + 0 ^ 2) = _
      ring1
    _ = (1 : Fraction.Rational) ^ 2 := by rw [clearance]
    _ = 1 := by ring1
end

/-- The sharpness monomial has nonzero residual at the reciprocal-denominator sample. -/
theorem sharpPolynomial_residual_ne_zero
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (sharpPolynomial degree scale scalePositive).eval
        (sharpFraction denominator denominatorPositive).value ≠ 0 := by
  rw [sharpPolynomial_eval]
  exact Gaussian.Field.mul_ne_zero_direct
    (leadingCoefficient_ne_zero scale scalePositive)
    (Gaussian.Power.pow_ne_zero_direct _
      (sharpFraction_value_ne_zero denominator denominatorPositive) degree)

/-- The family attains equality in the denominator-height obstruction for
every displayed positive coefficient scale, denominator, and degree. -/
theorem scaled_height_mul_residual_eq_one
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (Denominator.Clearing.coefficientScale
        (sharpPolynomial degree scale scalePositive) : Fraction.Rational) ^ 2 *
          ((sharpFraction denominator denominatorPositive).height :
            Fraction.Rational) ^
            (sharpPolynomial degree scale scalePositive).natDegree *
        Gaussian.Norm.Basic.normSq ((sharpPolynomial degree scale scalePositive).eval
          (sharpFraction denominator denominatorPositive).value) = 1 := by
  rw [sharpPolynomial_coefficientScale, sharpPolynomial_natDegree,
    sharpPolynomial_eval, Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow]
  have coefficientIdentity :=
    leadingCoefficient_norm_identity scale
      scalePositive
  have sampleIdentity := sharpFraction_norm_identity
    denominator denominatorPositive
  induction degree with
  | zero =>
      simp only [pow_zero, Fraction.Field.mul_one_direct]
      exact coefficientIdentity
  | succ degree inductionHypothesis =>
      rw [pow_succ ((sharpFraction denominator denominatorPositive).height : Fraction.Rational) degree,
        pow_succ (Gaussian.Norm.Basic.normSq (sharpFraction denominator denominatorPositive).value) degree]
      calc
        (scale : Fraction.Rational) ^ 2 *
            (((sharpFraction denominator denominatorPositive).height : Fraction.Rational) ^ degree *
              ((sharpFraction denominator denominatorPositive).height : Fraction.Rational)) *
            (Gaussian.Norm.Basic.normSq (leadingCoefficient scale scalePositive) *
              (Gaussian.Norm.Basic.normSq (sharpFraction denominator denominatorPositive).value ^ degree *
                Gaussian.Norm.Basic.normSq (sharpFraction denominator denominatorPositive).value)) =
            ((scale : Fraction.Rational) ^ 2 *
              ((sharpFraction denominator denominatorPositive).height : Fraction.Rational) ^ degree *
              (Gaussian.Norm.Basic.normSq (leadingCoefficient scale scalePositive) *
                Gaussian.Norm.Basic.normSq (sharpFraction denominator denominatorPositive).value ^ degree)) *
              (((sharpFraction denominator denominatorPositive).height : Fraction.Rational) *
                Gaussian.Norm.Basic.normSq (sharpFraction denominator denominatorPositive).value) := by
          ring1
        _ = 1 := by
          rewrite [inductionHypothesis, sampleIdentity]
          exact Fraction.Field.mul_one_direct 1

end Purelib.Polynomial.Dense.Gaussian.Residual.NaturalDenominator.Sharp

end
