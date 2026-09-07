import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.DenominatorHeight

/-!
# Sharpness witnesses for the denominator-height obstruction

For every positive coefficient scale `S`, positive common denominator `D`,
and degree `d`, the displayed monomial `(1/S) Z^d` evaluated at `1/D`
attains equality in the lower residual bound.  Thus the unit constant and the
exponents of both `S²` and `H^d` cannot be uniformly improved using only
these displayed parameters.
-/

namespace RFAP.DenominatorHeightSharp

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Fraction := RFAP.ConstructiveGaussianHeight.Fraction

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- Gcd-reduced record for `1 / scale`. -/
def unitReduced (scale : Nat) (positive : 0 < scale) :
    RFAP.ConstructiveFraction.ReducedFraction :=
  { num := 1
    den := scale
    den_pos := positive
    reduced := ⟨⟨1, 0, by
      simp only [Int.natAbs_one, Int.one_mul, Int.zero_mul,
        Int.add_zero, Int.natCast_one]⟩⟩ }

/-- The exact constructive rational `1 / scale`, entered through already
reduced finite data. -/
def unitCoordinate (scale : Nat) (positive : 0 < scale) : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction (unitReduced scale positive).toFraction

@[simp] theorem representative_unitCoordinate (scale : Nat)
    (positive : 0 < scale) :
    RFAP.ConstructiveFraction.representative
        (unitCoordinate scale positive) = unitReduced scale positive := by
  exact RFAP.ConstructiveFraction.representative_of_reduced _

theorem unitCoordinate_mul_scale (scale : Nat) (positive : 0 < scale) :
    unitCoordinate scale positive * (scale : Coordinate) = 1 := by
  have clearance := RFAP.ConstructiveFraction.representative_mul_den
    (unitCoordinate scale positive)
  rw [representative_unitCoordinate scale positive] at clearance
  exact clearance

theorem unitCoordinate_ne_zero (scale : Nat) (positive : 0 < scale) :
    unitCoordinate scale positive ≠ 0 := by
  intro zero
  have clearance := unitCoordinate_mul_scale scale positive
  rw [zero, RFAP.ConstructiveFraction.zero_mul_direct] at clearance
  exact RFAP.ConstructiveFraction.zero_ne_one clearance

def leadingCoefficient (scale : Nat) (positive : 0 < scale) : Gaussian :=
  ⟨unitCoordinate scale positive, 0⟩

theorem leadingCoefficient_ne_zero (scale : Nat) (positive : 0 < scale) :
    leadingCoefficient scale positive ≠ 0 := by
  intro zero
  exact unitCoordinate_ne_zero scale positive
    (congrArg RFAP.ConstructiveGaussian.Gaussian.re zero)

/-- Degree-`degree` monomial `(1 / scale) Z^degree`. -/
def sharpPolynomial (degree scale : Nat) (scalePositive : 0 < scale) :
    GaussianPolynomial :=
  ⟨leadingCoefficient scale scalePositive :: List.replicate degree 0⟩

@[simp] theorem sharpPolynomial_normalize (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).normalize =
      sharpPolynomial degree scale scalePositive := by
  apply RFAP.ComputablePolynomial.DensePolynomial.ext
  simp [sharpPolynomial, normalize,
    leadingCoefficient_ne_zero scale scalePositive]

@[simp] theorem sharpPolynomial_isZero (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).isZero = false := by
  change (sharpPolynomial degree scale scalePositive).normalize.coeffs.isEmpty =
    false
  rw [sharpPolynomial_normalize]
  rfl

@[simp] theorem sharpPolynomial_natDegree (degree scale : Nat)
    (scalePositive : 0 < scale) :
    (sharpPolynomial degree scale scalePositive).natDegree = degree := by
  unfold natDegree degreeCount
  rw [sharpPolynomial_normalize]
  simp only [sharpPolynomial, List.length_cons, List.length_replicate]
  omega

theorem sharpPolynomial_eval (degree scale : Nat)
    (scalePositive : 0 < scale) (point : Gaussian) :
    (sharpPolynomial degree scale scalePositive).eval point =
      leadingCoefficient scale scalePositive * point ^ degree := by
  unfold sharpPolynomial eval
  rw [show leadingCoefficient scale scalePositive :: List.replicate degree 0 =
      [leadingCoefficient scale scalePositive] ++ List.replicate degree 0
    from rfl]
  rw [evalCoeffs_append_replicate_zero]
  simp only [evalCoeffs, List.foldl_cons, List.foldl_nil, zero_mul, zero_add]

private def zeroReduced : RFAP.ConstructiveFraction.ReducedFraction :=
  { num := 0
    den := 1
    den_pos := by decide
    reduced := ⟨⟨0, 1, by
      simp only [Int.natAbs_zero, Int.zero_mul, Int.natCast_one,
        Int.mul_one, Int.zero_add]⟩⟩ }

private theorem representative_zero :
    RFAP.ConstructiveFraction.representative (0 : Coordinate) = zeroReduced := by
  change RFAP.ConstructiveFraction.representative
    (RFAP.ConstructiveFraction.ofFraction zeroReduced.toFraction) = zeroReduced
  exact RFAP.ConstructiveFraction.representative_of_reduced _

private theorem coefficientDenominator_leading (scale : Nat)
    (positive : 0 < scale) :
    RFAP.DenominatorHeight.coefficientDenominator
      (leadingCoefficient scale positive) = scale := by
  unfold RFAP.DenominatorHeight.coefficientDenominator leadingCoefficient
  rw [representative_unitCoordinate scale positive, representative_zero]
  simp only [unitReduced, zeroReduced]
  exact RFAP.CanonicalLCM.lcm_one_right scale

private theorem coefficientDenominator_zero :
    RFAP.DenominatorHeight.coefficientDenominator (0 : Gaussian) = 1 := by
  unfold RFAP.DenominatorHeight.coefficientDenominator
  change RFAP.CanonicalLCM.lcm
    (RFAP.ConstructiveFraction.representative (0 : Coordinate)).den
    (RFAP.ConstructiveFraction.representative (0 : Coordinate)).den = 1
  rw [representative_zero]
  exact RFAP.CanonicalLCM.lcm_one_right 1

private theorem lcmScale_replicate_zero (count : Nat) :
    RFAP.DenominatorHeight.lcmScale
      (List.replicate count (0 : Gaussian)) = 1 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, RFAP.DenominatorHeight.lcmScale,
        coefficientDenominator_zero, inductionHypothesis]
      exact RFAP.CanonicalLCM.lcm_one_right 1

@[simp] theorem sharpPolynomial_coefficientScale (degree scale : Nat)
    (scalePositive : 0 < scale) :
    RFAP.DenominatorHeight.coefficientScale
      (sharpPolynomial degree scale scalePositive) = scale := by
  unfold RFAP.DenominatorHeight.coefficientScale
  rw [sharpPolynomial_normalize]
  change RFAP.DenominatorHeight.lcmScale
    (leadingCoefficient scale scalePositive :: List.replicate degree 0) = scale
  rw [RFAP.DenominatorHeight.lcmScale,
    coefficientDenominator_leading scale scalePositive,
    lcmScale_replicate_zero]
  exact RFAP.CanonicalLCM.lcm_one_right scale

/-- Displayed sample `1 / denominator` with a real positive common
denominator. -/
def sharpFraction (denominator : Nat) (positive : 0 < denominator) : Fraction :=
  RFAP.ConstructiveGaussianHeight.Fraction.grid 1 0 denominator positive

private theorem sharpFraction_norm_identity (denominator : Nat)
    (positive : 0 < denominator) :
    ((sharpFraction denominator positive).height : Coordinate) *
        normSq (sharpFraction denominator positive).value = 1 := by
  have clearance :=
    (sharpFraction denominator positive).value_mul_denominator
  have normClearance := congrArg normSq clearance
  rw [normSq_mul,
    RFAP.ConstructiveGaussianHeight.GaussianInt.normSq_toGaussian,
    RFAP.ConstructiveGaussianHeight.GaussianInt.normSq_toGaussian] at normClearance
  change
    normSq (sharpFraction denominator positive).value *
        (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
          (RFAP.ConstructiveGaussianHeight.GaussianInt.ofNat denominator) :
            Coordinate) =
      (RFAP.ConstructiveGaussianHeight.GaussianInt.normNat
        (RFAP.ConstructiveGaussianHeight.GaussianInt.ofNat 1) : Coordinate)
    at normClearance
  rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_ofNat,
    RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_ofNat] at normClearance
  change
    normSq (sharpFraction denominator positive).value *
        (denominator ^ 2 : Nat) = 1 at normClearance
  calc
    ((sharpFraction denominator positive).height : Coordinate) *
        normSq (sharpFraction denominator positive).value =
        normSq (sharpFraction denominator positive).value *
          (denominator ^ 2 : Nat) := by
      change (denominator ^ 2 : Nat) *
          normSq (sharpFraction denominator positive).value = _
      ring1
    _ = 1 := normClearance

theorem sharpFraction_value_ne_zero (denominator : Nat)
    (positive : 0 < denominator) :
    (sharpFraction denominator positive).value ≠ 0 := by
  intro zero
  have identity := sharpFraction_norm_identity denominator positive
  rw [zero, normSq_zero, RFAP.ConstructiveFraction.mul_zero_direct] at identity
  exact RFAP.ConstructiveFraction.zero_ne_one identity

private theorem leadingCoefficient_norm_identity (scale : Nat)
    (positive : 0 < scale) :
    (scale : Coordinate) ^ 2 *
        normSq (leadingCoefficient scale positive) = 1 := by
  have clearance := unitCoordinate_mul_scale scale positive
  calc
    (scale : Coordinate) ^ 2 *
        normSq (leadingCoefficient scale positive) =
        (unitCoordinate scale positive * (scale : Coordinate)) ^ 2 := by
      change (scale : Coordinate) ^ 2 *
        (unitCoordinate scale positive ^ 2 + 0 ^ 2) = _
      ring1
    _ = (1 : Coordinate) ^ 2 := by rw [clearance]
    _ = 1 := by ring1

theorem sharpPolynomial_residual_ne_zero
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (sharpPolynomial degree scale scalePositive).eval
        (sharpFraction denominator denominatorPositive).value ≠ 0 := by
  rw [sharpPolynomial_eval]
  exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (leadingCoefficient_ne_zero scale scalePositive)
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct _
      (sharpFraction_value_ne_zero denominator denominatorPositive) degree)

/-- The family attains equality in the denominator-height obstruction for
every displayed positive coefficient scale, denominator, and degree. -/
theorem scaled_height_mul_residual_eq_one
    (degree scale denominator : Nat) (scalePositive : 0 < scale)
    (denominatorPositive : 0 < denominator) :
    (RFAP.DenominatorHeight.coefficientScale
        (sharpPolynomial degree scale scalePositive) : Coordinate) ^ 2 *
          ((sharpFraction denominator denominatorPositive).height :
            Coordinate) ^
            (sharpPolynomial degree scale scalePositive).natDegree *
        normSq ((sharpPolynomial degree scale scalePositive).eval
          (sharpFraction denominator denominatorPositive).value) = 1 := by
  rw [sharpPolynomial_coefficientScale, sharpPolynomial_natDegree,
    sharpPolynomial_eval, normSq_mul, normSq_pow]
  calc
    (scale : Coordinate) ^ 2 *
          ((sharpFraction denominator denominatorPositive).height :
            Coordinate) ^ degree *
        (normSq (leadingCoefficient scale scalePositive) *
          normSq (sharpFraction denominator denominatorPositive).value ^
            degree) =
        ((scale : Coordinate) ^ 2 *
          normSq (leadingCoefficient scale scalePositive)) *
        (((sharpFraction denominator denominatorPositive).height :
          Coordinate) *
          normSq (sharpFraction denominator denominatorPositive).value) ^
            degree := by
      rw [mul_pow]
      ring1
    _ = 1 := by
      rw [leadingCoefficient_norm_identity,
        sharpFraction_norm_identity]
      simp only [one_pow]
      ring1

end RFAP.DenominatorHeightSharp
