module

public import Purelib.Calculus.Jet.Quadratic.SquareRoot
public import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Uniform bounds on the original affine inverse-root certificate

Both original residual factors, the actual coefficient quadrance and positive
source, target and signed-sum margins determine fixed finite ceilings. The
bounds concern the original constructor's retained factor; neither its actual
readings nor its root/reciprocal composition is rebuilt or replaced.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.SquareRoot

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Both residual factors and the coefficient ceiling determine the signed-sum root-movement ceiling. -/
@[expose] def movementCeiling (coefficientCeiling sumFloor firstFactor lastFactor : Fraction.Rational) :
    Fraction.Rational :=
  (4 * (firstFactor + lastFactor) + 2 * coefficientCeiling) * sumFloor⁻¹

/-- The original source margin pays the squared movement and both residual factors in the root remainder ceiling. -/
@[expose] def remainderCeiling (coefficientCeiling sourceFloor sumFloor firstFactor lastFactor : Fraction.Rational) :
    Fraction.Rational :=
  2 * (2 * (firstFactor + lastFactor) + movementCeiling coefficientCeiling sumFloor firstFactor lastFactor ^ 2) *
    sourceFloor⁻¹

/-- The original Gaussian half and source margin bound the root slope before reciprocal composition. -/
@[expose] def rootSlopeCeiling (coefficientCeiling sourceFloor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq half * coefficientCeiling * sourceFloor⁻¹

/-- Source, target and sum margins bound the original inverse-root composition's finite remainder factor. -/
@[expose] def inverseCeiling
    (coefficientCeiling sourceFloor targetFloor sumFloor firstFactor lastFactor : Fraction.Rational) :
    Fraction.Rational :=
  let remainder := remainderCeiling coefficientCeiling sourceFloor sumFloor firstFactor lastFactor
  2 * (sourceFloor⁻¹ ^ 2 * remainder + sourceFloor⁻¹ ^ 2 * targetFloor⁻¹ *
    (2 * (rootSlopeCeiling coefficientCeiling sourceFloor + remainder)) ^ 2)

/-- Positive source and target margins give a nonnegative original inverse-composition ceiling.

The coefficient and residual factors are nonnegative. The signed-sum margin
remains the same explicit computed input; its movement contribution is squared.
-/
theorem inverseCeiling_nonnegative
    {coefficientCeiling sourceFloor targetFloor sumFloor firstFactor lastFactor : Fraction.Rational}
    (coefficientNonnegative : 0 ≤ coefficientCeiling) (sourcePositive : 0 < sourceFloor)
    (targetPositive : 0 < targetFloor) (sumPositive : 0 < sumFloor)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    0 ≤ inverseCeiling coefficientCeiling sourceFloor targetFloor sumFloor firstFactor lastFactor := by
  have sourceInverse := (Fraction.Order.Field.inv_pos_direct sourcePositive).le
  have targetInverse := (Fraction.Order.Field.inv_pos_direct targetPositive).le
  have movementNonnegative : 0 ≤ movementCeiling coefficientCeiling sumFloor firstFactor lastFactor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
          (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
          coefficientNonnegative))
      (Fraction.Order.Field.inv_pos_direct sumPositive).le
  have remainderNonnegative : 0 ≤ remainderCeiling coefficientCeiling sourceFloor sumFloor firstFactor lastFactor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
            (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
          (Arithmetic.pow_nonneg_direct movementNonnegative 2))) sourceInverse
  have slopeNonnegative : 0 ≤ rootSlopeCeiling coefficientCeiling sourceFloor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg half) coefficientNonnegative) sourceInverse
  have sensitivityNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct slopeNonnegative remainderNonnegative)
  exact Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.pow_nonneg_direct sourceInverse 2) remainderNonnegative)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.pow_nonneg_direct sourceInverse 2) targetInverse)
        (Arithmetic.pow_nonneg_direct sensitivityNonnegative 2)))

/-- The actual displayed root-movement factor obeys the coefficient and signed-sum margin ceiling. -/
theorem movementFactor_le_ceiling {first last coefficient : Canonical}
    {firstFactor lastFactor coefficientCeiling sumFloor : Fraction.Rational}
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (coefficientBound : Norm.Basic.normSq coefficient ≤ coefficientCeiling)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last)) :
    movementFactor first last coefficient firstFactor lastFactor ≤
      movementCeiling coefficientCeiling sumFloor firstFactor lastFactor := by
  have commonNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
    (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative)
  have numeratorBound := Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl (4 * (firstFactor + lastFactor)))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  have numeratorNonnegative := Arithmetic.add_le_add_direct commonNonnegative
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
      (Norm.Basic.normSq_nonneg coefficient))
  exact Arithmetic.mul_le_mul_direct numeratorBound
    (Norm.Reciprocal.normSq_le sumPositive sumLower) (Norm.Basic.normSq_nonneg _)
    (numeratorNonnegative.trans numeratorBound)

/-- The actual root remainder factor obeys the original source and signed-sum margin ceiling. -/
theorem remainderFactor_le_ceiling {first last coefficient : Canonical}
    {firstFactor lastFactor coefficientCeiling sourceFloor sumFloor : Fraction.Rational}
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (coefficientBound : Norm.Basic.normSq coefficient ≤ coefficientCeiling)
    (sourcePositive : 0 < sourceFloor) (sourceLower : sourceFloor ≤ Norm.Basic.normSq first)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last)) :
    remainderFactor first last coefficient firstFactor lastFactor ≤
      remainderCeiling coefficientCeiling sourceFloor sumFloor firstFactor lastFactor := by
  have movementBound := movementFactor_le_ceiling firstNonnegative lastNonnegative coefficientBound
    sumPositive sumLower
  have movementNonnegative : 0 ≤ movementFactor first last coefficient firstFactor lastFactor :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4)
          (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative))
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
          (Norm.Basic.normSq_nonneg coefficient))) (Norm.Basic.normSq_nonneg _)
  have commonNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative)
  have numeratorBound := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl (2 * (firstFactor + lastFactor)))
      (Arithmetic.pow_le_pow_direct movementNonnegative movementBound 2))
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have numeratorNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct commonNonnegative
      (Arithmetic.sq_nonneg_direct
        (movementFactor first last coefficient firstFactor lastFactor)))
  exact Arithmetic.mul_le_mul_direct numeratorBound
    (Norm.Reciprocal.normSq_le sourcePositive sourceLower)
    (Norm.Basic.normSq_nonneg _) (numeratorNonnegative.trans numeratorBound)

section OriginalCertificate

variable (first last radicand increment coefficient : Canonical) (firstFactor lastFactor : Fraction.Rational)
  (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
  (firstNonzero : first ≠ 0) (lastNonzero : last ≠ 0) (sumNonzero : first + last ≠ 0)
  (unit : Norm.Basic.normSq increment ≤ 1)
  (firstResidual : Norm.Basic.normSq (first * first - radicand) ≤ firstFactor * Norm.Basic.normSq increment ^ 2)
  (lastResidual : Norm.Basic.normSq (last * last - (radicand - increment * coefficient)) ≤
    lastFactor * Norm.Basic.normSq increment ^ 2)

/-- The retained inverse-root factor is exactly the original root/reciprocal composition's scalar factor. -/
theorem inverseCertificate_factor :
    (inverseCertificate first last radicand increment coefficient firstFactor lastFactor
      firstNonnegative lastNonnegative
      firstNonzero lastNonzero sumNonzero unit firstResidual lastResidual).factor =
    2 * (Norm.Basic.normSq first⁻¹ ^ 2 * remainderFactor first last coefficient firstFactor lastFactor +
      Norm.Basic.normSq first⁻¹ ^ 2 * Norm.Basic.normSq last⁻¹ *
        (2 * (Norm.Basic.normSq (half * coefficient * first⁻¹) +
          remainderFactor first last coefficient firstFactor lastFactor)) ^ 2) := by
  change 2 * (Canonical.normSq (-(first⁻¹ * first⁻¹)) *
      remainderFactor first last coefficient firstFactor lastFactor +
    Norm.Basic.normSq (first⁻¹ * first⁻¹ * last⁻¹) *
      (2 * (Canonical.normSq (-(half * coefficient * first⁻¹)) +
        remainderFactor first last coefficient firstFactor lastFactor)) ^ 2) = _
  rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_neg, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul,
    Norm.Basic.normSq_mul]
  ring1

/-- The original inverse-root factor is bounded by both actual root margins and their signed-sum margin. -/
theorem inverseCertificate_factor_le {coefficientCeiling sourceFloor targetFloor sumFloor : Fraction.Rational}
    (coefficientBound : Norm.Basic.normSq coefficient ≤ coefficientCeiling)
    (sourcePositive : 0 < sourceFloor) (sourceLower : sourceFloor ≤ Norm.Basic.normSq first)
    (targetPositive : 0 < targetFloor) (targetLower : targetFloor ≤ Norm.Basic.normSq last)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last)) :
    (inverseCertificate first last radicand increment coefficient firstFactor lastFactor
      firstNonnegative lastNonnegative
      firstNonzero lastNonzero sumNonzero unit firstResidual lastResidual).factor ≤
    inverseCeiling coefficientCeiling sourceFloor targetFloor sumFloor firstFactor lastFactor := by
  let root := certificate first last radicand increment coefficient firstFactor lastFactor
    firstNonnegative lastNonnegative
    firstNonzero sumNonzero unit firstResidual lastResidual
  let remainder := remainderFactor first last coefficient firstFactor lastFactor
  have remainderNonnegative : 0 ≤ remainder := root.factor_nonneg
  have sourceInverse := Norm.Reciprocal.normSq_le sourcePositive sourceLower
  have targetInverse := Norm.Reciprocal.normSq_le targetPositive targetLower
  have sourceSquare := Arithmetic.pow_le_pow_direct
    (Norm.Basic.normSq_nonneg first⁻¹) sourceInverse 2
  have remainderBound := remainderFactor_le_ceiling firstNonnegative lastNonnegative coefficientBound
    sourcePositive sourceLower sumPositive sumLower
  have numerator := Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientBound
    (Norm.Basic.normSq_nonneg half)
  have slopeBound : Norm.Basic.normSq (half * coefficient * first⁻¹) ≤
      rootSlopeCeiling coefficientCeiling sourceFloor := by
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct numerator sourceInverse (Norm.Basic.normSq_nonneg _)
      ((Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg half)
        (Norm.Basic.normSq_nonneg coefficient)).trans numerator)
  have sensitivityBound := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct slopeBound remainderBound)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have sensitivityNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.add_le_add_direct
      (Norm.Basic.normSq_nonneg (half * coefficient * first⁻¹)) remainderNonnegative)
  have sensitivitySquare := Arithmetic.pow_le_pow_direct sensitivityNonnegative sensitivityBound 2
  have firstTerm := Arithmetic.mul_le_mul_direct sourceSquare remainderBound remainderNonnegative
    (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct sourcePositive).le 2)
  have reciprocalFactor := Arithmetic.mul_le_mul_direct sourceSquare targetInverse
    (Norm.Basic.normSq_nonneg _)
    (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct sourcePositive).le 2)
  have reciprocalNonnegative := Arithmetic.mul_nonneg_direct
    (Arithmetic.pow_nonneg_direct (Norm.Basic.normSq_nonneg first⁻¹) 2)
    (Norm.Basic.normSq_nonneg last⁻¹)
  have lastTerm := Arithmetic.mul_le_mul_direct reciprocalFactor sensitivitySquare
    (Arithmetic.pow_nonneg_direct sensitivityNonnegative 2)
    (reciprocalNonnegative.trans reciprocalFactor)
  rewrite [inverseCertificate_factor]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstTerm lastTerm)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)

end OriginalCertificate

end Purelib.Calculus.Jet.Quadratic.SquareRoot
