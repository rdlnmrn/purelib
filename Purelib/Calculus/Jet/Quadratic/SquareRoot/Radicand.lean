module

public import Purelib.Calculus.Jet.Quadratic.SquareRoot
public import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Uniform square-root Taylor bounds for a retained nonlinear radicand

The original radicand certificate supplies its actual base, output, slope
and quadratic remainder. Two displayed sheet readings retain their separate
square residual payments at the original increment's fourth-order scale.
Positive denominator and signed-sum floors yield root movement and a
quadratic root remainder with factors independent of the increment's size.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand

open Purelib.Calculus.Jet.Quadratic.Basic
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The actual discrepancy from the nonlinear radicand's retained first-order square expansion. -/
@[expose] def error {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) : Canonical :=
  last * last - first * first - increment * radicand.slope

/-- The explicit error factor pays both square residuals and the original radicand remainder. -/
@[expose] def errorFactor {increment : Canonical} (radicand : Certificate increment)
    (firstFactor lastFactor : Fraction.Rational) : Fraction.Rational :=
  2 * (radicand.factor + 2 * (firstFactor + lastFactor))

/-- Both original residual payments and the radicand certificate bound the actual square-expansion error. -/
theorem error_le {increment first last : Canonical} (radicand : Certificate increment)
    {firstFactor lastFactor : Fraction.Rational}
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (error radicand first last) ≤
      errorFactor radicand firstFactor lastFactor * Norm.Basic.normSq increment ^ 2 := by
  have identity : error radicand first last = radicand.remainder +
      ((last * last - radicand.output) - (first * first - radicand.base)) := by
    rewrite [← radicand.expansion]
    unfold error
    ring1
  have residualDifference :
      Norm.Basic.normSq ((last * last - radicand.output) - (first * first - radicand.base)) ≤
        2 * (firstFactor + lastFactor) * Norm.Basic.normSq increment ^ 2 :=
    (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct lastResidual firstResidual)
        (by decide +kernel)).trans_eq (by ring1))
  rewrite [identity]
  have original : Norm.Basic.normSq radicand.remainder ≤
      radicand.factor * Norm.Basic.normSq increment ^ 2 := by
    simpa only [Norm.Basic.normSq_eq_canonical] using radicand.remainder_le
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct original residualDifference)
      (by decide +kernel)).trans_eq (by unfold errorFactor; ring1))

/-- The stable movement factor uses the original radicand slope ceiling and the signed-sum floor. -/
@[expose] def movementFactor {increment : Canonical} (radicand : Certificate increment)
    (firstFactor lastFactor slopeUpper sumFloor : Fraction.Rational) : Fraction.Rational :=
  2 * (slopeUpper + errorFactor radicand firstFactor lastFactor) * sumFloor⁻¹

/-- The stable root remainder factor uses the original denominator floor and both residual payments. -/
@[expose] def remainderFactor {increment : Canonical} (radicand : Certificate increment)
    (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational) : Fraction.Rational :=
  2 * (errorFactor radicand firstFactor lastFactor +
    movementFactor radicand firstFactor lastFactor slopeUpper sumFloor ^ 2) * floor⁻¹

/-- A positive quadrance floor gives nonzeroness of its actual retained reading. -/
private theorem nonzero_of_floor {value : Canonical} {floor : Fraction.Rational}
    (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq value) : value ≠ 0 := by
  intro zero
  rewrite [zero, Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt positive) lower

/-- The retained half has norm at most one and twice its value is exactly one. -/
private theorem half_bounds : Norm.Basic.normSq SquareRoot.half ≤ 1 ∧ SquareRoot.half * 2 = 1 := by
  constructor <;> decide +kernel

/-- The computed error factor is nonnegative for two original nonnegative residual factors. -/
theorem errorFactor_nonnegative {increment : Canonical} (radicand : Certificate increment)
    {firstFactor lastFactor : Fraction.Rational}
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) :
    0 ≤ errorFactor radicand firstFactor lastFactor :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.add_le_add_direct radicand.factor_nonneg
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct firstNonnegative lastNonnegative)))

/-- Original square factorization derives root movement from the nonlinear radicand's finite evidence. -/
theorem movement_le {increment first last : Canonical} (radicand : Certificate increment)
    {firstFactor lastFactor slopeUpper sumFloor : Fraction.Rational}
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (last - first) ≤
      movementFactor radicand firstFactor lastFactor slopeUpper sumFloor * Norm.Basic.normSq increment := by
  have sumNonzero := nonzero_of_floor sumPositive sumLower
  have inverseCancel : (first + last)⁻¹ * (first + last) = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul (first + last) sumNonzero
  have identity : last - first =
      (increment * radicand.slope + error radicand first last) * (first + last)⁻¹ := by
    apply Gaussian.Field.mul_right_cancel_of_ne sumNonzero
    calc
      _ = increment * radicand.slope + error radicand first last := by unfold error; ring1
      _ = _ := by rewrite [Gaussian.Basic.mul_assoc, inverseCancel, Gaussian.Basic.mul_one]; rfl
  have incrementSquare : Norm.Basic.normSq increment ^ 2 ≤ Norm.Basic.normSq increment := by
    rewrite [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct unit
      (Norm.Basic.normSq_nonneg increment)).trans_eq (Fraction.Field.mul_one_direct _)
  have errorBound := (error_le radicand firstResidual lastResidual).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct incrementSquare
      (errorFactor_nonnegative radicand firstNonnegative lastNonnegative))
  have coefficientBound : Norm.Basic.normSq (increment * radicand.slope + error radicand first last) ≤
      2 * (slopeUpper + errorFactor radicand firstFactor lastFactor) * Norm.Basic.normSq increment := by
    have slopeMovement : Norm.Basic.normSq (increment * radicand.slope) ≤
        Norm.Basic.normSq increment * slopeUpper := by
      rewrite [Norm.Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct slopeBound (Norm.Basic.normSq_nonneg _)
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct slopeMovement errorBound)
        (by decide +kernel)).trans_eq (by ring1))
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (Arithmetic.mul_le_mul_direct coefficientBound
    (Norm.Reciprocal.normSq_le sumPositive sumLower) (Norm.Basic.normSq_nonneg _)
    ((Norm.Basic.normSq_nonneg _).trans coefficientBound)).trans_eq
      (by unfold movementFactor; ring1)

/-- The actual root remainder is computed from the nonlinear square discrepancy and root displacement. -/
@[expose] def remainder {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) : Canonical :=
  SquareRoot.half * (error radicand first last - (last - first) ^ 2) * first⁻¹

/-- The original positive denominator floor gives the exact nonlinear root expansion. -/
theorem expansion {increment first last : Canonical} (radicand : Certificate increment)
    {floor : Fraction.Rational} (positive : 0 < floor) (lower : floor ≤ Norm.Basic.normSq first) :
    last - first - increment * (SquareRoot.half * radicand.slope * first⁻¹) = remainder radicand first last := by
  have firstNonzero := nonzero_of_floor positive lower
  have inverseCancel : first⁻¹ * first = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul first firstNonzero
  apply Gaussian.Field.mul_right_cancel_of_ne firstNonzero
  calc
    _ = (last - first) * first - SquareRoot.half * increment * radicand.slope * (first⁻¹ * first) := by ring1
    _ = (last - first) * first - SquareRoot.half * increment * radicand.slope := by
      rewrite [inverseCancel, Gaussian.Basic.mul_one]; rfl
    _ = SquareRoot.half * (2 * (last - first) * first - increment * radicand.slope) := by
      calc
        _ = (SquareRoot.half * 2) * ((last - first) * first) -
            SquareRoot.half * increment * radicand.slope := by
          rewrite [half_bounds.2, Gaussian.Basic.one_mul]; rfl
        _ = _ := by ring1
    _ = SquareRoot.half * (error radicand first last - (last - first) ^ 2) := by unfold error; ring1
    _ = _ := by unfold remainder; rewrite [Gaussian.Basic.mul_assoc, inverseCancel, Gaussian.Basic.mul_one]; rfl

/-- The computed root remainder factor is nonnegative under the original residual and denominator payments. -/
theorem remainderFactor_nonnegative {increment : Canonical} (radicand : Certificate increment)
    {firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational}
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor) (positive : 0 < floor) :
    0 ≤ remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor := by
  unfold remainderFactor
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (errorFactor_nonnegative radicand firstNonnegative lastNonnegative)
        (Arithmetic.sq_nonneg_direct _)))
    (Fraction.Order.Field.inv_pos_direct positive).le

/-- The original residuals, nonlinear radicand certificate and finite margins bound the computed root remainder. -/
theorem remainder_le {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (floorPositive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    Canonical.normSq (remainder radicand first last) ≤
      remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor * Canonical.normSq increment ^ 2 := by
  let movement := movementFactor radicand firstFactor lastFactor slopeUpper sumFloor
  let discrepancy := error radicand first last
  let remainder := SquareRoot.half * (discrepancy - (last - first) ^ 2) * first⁻¹
  have movementBound : Norm.Basic.normSq (last - first) ≤ movement * Norm.Basic.normSq increment :=
    movement_le radicand sumPositive sumLower slopeBound firstNonnegative lastNonnegative unit
      firstResidual lastResidual
  have movementSquare : Norm.Basic.normSq ((last - first) ^ 2) ≤
      movement ^ 2 * Norm.Basic.normSq increment ^ 2 := by
    rewrite [Norm.Power.normSq_pow]
    exact (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) movementBound 2).trans_eq
      (by ring1)
  have discrepancyBound := error_le radicand firstResidual lastResidual
  have differenceBound : Norm.Basic.normSq (discrepancy - (last - first) ^ 2) ≤
      2 * (errorFactor radicand firstFactor lastFactor + movement ^ 2) * Norm.Basic.normSq increment ^ 2 :=
    (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct discrepancyBound movementSquare)
        (by decide +kernel)).trans_eq (by ring1))
  have differenceNonnegative := (Norm.Basic.normSq_nonneg _).trans differenceBound
  simp only [← Norm.Basic.normSq_eq_canonical]
  change Norm.Basic.normSq remainder ≤ _
  dsimp only [remainder]
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
  have halfDifference := Arithmetic.mul_le_mul_direct half_bounds.1 differenceBound
    (Norm.Basic.normSq_nonneg _) (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
  rewrite [Fraction.Field.one_mul] at halfDifference
  exact (Arithmetic.mul_le_mul_direct halfDifference
    (Norm.Reciprocal.normSq_le floorPositive firstLower) (Norm.Basic.normSq_nonneg _)
    differenceNonnegative).trans_eq (by unfold remainderFactor; dsimp only [movement]; ring1)

/-- Construct the actual nonlinear root certificate from opaque owned expansion and quantitative proofs. -/
@[expose] def certificate {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (floorPositive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) : Certificate increment :=
  { base := first
    output := last
    slope := SquareRoot.half * radicand.slope * first⁻¹
    remainder := remainder radicand first last
    expansion := expansion radicand floorPositive firstLower
    factor := remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor
    factor_nonneg := remainderFactor_nonnegative radicand firstNonnegative lastNonnegative floorPositive
    remainder_le := remainder_le radicand first last firstFactor lastFactor slopeUpper floor sumFloor
      firstNonnegative lastNonnegative floorPositive firstLower sumPositive sumLower slopeBound unit
      firstResidual lastResidual }

/-- The actual reciprocal displacement has its original expansion under the two denominator floors. -/
theorem reciprocal_expansion (first last : Canonical) (floor : Fraction.Rational)
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) :
    last⁻¹ - first⁻¹ - (last - first) * (-(first⁻¹ * first⁻¹)) =
      (last - first) ^ 2 * (first⁻¹ * first⁻¹ * last⁻¹) :=
  (SquareRoot.reciprocalCertificate first last
    (nonzero_of_floor positive firstLower) (nonzero_of_floor positive lastLower)).expansion

/-- The cubic inverse-floor budget is nonnegative under the original positive floor. -/
theorem reciprocalFactor_nonnegative {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ floor⁻¹ ^ 3 :=
  Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le 3

/-- Both original denominator floors bound the retained reciprocal remainder by a fixed cubic inverse-floor factor. -/
theorem reciprocal_remainder_le (first last : Canonical) (floor : Fraction.Rational)
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) :
    Canonical.normSq ((last - first) ^ 2 * (first⁻¹ * first⁻¹ * last⁻¹)) ≤
      floor⁻¹ ^ 3 * Canonical.normSq (last - first) ^ 2 := by
  let original := SquareRoot.reciprocalCertificate first last
    (by exact nonzero_of_floor positive firstLower) (by exact nonzero_of_floor positive lastLower)
  have coefficient : Norm.Basic.normSq (first⁻¹ * first⁻¹ * last⁻¹) ≤ floor⁻¹ ^ 3 := by
    have bounded := Norm.Reciprocal.coefficient_two_powers_normSq_le
      (coefficient := (1 : Canonical)) (first := first) (last := last) (budget := 1)
      (by
        rewrite [Norm.Basic.normSq_one]
        exact Fraction.Order.Basic.le_refl _)
      positive positive firstLower lastLower 2 1
    rewrite [Gaussian.Basic.one_mul, pow_two, pow_one, Fraction.Field.one_mul] at bounded
    exact bounded.trans_eq (by ring1)
  exact original.remainder_le.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
      (Arithmetic.pow_nonneg_direct (Canonical.normSq_nonneg _) 2))

/-- Construct the actual reciprocal certificate from its opaque original expansion and floor-payment proofs. -/
@[expose] def reciprocalCertificate (first last : Canonical) (floor : Fraction.Rational)
    (positive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last) : Certificate (last - first) :=
  { base := first⁻¹
    output := last⁻¹
    slope := -(first⁻¹ * first⁻¹)
    remainder := (last - first) ^ 2 * (first⁻¹ * first⁻¹ * last⁻¹)
    expansion := reciprocal_expansion first last floor positive firstLower lastLower
    factor := floor⁻¹ ^ 3
    factor_nonneg := reciprocalFactor_nonnegative positive
    remainder_le := reciprocal_remainder_le first last floor positive firstLower lastLower }

/-- The stable inverse-root factor uses only original radicand and denominator budgets. -/
@[expose] def inverseFactor {increment : Canonical} (radicand : Certificate increment)
    (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational) : Fraction.Rational :=
  let rootFactor := remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor
  2 * (floor⁻¹ ^ 2 * rootFactor + floor⁻¹ ^ 3 * (2 * (slopeUpper * floor⁻¹ + rootFactor)) ^ 2)

/-- Compose the actual nonlinear root and reciprocal certificates while retaining both original readings. -/
@[expose] def inverseComposition {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (floorPositive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) : Certificate increment :=
  let root := certificate radicand first last firstFactor lastFactor slopeUpper floor sumFloor
    firstNonnegative lastNonnegative floorPositive firstLower sumPositive sumLower slopeBound unit
    firstResidual lastResidual
  let reciprocal := reciprocalCertificate first last floor floorPositive firstLower lastLower
  root.compose reciprocal (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)

/-- The original composed inverse certificate has its factor bounded by the fixed radicand and margin budgets. -/
theorem inverse_factor_le {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (floorPositive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) :
    (inverseComposition radicand first last firstFactor lastFactor slopeUpper floor sumFloor
      firstNonnegative lastNonnegative floorPositive firstLower lastLower sumPositive sumLower slopeBound unit
      firstResidual lastResidual).factor ≤
        inverseFactor radicand firstFactor lastFactor slopeUpper floor sumFloor := by
  let root := certificate radicand first last firstFactor lastFactor slopeUpper floor sumFloor
    firstNonnegative lastNonnegative floorPositive firstLower sumPositive sumLower slopeBound unit
    firstResidual lastResidual
  let reciprocal := reciprocalCertificate first last floor floorPositive firstLower lastLower
  let composed := root.compose reciprocal (by simpa only [Norm.Basic.normSq_eq_canonical] using unit)
  let rootFactor := remainderFactor radicand firstFactor lastFactor slopeUpper floor sumFloor
  let sensitivity := 2 * (slopeUpper * floor⁻¹ + rootFactor)
  have firstInverse := Norm.Reciprocal.normSq_le floorPositive firstLower
  have rootSlope : Norm.Basic.normSq root.slope ≤ slopeUpper * floor⁻¹ := by
    change Norm.Basic.normSq (SquareRoot.half * radicand.slope * first⁻¹) ≤ _
    rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    have halfSlope : Norm.Basic.normSq SquareRoot.half * Norm.Basic.normSq radicand.slope ≤ 1 * slopeUpper := by
      exact Arithmetic.mul_le_mul_direct half_bounds.1 slopeBound
        (Norm.Basic.normSq_nonneg _) (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    rewrite [Fraction.Field.one_mul] at halfSlope
    exact Arithmetic.mul_le_mul_direct halfSlope firstInverse (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg radicand.slope).trans slopeBound)
  have reciprocalSlope : Norm.Basic.normSq reciprocal.slope ≤ floor⁻¹ ^ 2 := by
    change Norm.Basic.normSq (-(first⁻¹ * first⁻¹)) ≤ _
    rewrite [Norm.Basic.normSq_neg, Norm.Basic.normSq_mul, pow_two]
    exact Arithmetic.mul_le_mul_direct firstInverse firstInverse (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans firstInverse)
  have rootSensitivity : root.sensitivity ≤ sensitivity := by
    change 2 * (Canonical.normSq root.slope + rootFactor) ≤ _
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct rootSlope (Fraction.Order.Basic.le_refl _)) (by decide +kernel)
  have firstTerm : Canonical.normSq reciprocal.slope * root.factor ≤ floor⁻¹ ^ 2 * rootFactor := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_right_direct reciprocalSlope root.factor_nonneg
  have secondTerm : reciprocal.factor * root.sensitivity ^ 2 ≤ floor⁻¹ ^ 3 * sensitivity ^ 2 :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.pow_le_pow_direct root.sensitivity_nonneg rootSensitivity 2)
      reciprocal.factor_nonneg
  have factorBound : composed.factor ≤ inverseFactor radicand firstFactor lastFactor slopeUpper floor sumFloor := by
    change 2 * (Canonical.normSq reciprocal.slope * root.factor + reciprocal.factor * root.sensitivity ^ 2) ≤ _
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide +kernel)
  exact factorBound

/-- Construct the original inverse-root expansion with its stable fixed-budget factor.

The retained nonlinear root and reciprocal composition supplies every scalar
field. Its owned quantitative proof enlarges only the remainder factor to
the computed bound, independently of the original increment's size.
-/
@[expose] def inverseCertificate {increment : Canonical} (radicand : Certificate increment)
    (first last : Canonical) (firstFactor lastFactor slopeUpper floor sumFloor : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstFactor) (lastNonnegative : 0 ≤ lastFactor)
    (floorPositive : 0 < floor) (firstLower : floor ≤ Norm.Basic.normSq first)
    (lastLower : floor ≤ Norm.Basic.normSq last)
    (sumPositive : 0 < sumFloor) (sumLower : sumFloor ≤ Norm.Basic.normSq (first + last))
    (slopeBound : Norm.Basic.normSq radicand.slope ≤ slopeUpper)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (firstResidual : Norm.Basic.normSq (first * first - radicand.base) ≤
      firstFactor * Norm.Basic.normSq increment ^ 2)
    (lastResidual : Norm.Basic.normSq (last * last - radicand.output) ≤
      lastFactor * Norm.Basic.normSq increment ^ 2) : Certificate increment :=
  let composed := inverseComposition radicand first last firstFactor lastFactor slopeUpper floor sumFloor
    firstNonnegative lastNonnegative floorPositive firstLower lastLower sumPositive sumLower slopeBound unit
    firstResidual lastResidual
  let factorBound := inverse_factor_le radicand first last firstFactor lastFactor slopeUpper floor sumFloor
    firstNonnegative lastNonnegative floorPositive firstLower lastLower sumPositive sumLower slopeBound unit
    firstResidual lastResidual
  { composed with
      factor := inverseFactor radicand firstFactor lastFactor slopeUpper floor sumFloor
      factor_nonneg := composed.factor_nonneg.trans factorBound
      remainder_le := composed.remainder_le.trans
        (Arithmetic.mul_le_mul_of_nonneg_right_direct factorBound
          (Arithmetic.pow_nonneg_direct (Canonical.normSq_nonneg _) 2)) }

end Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand
