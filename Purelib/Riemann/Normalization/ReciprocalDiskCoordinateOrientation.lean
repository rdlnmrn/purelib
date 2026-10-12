module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation
import Purelib.Tactic.Ring
public import Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# Signed root-coordinate geometry with a paid square residual

The dot product selects the local sheet. A separate finite square-error
budget transfers an actual inverse-arc area margin to the sampled root edge.
Neither condition is inferred from the primitive's values.
-/

namespace Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

section
open Purelib.Data
/-- The square of a sum is at most twice the sum of the two squares. -/
private theorem square_sum (first last : Coordinate) :
    (first + last) ^ 2 ≤ 2 * (first ^ 2 + last ^ 2) := by
  apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  exact (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct (first - last)).trans_eq (by ring1)

/-- An approximate root square has quadrance at most four under unit point and residual bounds. -/
private theorem square_norm_upper {root point : Gaussian} {tolerance : Coordinate}
    (pointUpper : normSq point ≤ 1) (small : tolerance ≤ 1)
    (accurate : normSq (root * root - point) < tolerance) : normSq (root * root) ≤ 4 := by
  have triangle := Gaussian.Norm.Bounds.normSq_add_le_two (root * root - point) point
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
  have estimate := triangle.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (accurate.le.trans small) pointUpper) (by decide))
  rw [show root * root - point + point = root * root by ring1] at estimate
  exact estimate.trans_eq (by decide)

/-- An approximate odd-chart root has quadrance at most two.

The source point has quadrance at most one, and the square residual is smaller than a tolerance at most one. -/
theorem coordinate_norm_upper {root point : Gaussian} {tolerance : Coordinate}
    (pointUpper : normSq point ≤ 1) (small : tolerance ≤ 1)
    (accurate : normSq (root * root - point) < tolerance) : normSq root ≤ 2 := by
  have estimate := square_norm_upper pointUpper small accurate
  rw [Gaussian.Basic.Canonical.normSq_mul] at estimate
  apply Rat.Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide : (0 : Coordinate) ≤ 2)
  exact (show normSq root ^ 2 = normSq root * normSq root by ring1).trans_le
    (estimate.trans_eq (by decide))

end

open Purelib.Integration
open Purelib.Data
/-- The squared-root edge area differs from the point edge area by squared error at most four times tolerance.

Both source points have quadrance at most one and both square residuals satisfy the same positive tolerance at most one.
-/
theorem squared_area_error {first last firstPoint lastPoint : Gaussian} {tolerance : Coordinate}
    (firstUnit : normSq firstPoint ≤ 1) (lastUnit : normSq lastPoint ≤ 1)
    (positive : 0 < tolerance) (small : tolerance ≤ 1)
    (firstSquare : normSq (first * first - firstPoint) < tolerance)
    (lastSquare : normSq (last * last - lastPoint) < tolerance) :
    (Energy.AffineTriangle.crossEnergy (last * last) (first * first) - Energy.AffineTriangle.crossEnergy lastPoint
      firstPoint) ^ 2 ≤ 4 * tolerance := by
  have firstUpper := square_norm_upper firstUnit small firstSquare
  have firstCross := Energy.AffineTriangle.crossEnergy_sq_le (last * last - lastPoint) (first * first)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at firstCross
  have firstError := firstCross.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct lastSquare.le firstUpper (Gaussian.Basic.Canonical.normSq_nonneg
        _) positive.le)
      (by decide : (0 : Coordinate) ≤ (4 : Coordinate)⁻¹))
  have lastCross := Energy.AffineTriangle.crossEnergy_sq_le lastPoint (first * first - firstPoint)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at lastCross
  have lastError := lastCross.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct lastUnit firstSquare.le (Gaussian.Basic.Canonical.normSq_nonneg
        _) (by decide : (0 : Coordinate) ≤ 1))
      (by decide : (0 : Coordinate) ≤ (4 : Coordinate)⁻¹))
  have difference : Energy.AffineTriangle.crossEnergy (last * last) (first * first) - Energy.AffineTriangle.crossEnergy
    lastPoint firstPoint =
      Energy.AffineTriangle.crossEnergy (last * last - lastPoint) (first * first) + Energy.AffineTriangle.crossEnergy
        lastPoint (first * first - firstPoint) := by
    simp only [Energy.AffineTriangle.crossEnergy, Gaussian.Basic.conj, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Basic.mul_im, Rat.Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [difference]
  have estimate := (square_sum _ _).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstError lastError) (by decide))
  have extra : 0 ≤ (6 * tolerance) * (4 : Coordinate)⁻¹ := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le) (by decide)
  exact (estimate.trans (le_add_of_nonneg_right extra)).trans_eq (by
    change 2 * ((tolerance * 4) * (4 : Coordinate)⁻¹ + (1 * tolerance) * 4⁻¹) + (6 * tolerance) * 4⁻¹ = 4 * tolerance
    rw [show 2 * ((tolerance * 4) * (4 : Coordinate)⁻¹ + (1 * tolerance) * 4⁻¹) +
      (6 * tolerance) * 4⁻¹ = (4 * 4⁻¹) * (4 * tolerance) by ring1]
    rw [show (4 : Coordinate) * 4⁻¹ = 1 by decide, Rat.Fraction.Field.one_mul])

/-- Squaring both endpoints multiplies their signed cross-energy by twice their coordinate dot product. -/
theorem squared_area (first last : Gaussian) :
    Energy.AffineTriangle.crossEnergy (last * last) (first * first) =
      Energy.AffineTriangle.crossEnergy last first * (2 * (first.re * last.re + first.im * last.im)) := by
  simp only [Energy.AffineTriangle.crossEnergy, Gaussian.Basic.conj, Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im, Rat.Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- A paid square-error budget and positive same-sheet dot product preserve the signed root-edge orientation.

The point edge has a positive area margin; sixteen times the common square tolerance is at most that margin squared.
Both point quadrances and the tolerance are at most one. -/
theorem coordinate_area_positive {first last firstPoint lastPoint : Gaussian} {tolerance margin : Coordinate}
    (firstUnit : normSq firstPoint ≤ 1) (lastUnit : normSq lastPoint ≤ 1)
    (positive : 0 < tolerance) (small : tolerance ≤ 1)
    (firstSquare : normSq (first * first - firstPoint) < tolerance)
    (lastSquare : normSq (last * last - lastPoint) < tolerance)
    (dot : 0 < first.re * last.re + first.im * last.im)
    (marginPositive : 0 < margin) (marginBound : margin ≤ Energy.AffineTriangle.crossEnergy lastPoint firstPoint)
    (paid : 16 * tolerance ≤ margin ^ 2) : 0 < Energy.AffineTriangle.crossEnergy last first := by
  let halfMargin := margin / 2
  have halfPositive : 0 < halfMargin := Rat.Fraction.Order.Field.div_pos_direct marginPositive (by decide)
  have halfTwice : halfMargin * 2 = margin := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have squarePaid : 4 * tolerance ≤ halfMargin ^ 2 := by
    have estimate := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (by
        decide : (0 : Coordinate) ≤ (4 : Coordinate)⁻¹)
    have firstEq : (16 * tolerance) * (4 : Coordinate)⁻¹ = 4 * tolerance := by
      rw [show (16 * tolerance) * (4 : Coordinate)⁻¹ = (4 * 4⁻¹) * (4 * tolerance) by ring1]
      rw [show (4 : Coordinate) * 4⁻¹ = 1 by decide, Rat.Fraction.Field.one_mul]
    have lastEq : margin ^ 2 * (4 : Coordinate)⁻¹ = halfMargin ^ 2 := by
      dsimp only [halfMargin]
      rw [Rat.Fraction.Field.div_eq_mul_inv_direct, show (4 : Coordinate)⁻¹ = (2⁻¹ : Coordinate) ^ 2 by decide]
      ring1
    exact firstEq.symm.trans_le (estimate.trans_eq lastEq)
  have error := Rat.Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct halfPositive.le
    ((squared_area_error firstUnit lastUnit positive small firstSquare lastSquare).trans squarePaid)
  have lower : halfMargin ≤ Energy.AffineTriangle.crossEnergy (last * last) (first * first) := by
    have estimate := add_le_add marginBound error
    exact (show halfMargin = margin + -halfMargin by rw [← halfTwice]; ring1).trans_le
      (estimate.trans_eq (by ring1))
  have areaPositive := halfPositive.trans_le lower
  rw [squared_area] at areaPositive
  have factorPositive := Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : Coordinate) < 2) dot
  have divided := Rat.Fraction.Order.Field.div_pos_direct areaPositive factorPositive
  apply divided.trans_eq
  apply Rat.Fraction.Field.mul_right_cancel_of_ne factorPositive.ne'
  exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ factorPositive.ne'

end Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
