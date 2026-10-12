module
import Purelib.Algebra.Polynomial.Dense.SmallCoefficients
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Path.Affine.SmallCoefficients
public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Periods.PeriodCurves
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitQuarticPreparedHorizontalCells (HorizontalGaussianPolynomial)

open Purelib.Data

open Purelib.Polynomial

open Purelib

section
@[expose] public section

/-!
# Uniform analytic data for later horizontal quartic cells

The last six outer cells of the canonical horizontal connector all have the
same quarter-unit direction, and their starting points have no larger squared
norm than the start of the second cell.  This module caches the symbolic
quartic substitution once and proves that its dense-Horner slope is monotone
in that starting-point norm.  Later cells can therefore reuse the exact
second-cell slope instead of normalizing another quartic coefficient list.
-/

namespace Purelib.Polynomial.Special.QuarticMinusOne.Affine.Horizontal

/-- Common affine direction of every outer horizontal quarter-cell. -/
def horizontalCellDirection :
  Gaussian.Basic.Canonical := Gaussian.Components.Basic.point (1 / 4) 0

/-- Symbolic quartic substitution along a horizontal quarter-cell. -/
def horizontalQuarticCache (origin :
  Gaussian.Basic.Canonical) : HorizontalGaussianPolynomial
  :=
  ⟨[horizontalCellDirection ^ 4,
    4 * origin * horizontalCellDirection ^ 3,
    6 * origin ^ 2 * horizontalCellDirection ^ 2,
    4 * origin ^ 3 * horizontalCellDirection,
    origin ^ 4 - 1]⟩

/-- The Horner stage representing the horizontal affine parameter to power 0.

The stage retains the original quarter-unit direction and the preceding exact dense coefficient program. -/
private def horizontalStage1 (origin :
  Gaussian.Basic.Canonical) :
    HorizontalGaussianPolynomial :=
  Dense.Gaussian.Substitution.Affine.mulLine origin horizontalCellDirection 0
    +
    DensePolynomial.constant 1

/-- The Horner stage representing the horizontal affine parameter to power 1.

The stage retains the original quarter-unit direction and the preceding exact dense coefficient program. -/
private def horizontalStage2 (origin :
  Gaussian.Basic.Canonical) :
    HorizontalGaussianPolynomial :=
  Dense.Gaussian.Substitution.Affine.mulLine origin horizontalCellDirection
      (horizontalStage1 origin) + DensePolynomial.constant 0

/-- The Horner stage representing the horizontal affine parameter to power 2.

The stage retains the original quarter-unit direction and the preceding exact dense coefficient program. -/
private def horizontalStage3 (origin :
  Gaussian.Basic.Canonical) :
    HorizontalGaussianPolynomial :=
  Dense.Gaussian.Substitution.Affine.mulLine origin horizontalCellDirection
      (horizontalStage2 origin) + DensePolynomial.constant 0

/-- The Horner stage representing the horizontal affine parameter to power 3.

The stage retains the original quarter-unit direction and the preceding exact dense coefficient program. -/
private def horizontalStage4 (origin :
  Gaussian.Basic.Canonical) :
    HorizontalGaussianPolynomial :=
  Dense.Gaussian.Substitution.Affine.mulLine origin horizontalCellDirection
      (horizontalStage3 origin) + DensePolynomial.constant 0

/-- Exact coefficients of the horizontal Horner stage of degree 0. -/
private theorem horizontalStage1_eq (origin :
  Gaussian.Basic.Canonical) :
    horizontalStage1 origin = ⟨[1]⟩ := by
  apply DensePolynomial.ext
  with_unfolding_all rfl

/-- Exact coefficients of the horizontal Horner stage of degree 1.

The cell origin is nonzero, preserving the displayed coefficient shape through normalization. -/
private theorem horizontalStage2_eq (origin :
  Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) :
    horizontalStage2 origin =
      ⟨[horizontalCellDirection, origin]⟩ := by
  unfold horizontalStage2
  rw [horizontalStage1_eq, DensePolynomial.add_constant_zero,
    Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_one_coeff origin
    horizontalCellDirection 1 originNonzero
    (by with_unfolding_all decide) (by decide) ⟨[1]⟩ rfl]
  rw [Gaussian.Basic.mul_one, Gaussian.Basic.mul_one]

/-- Exact coefficients of the horizontal Horner stage of degree 2.

The cell origin is nonzero, preserving the displayed coefficient shape through normalization. -/
private theorem horizontalStage3_eq (origin :
  Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) :
    horizontalStage3 origin =
      ⟨[horizontalCellDirection ^ 2,
      2 * origin * horizontalCellDirection, origin ^ 2]⟩ := by
  unfold horizontalStage3
  rw [horizontalStage2_eq origin originNonzero,
    DensePolynomial.add_constant_zero,
    Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_two_coeffs origin
    horizontalCellDirection
    horizontalCellDirection
    origin originNonzero (by with_unfolding_all decide)
      (by with_unfolding_all decide)
      ⟨[horizontalCellDirection, origin]⟩ rfl]
  apply congrArg₂ List.cons
  · ring1
  · apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · rfl

/-- Exact coefficients of the horizontal Horner stage of degree 3.

The cell origin is nonzero, preserving the displayed coefficient shape through normalization. -/
private theorem horizontalStage4_eq (origin :
  Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) :
    horizontalStage4 origin =
      ⟨[horizontalCellDirection ^ 3,
      3 * origin * horizontalCellDirection ^ 2,
      3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ := by
  unfold horizontalStage4
  rw [horizontalStage3_eq origin originNonzero,
    DensePolynomial.add_constant_zero,
    Dense.Gaussian.Substitution.Affine.normalize_mulLine]
  apply DensePolynomial.ext
  rw [Path.Affine.SmallCoefficients.mulLine_three_coeffs origin
    horizontalCellDirection
    (horizontalCellDirection ^ 2) (2 * origin *
      horizontalCellDirection)
      (origin ^ 2) originNonzero (by with_unfolding_all decide)
      (Gaussian.Power.pow_ne_zero_direct
        horizontalCellDirection (by with_unfolding_all decide) 2)
      ⟨[horizontalCellDirection ^ 2, 2 * origin *
        horizontalCellDirection,
        origin ^ 2]⟩ rfl]
  apply congrArg₂ List.cons
  · ring1
  · apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · apply congrArg₂ List.cons
        · ring1
        · rfl

/-- Exact symbolic coefficient cache for a nonzero horizontal cell start.

The retained quarter-unit direction and original four Horner stages produce
the displayed quartic coefficient list without changing its normalization. -/
theorem horizontalQuarticCache_eq (origin :
  Gaussian.Basic.Canonical)
    (originNonzero : origin ≠ 0) :
    Dense.Gaussian.Substitution.Affine.composeLine
        Riemann.Periods.PeriodCurves.quarticPolynomial origin
          horizontalCellDirection =
            horizontalQuarticCache origin := by
  unfold Dense.Gaussian.Substitution.Affine.composeLine Dense.Gaussian.Substitution.Affine.composeLineCoeffs
  rw [show Riemann.Periods.PeriodCurves.quarticPolynomial.coeffs =
    [(1 : Gaussian.Basic.Canonical), 0, 0, 0, -1] from by with_unfolding_all rfl]
  change Dense.Gaussian.Substitution.Affine.mulLine origin
    horizontalCellDirection
      (horizontalStage4 origin) + DensePolynomial.constant (-1) =
        _
  rw [horizontalStage4_eq origin originNonzero]
  have mulEq :
      Dense.Gaussian.Substitution.Affine.mulLine origin
        horizontalCellDirection
          ⟨[horizontalCellDirection ^ 3,
            3 * origin * horizontalCellDirection ^ 2,
            3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ =
        ⟨[horizontalCellDirection ^ 4,
          4 * origin * horizontalCellDirection ^ 3,
          6 * origin ^ 2 * horizontalCellDirection ^ 2,
          4 * origin ^ 3 * horizontalCellDirection, origin ^ 4]⟩ := by
    apply DensePolynomial.ext
    rw [Path.Affine.SmallCoefficients.mulLine_four_coeffs origin
      horizontalCellDirection
      (horizontalCellDirection ^ 3)
        (3 * origin * horizontalCellDirection ^ 2)
        (3 * origin ^ 2 * horizontalCellDirection) (origin ^ 3)
        originNonzero (by with_unfolding_all decide)
        (Gaussian.Power.pow_ne_zero_direct
          horizontalCellDirection (by with_unfolding_all decide) 3)
        ⟨[horizontalCellDirection ^ 3,
          3 * origin * horizontalCellDirection ^ 2,
          3 * origin ^ 2 * horizontalCellDirection, origin ^ 3]⟩ rfl]
    apply congrArg₂ List.cons
    · ring1
    · apply congrArg₂ List.cons
      · ring1
      · apply congrArg₂ List.cons
        · ring1
        · apply congrArg₂ List.cons
          · ring1
          · apply congrArg₂ List.cons
            · ring1
            · rfl
  rw [mulEq, Algebra.Polynomial.Dense.SmallCoefficients.quartic_add_constant _ _ _ _ _
    (Gaussian.Power.pow_ne_zero_direct
      horizontalCellDirection (by with_unfolding_all decide) 4)]
  unfold horizontalQuarticCache
  apply DensePolynomial.ext
  rfl

/-- The horizontal quarter-cell slope is monotone in its starting squared norm.

The original quartic coefficients contribute monotone nonnegative power
bounds. Their retained weighted sum and maximum with one preserve the order. -/
theorem horizontalQuarticLipschitz_mono
    (origin target : Gaussian.Basic.Canonical)
    (normLe : Data.Gaussian.Norm.Basic.normSq origin ≤
      Data.Gaussian.Norm.Basic.normSq target) :
    Dense.Gaussian.Bounds.Box.denseLipschitzBound
        (horizontalQuarticCache origin)
          Riemann.Branches.ClearSheetContinuation.parameterAmbient ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound
        (horizontalQuarticCache target)
          Riemann.Branches.ClearSheetContinuation.parameterAmbient := open Purelib.Data.Rat in by
  have normNonnegative :=
    Gaussian.Norm.Basic.normSq_nonneg origin
  have squareLe :
      Data.Gaussian.Norm.Basic.normSq origin ^ 2 ≤
        Data.Gaussian.Norm.Basic.normSq target ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct normNonnegative normLe 2
  have cubeLe :
      Data.Gaussian.Norm.Basic.normSq origin ^ 3 ≤
        Data.Gaussian.Norm.Basic.normSq target ^ 3 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct normNonnegative normLe 3
  have secondLe :
      Data.Gaussian.Norm.Basic.normSq
          (4 * origin * horizontalCellDirection ^ 3) ≤
        Data.Gaussian.Norm.Basic.normSq
          (4 * target * horizontalCellDirection ^ 3) := by
    simp only [Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct normLe
        (Gaussian.Norm.Basic.normSq_nonneg 4))
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (Gaussian.Norm.Basic.normSq_nonneg
          horizontalCellDirection) 3)
  have thirdLe :
      Data.Gaussian.Norm.Basic.normSq
          (6 * origin ^ 2 * horizontalCellDirection ^ 2) ≤
        Data.Gaussian.Norm.Basic.normSq
          (6 * target ^ 2 * horizontalCellDirection ^ 2) := by
    simp only [Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (Gaussian.Norm.Basic.normSq_nonneg 6))
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (Gaussian.Norm.Basic.normSq_nonneg
          horizontalCellDirection) 2)
  have fourthLe :
      Data.Gaussian.Norm.Basic.normSq
          (4 * origin ^ 3 * horizontalCellDirection) ≤
        Data.Gaussian.Norm.Basic.normSq
          (4 * target ^ 3 * horizontalCellDirection) := by
    simp only [Gaussian.Norm.Basic.normSq_mul,
      Gaussian.Power.normSq_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct cubeLe
        (Gaussian.Norm.Basic.normSq_nonneg 4))
      (Gaussian.Norm.Basic.normSq_nonneg
        horizontalCellDirection)
  unfold horizontalQuarticCache
  rw [Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs,
    Purelib.Riemann.Branches.ClearSheetContinuation.parameterAmbient_denseLipschitzBound_fiveCoeffs]
  apply Fraction.Order.Basic.max_le
  · exact Fraction.Order.Basic.le_max_left _ _
  · apply Data.Rat.Fraction.Order.Basic.le_trans _ _ _ ?_ (Fraction.Order.Basic.le_max_right _ _)
    exact Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondLe
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 192) (by omega)).le))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct thirdLe
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 32) (by omega)).le))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct fourthLe
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 4) (by omega)).le)
end Purelib.Polynomial.Special.QuarticMinusOne.Affine.Horizontal

end
