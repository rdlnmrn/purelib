module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Dyadic.Grid
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Ring.Commute
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Dyadic

section
@[expose] public section

/-!
# Generated sample certificates for the quartic B-backward connector

This module connects the 128 generated rational root and quotient samples to
the canonical centred edges already cached by the explicit B-backward bank.
The prepared-cell accessors keep these proofs from reconstructing the
dependent owner thread.
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- The backward vertical displacement by one sixty-fourth has squared norm one over 4096. -/
theorem bBackwardVerticalDisplacement_normSq :
    Norm.Basic.normSq (Components.Basic.point 0 (-1 / 64)) =
      (1 / 4096 : Fraction.Rational) := by
  change (0 : Fraction.Rational) ^ 2 + (-1 / 64) ^ 2 = 1 / 4096
  rw [zero_pow (by omega), zero_add, pow_two,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne'
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne')
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 4096) (by omega)).ne'
  ring1

/-- The backward horizontal displacement by one sixty-fourth has squared norm one over 4096. -/
theorem bBackwardHorizontalDisplacement_normSq :
    Norm.Basic.normSq (Components.Basic.point (-1 / 64) 0) =
      (1 / 4096 : Fraction.Rational) := by
  change (-1 / 64 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 4096
  rw [zero_pow (by omega), add_zero, pow_two,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne'
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne')
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 4096) (by omega)).ne'
  ring1
end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-! # Generated sample certificates for the quartic B-forward connector -/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- The forward horizontal displacement by one sixty-fourth has squared norm one over 4096. -/
theorem bForwardHorizontalDisplacement_normSq :
    Norm.Basic.normSq (Components.Basic.point (1 / 64) 0) =
      (1 / 4096 : Fraction.Rational) := by
  change (1 / 64 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 4096
  rw [zero_pow (by omega), add_zero, pow_two,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne'
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne')
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 4096) (by omega)).ne'
  ring1

/-- The forward vertical displacement by one sixty-fourth has squared norm one over 4096. -/
theorem bForwardVerticalDisplacement_normSq :
    Norm.Basic.normSq (Components.Basic.point 0 (1 / 64)) =
      (1 / 4096 : Fraction.Rational) := by
  change (0 : Fraction.Rational) ^ 2 + (1 / 64) ^ 2 = 1 / 4096
  rw [zero_pow (by omega), zero_add, pow_two,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne'
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 64) (by omega)).ne')
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 4096) (by omega)).ne'
  ring1
end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-!
# Generated sample certificates for the horizontal quartic connector

This module connects the untrusted generated rational root data to the exact
prepared edges cached by the A-forward construction.  The common helpers keep
the proof cost linear in the 64 nonstationary horizontal edges.
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- Adjacent negative horizontal grid points at spacing one thirty-second have squared distance one over 1024. -/
theorem negativeHorizontalStep_normSq (n m : Fraction.Rational)
    (adjacent : n = m + 1) :
    Norm.Basic.normSq
        (Components.Basic.point (-(m / 32)) (-1 / 2) - Components.Basic.point (-(n / 32)) (-1 / 2)) =
      (1 / 1024 : Fraction.Rational) := by
  have difference :
      Components.Basic.point (-(m / 32)) (-1 / 2) - Components.Basic.point (-(n / 32)) (-1 / 2) =
        Components.Basic.point (1 / 32) 0 := by
    apply Basic.ext
    · simp only [Basic.sub_re, Components.Basic.point]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      rw [adjacent]
      ring1
    · simp only [Basic.sub_im, Components.Basic.point]
      ring1
  rw [difference]
  change (1 / 32 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 1024
  rw [pow_two, Fraction.Field.div_mul_div_direct]
  rw [show (1 : Fraction.Rational) * 1 = 1 by ring1,
    show (32 : Fraction.Rational) * 32 = 1024 by ring1]
  ring1

/-- Adjacent positive horizontal grid points at spacing one thirty-second have squared distance one over 1024. -/
theorem positiveHorizontalStep_normSq (n m : Fraction.Rational)
    (adjacent : n = m + 1) :
    Norm.Basic.normSq
        (Components.Basic.point (n / 32) (-1 / 2) - Components.Basic.point (m / 32) (-1 / 2)) =
      (1 / 1024 : Fraction.Rational) := by
  have difference :
      Components.Basic.point (n / 32) (-1 / 2) - Components.Basic.point (m / 32) (-1 / 2) =
        Components.Basic.point (1 / 32) 0 := by
    apply Basic.ext
    · simp only [Basic.sub_re, Components.Basic.point]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      rw [adjacent]
      ring1
    · simp only [Basic.sub_im, Components.Basic.point]
      ring1
  rw [difference]
  change (1 / 32 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 1024
  rw [pow_two, Fraction.Field.div_mul_div_direct]
  rw [show (1 : Fraction.Rational) * 1 = 1 by ring1,
    show (32 : Fraction.Rational) * 32 = 1024 by ring1]
  ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A connector index at most forty gives squared norm at most 29 over 16.

The original dyadic horizontal coordinate lies between zero and five quarters
in magnitude, while its fixed imaginary coordinate contributes one quarter. -/
public theorem firstConnectorPoint_normSq_le (n : Nat) (bound : n ≤ 40)
  :
    Norm.Basic.normSq
      (Components.Basic.point (-((n : Fraction.Rational) / 32)) (-1 / 2)) ≤ (29 / 16 : Fraction.Rational) := by
  have nNonnegative : (0 : Fraction.Rational) ≤ n := Fraction.Order.NatCast.qNatNonnegative n
  have ratioNonnegative : (0 : Fraction.Rational) ≤ (n : Fraction.Rational) / 32 :=
    Fraction.Order.Field.div_nonneg_direct nNonnegative
      (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega)).le
  have nLeForty : (n : Fraction.Rational) ≤ 40 :=
    Fraction.Cast.Order.natCast_le_direct bound
  have ratioLe : ((n : Fraction.Rational) / 32) ≤ 5 / 4 := by
    apply Fraction.Compatibility.divLeDivOfCrossMul
      (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega)) (Fraction.Order.NatCast.natCast_pos_direct 4 (by omega))
    calc
      (n : Fraction.Rational) * 4 ≤ 40 * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          nLeForty (by decide)
      _ = 5 * 32 := by ring1
  have negHalf : (-1 / 2 : Fraction.Rational) = -(1 / 2) := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  change (-((n : Fraction.Rational) / 32)) ^ 2 + (-1 / 2) ^ 2 ≤ 29 / 16
  rw [show (-((n : Fraction.Rational) / 32)) ^ 2 = ((n : Fraction.Rational) / 32) ^ 2 by ring1,
    negHalf, show (-(1 / 2 : Fraction.Rational)) ^ 2 = (1 / 2 : Fraction.Rational) ^ 2 by ring1]
  calc
    ((n : Fraction.Rational) / 32) ^ 2 + (1 / 2 : Fraction.Rational) ^ 2 ≤
        (5 / 4 : Fraction.Rational) ^ 2 + (1 / 2 : Fraction.Rational) ^ 2 :=
      add_le_add
        (Fraction.Order.Arithmetic.pow_le_pow_direct
          ratioNonnegative ratioLe 2) le_rfl
    _ = 29 / 16 := by with_unfolding_all decide

/-- Adjacent connector grid indices give squared distance one over 1024. -/
public theorem adjacentConnectorPoint_normSq (n m : Fraction.Rational)
    (adjacent : n = m + 1) :
    Norm.Basic.normSq
      (Components.Basic.point (-(n / 32)) (-1 / 2) - Components.Basic.point (-(m / 32)) (-1 / 2)) =
      (1 / 1024 : Fraction.Rational) := by
  have difference :
      Components.Basic.point (-(n / 32)) (-1 / 2) - Components.Basic.point (-(m / 32)) (-1 / 2) =
        Components.Basic.point (-1 / 32) 0 := by
    apply Basic.ext
    · simp only [Basic.sub_re, Components.Basic.point]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      rw [adjacent]
      ring1
    · simp only [Basic.sub_im, Components.Basic.point]
      ring1
  rw [difference]
  change (-1 / 32 : Fraction.Rational) ^ 2 + 0 ^ 2 = 1 / 1024
  rw [pow_two, Fraction.Field.div_mul_div_direct]
  rw [show (-1 : Fraction.Rational) * (-1) = 1 by ring1,
    show (32 : Fraction.Rational) * 32 = 1024 by ring1]
  ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-!
# Analytic and grid data for the eighth prepared quartic connector cell
-/

section

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 17179869184 gives scaled squared distance at most one sixty-fourth. -/
theorem eighthScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 17179869184) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit)
          (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit)
          (targetImaginary * Grid.GridFineUnit)) ≤ (1 / 64 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit -
        targetReal * Grid.GridFineUnit) ^ 2 +
      (sourceImaginary * Grid.GridFineUnit -
        targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) *
          Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 17179869184 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 64 : Fraction.Rational) := by
      rw [Grid.oneSixtyFourthQuarticGridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCell

/-- A coordinate-square sum at most 4398046511104 gives scaled grid squared norm at most four. -/
private theorem quarticGridPointNormLeFour
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 4398046511104) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (4 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 4
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 4398046511104 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (4 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        4398046511104 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          4 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 4 := by rw [cancel]; ring1
end Purelib.Examples.Riemann.ExplicitQuarticPreparedEighthCell

end

end

section
@[expose] public section

/-!
# Analytic and grid data for the fifth prepared quartic connector cell
-/

section

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 536870912 gives scaled squared distance at most one over 2048. -/
theorem fifthScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 536870912) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit)
          (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit)
          (targetImaginary * Grid.GridFineUnit)) ≤ (1 / 2048 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit -
        targetReal * Grid.GridFineUnit) ^ 2 +
      (sourceImaginary * Grid.GridFineUnit -
        targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) *
          Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 536870912 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 2048 : Fraction.Rational) := by
      have gridFine := Grid.scaledQuarticGrid
        1 512 2048 (by omega) (by ring1)
      simp only [Nat.cast_ofNat] at gridFine
      rw [gridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell

/-- A coordinate-square sum at most 4398046511104 gives scaled grid squared norm at most four. -/
private theorem quarticGridPointNormLeFour
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 4398046511104) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (4 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 4
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 4398046511104 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (4 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        4398046511104 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          4 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 4 := by rw [cancel]; ring1
end Purelib.Examples.Riemann.ExplicitQuarticPreparedFifthCell

end

end

section
@[expose] public section

/-!
# Analytic and grid data for the fourth prepared quartic connector cell
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 2147483648 gives scaled squared distance at most one over 512. -/
theorem fourthScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 2147483648) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit)
          (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit)
          (targetImaginary * Grid.GridFineUnit)) ≤ (1 / 512 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit -
        targetReal * Grid.GridFineUnit) ^ 2 +
      (sourceImaginary * Grid.GridFineUnit -
        targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) *
          Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 2147483648 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 512 : Fraction.Rational) := by
      have gridFine := Grid.scaledQuarticGrid
        1 2048 512 (by omega) (by ring1)
      simp only [Nat.cast_ofNat] at gridFine
      rw [gridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

/-- A coordinate-square sum at most 4398046511104 gives scaled grid squared norm at most four. -/
theorem quarticGridPointNormLeFour
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 4398046511104) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (4 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 4
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 4398046511104 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (4 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        4398046511104 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          4 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 4 := by rw [cancel]; ring1
end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-!
# The dyadic grid of the second prepared quartic connector cell

This module caches the nine Purelib.Data.Gaussian-rational radicands of the second outer
connector cell on its depth-three dyadic mesh.  A common fine unit keeps the
endpoint evaluations and all eight squared displacements constructive and
small enough to elaborate at the ordinary limits.
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 34359738368 gives scaled squared distance at most one thirty-second. -/
public theorem scaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 34359738368) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.fineUnit) (sourceImaginary * Grid.fineUnit) -
        Components.Basic.point (targetReal * Grid.fineUnit) (targetImaginary * Grid.fineUnit)) ≤
      (1 / 32 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.fineUnit - targetReal * Grid.fineUnit) ^ 2 +
        (sourceImaginary * Grid.fineUnit - targetImaginary * Grid.fineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) * Grid.fineUnit ^ 2 := by ring1
    _ ≤ 34359738368 * Grid.fineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.fineUnit)
    _ = (1 / 32 : Fraction.Rational) := by
      change 34359738368 * Grid.GridFineUnit ^ 2 =
        (1 / 32 : Fraction.Rational)
      have gridFine := Grid.scaledQuarticGrid
        1 32768 32 (by omega) (by ring1)
      simp only [Nat.cast_ofNat] at gridFine
      rw [gridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

end

section
@[expose] public section

/-!
# Analytic and grid data for the seventh prepared quartic connector cell
-/

section

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 2147483648 gives scaled squared distance at most one over 512. -/
theorem seventhScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 2147483648) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit)
          (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit)
          (targetImaginary * Grid.GridFineUnit)) ≤ (1 / 512 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit -
        targetReal * Grid.GridFineUnit) ^ 2 +
      (sourceImaginary * Grid.GridFineUnit -
        targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) *
          Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 2147483648 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 512 : Fraction.Rational) := by
      have gridFine := Grid.scaledQuarticGrid
        1 2048 512 (by omega) (by ring1)
      simp only [Nat.cast_ofNat] at gridFine
      rw [gridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell

/-- A coordinate-square sum at most 4398046511104 gives scaled grid squared norm at most four. -/
private theorem quarticGridPointNormLeFour
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 4398046511104) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (4 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 4
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 4398046511104 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (4 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        4398046511104 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          4 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 4 := by rw [cancel]; ring1
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSeventhCell

end

end

section
@[expose] public section

/-!
# Analytic and grid data for the sixth prepared quartic connector cell
-/

section

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 536870912 gives scaled squared distance at most one over 2048. -/
theorem sixthScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 536870912) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit)
          (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit)
          (targetImaginary * Grid.GridFineUnit)) ≤ (1 / 2048 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit -
        targetReal * Grid.GridFineUnit) ^ 2 +
      (sourceImaginary * Grid.GridFineUnit -
        targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) *
          Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 536870912 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 2048 : Fraction.Rational) := by
      have gridFine := Grid.scaledQuarticGrid
        1 512 2048 (by omega) (by ring1)
      simp only [Nat.cast_ofNat] at gridFine
      rw [gridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

end Purelib.Data.Gaussian.Bounds.DyadicGrid

namespace Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell

/-- A coordinate-square sum at most 4398046511104 gives scaled grid squared norm at most four. -/
private theorem quarticGridPointNormLeFour
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 4398046511104) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (4 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 4
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 4398046511104 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (4 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        4398046511104 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          4 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 4 := by rw [cancel]; ring1
end Purelib.Examples.Riemann.ExplicitQuarticPreparedSixthCell

end

end

section
@[expose] public section

/-!
# Analytic and grid data for the third prepared quartic connector cell

The third outer horizontal cell retains the terminal box of the second cell.
Its preparation estimate uses one certified leaf of the finite radicand scan,
and its depth-three grid uses reduced rational representatives for the exact
quadratic boundary checks.
-/

namespace Purelib.Data.Gaussian.Bounds.DyadicGrid

/-- A coordinate-square displacement bound of 17179869184 gives scaled squared distance at most one sixty-fourth. -/
public theorem thirdScaledPointsNormLe
    (sourceReal sourceImaginary targetReal targetImaginary : Fraction.Rational)
    (coefficientLe :
      (sourceReal - targetReal) ^ 2 +
          (sourceImaginary - targetImaginary) ^ 2 ≤ 17179869184) :
    Norm.Basic.normSq
      (Components.Basic.point (sourceReal * Grid.GridFineUnit) (sourceImaginary * Grid.GridFineUnit) -
        Components.Basic.point (targetReal * Grid.GridFineUnit) (targetImaginary * Grid.GridFineUnit)) ≤
      (1 / 64 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  simp only [Basic.sub_re,
    Basic.sub_im,
    Components.Basic.point]
  calc
    (sourceReal * Grid.GridFineUnit - targetReal * Grid.GridFineUnit) ^ 2 +
        (sourceImaginary * Grid.GridFineUnit - targetImaginary * Grid.GridFineUnit) ^ 2 =
      ((sourceReal - targetReal) ^ 2 +
        (sourceImaginary - targetImaginary) ^ 2) * Grid.GridFineUnit ^ 2 := by ring1
    _ ≤ 17179869184 * Grid.GridFineUnit ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe (Fraction.Order.Arithmetic.sq_nonneg_direct Grid.GridFineUnit)
    _ = (1 / 64 : Fraction.Rational) := by
      rw [Grid.oneSixtyFourthQuarticGridFine]
      conv_rhs => rw [Grid.GridFineUnit_eq_scaled_square]
      ring1

/-- A coordinate-square sum at most 281474976710656 gives scaled grid squared norm at most 256. -/
theorem quarticGridPointNormLe256
    (real imaginary : Fraction.Rational)
    (coefficientLe : real ^ 2 + imaginary ^ 2 ≤ 281474976710656) :
    Norm.Basic.normSq
      (Components.Basic.point (real * (1 / 1048576)) (imaginary * (1 / 1048576))) ≤
      (256 : Fraction.Rational) := by
  unfold Norm.Basic.normSq
  change (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
      (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 ≤ 256
  have unitSquareNonnegative : (0 : Fraction.Rational) ≤ (1 / 1048576 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (real * (1 / 1048576 : Fraction.Rational)) ^ 2 +
        (imaginary * (1 / 1048576 : Fraction.Rational)) ^ 2 =
      (real ^ 2 + imaginary ^ 2) * (1 / 1048576 : Fraction.Rational) ^ 2 := by ring1
    _ ≤ 281474976710656 * (1 / 1048576 : Fraction.Rational) ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        coefficientLe unitSquareNonnegative
    _ = (256 : Fraction.Rational) := by
      have cancel : (1 / 1048576 : Fraction.Rational) * 1048576 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega)).ne'
      rw [pow_two]
      calc
        281474976710656 *
            ((1 / 1048576 : Fraction.Rational) * (1 / 1048576)) =
          256 * (((1 / 1048576 : Fraction.Rational) * 1048576) *
            ((1 / 1048576 : Fraction.Rational) * 1048576)) := by ring1
        _ = 256 := by
          rw [cancel]
          ring1
end Purelib.Data.Gaussian.Bounds.DyadicGrid

end
