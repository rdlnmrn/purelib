module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Division
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Cayley.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Geometry.Projective.Homography.Cayley.Bounds

/-- Quadrance at most `1/9` gives the denominator lower bound `normSq (1-z) ≥ 4/9`. -/
theorem one_sub_normSq_lower {z :
  Data.Gaussian.Basic.Canonical} (bound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) :
    4 / 9 ≤ Data.Gaussian.Norm.Basic.normSq (1 - z) := by
  have realSquare : z.re ^ 2 ≤ (1 / 3 : Fraction.Rational) ^ 2 := by
    calc
      z.re ^ 2 ≤ z.re ^ 2 + z.im ^ 2 :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.sq_nonneg_direct z.im)
      _ ≤ 1 / 9 := bound
      _ = (1 / 3 : Fraction.Rational) ^ 2 := by decide
  have realUpper : z.re ≤ 1 / 3 :=
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide) realSquare
  have differenceLower : (2 / 3 : Fraction.Rational) ≤ 1 - z.re := by
    calc
      (2 / 3 : Fraction.Rational) = 1 - 1 / 3 := by decide
      _ ≤ 1 - z.re := Fraction.Order.Arithmetic.sub_le_sub_left_direct realUpper 1
  have differenceNonnegative : 0 ≤ 1 - z.re :=
    (show (0 : Fraction.Rational) ≤ 2 / 3 by decide).trans differenceLower
  have squareLower := Fraction.Order.Arithmetic.pow_le_pow_direct
    (by decide : (0 : Fraction.Rational) ≤ 2 / 3) differenceLower 2
  change (4 / 9 : Fraction.Rational) ≤
    (1 - z.re) ^ 2 + (0 - z.im) ^ 2
  calc
    (4 / 9 : Fraction.Rational) = (2 / 3 : Fraction.Rational) ^ 2 := by decide
    _ ≤ (1 - z.re) ^ 2 := squareLower
    _ ≤ (1 - z.re) ^ 2 + (0 - z.im) ^ 2 :=
      le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.sq_nonneg_direct (0 - z.im))

/-- The Cayley denominator is nonzero on the disk with quadrance at most `1/9`. -/
theorem one_sub_ne_zero {z : Data.Gaussian.Basic.Canonical}
  (bound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) :
    1 - z ≠ 0 := by
  intro equal
  have lower := one_sub_normSq_lower bound
  rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at lower
  have : ¬(4 / 9 : Fraction.Rational) ≤ 0 := by decide
  exact this lower

/-- The difference of two Cayley chart values has numerator twice the input difference.

Both reduced coordinates must have quadrance at most `1/9`, ensuring nonzero denominators. -/
theorem localChart_sub_localChart {x y :
  Data.Gaussian.Basic.Canonical}
    (xBound : Data.Gaussian.Norm.Basic.normSq x ≤ 1 / 9) (yBound : Data.Gaussian.Norm.Basic.normSq y ≤
      1 / 9) :
    (1 + x) / (1 - x) - (1 + y) / (1 - y) =
      Scale.scale 2 (x - y) /
        ((1 - x) * (1 - y)) := by
  have xNonzero := one_sub_ne_zero xBound
  have yNonzero := one_sub_ne_zero yBound
  have productNonzero :=
    Data.Gaussian.Field.mul_ne_zero_direct xNonzero yNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    productNonzero
  calc
    ((1 + x) / (1 - x) - (1 + y) / (1 - y)) *
          ((1 - x) * (1 - y)) =
        (((1 + x) / (1 - x)) * (1 - x)) * (1 - y) -
          (((1 + y) / (1 - y)) * (1 - y)) * (1 - x) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = (1 + x) * (1 - y) - (1 + y) * (1 - x) := by
      rw [Division.gaussian_div_mul_cancel _ _ xNonzero,
        Division.gaussian_div_mul_cancel _ _ yNonzero]
    _ = Scale.scale 2 (x - y) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Scale.scale_re,
          Scale.scale_im, Basic.add_re, Basic.add_im, Basic.sub_re,
          Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.one_re, Basic.one_im] <;> ring1
    _ = (Scale.scale 2 (x - y) /
          ((1 - x) * (1 - y))) * ((1 - x) * (1 - y)) :=
      (Division.gaussian_div_mul_cancel _ _ productNonzero).symm

/-- The rational constant `4/9` is strictly positive. -/
private theorem four_ninths_pos : (0 : Fraction.Rational) <
  4 / 9 := by
  decide

/-- Multiplying `4/9` by nine gives four. -/
private theorem nine_mul_four_ninths :
    (9 : Fraction.Rational) * (4 / 9) = 4 := by
  calc
    (9 : Fraction.Rational) * (4 / 9) = (4 / 9) * 9 :=
      Fraction.Field.mul_comm _ _
    _ = 4 := Fraction.Field.div_mul_cancel_of_ne 4 9 (by decide)

/-- The sensitivity factor `81/4` cancels the product of the two `4/9` denominator bounds. -/
private theorem localChartSensitivity_scalar :
    ((((9 : Fraction.Rational) * 9) / 4) * ((4 / 9) * (4 / 9))) = 4 := by
  decide

/-- Move the two denominator lower bounds into the `81/4` sensitivity factor. -/
private theorem localChartSensitivity_identity (distance :
  Fraction.Rational) :
    4 * distance =
      ((((9 : Fraction.Rational) * 9) / 4) * distance) *
        ((4 / 9) * (4 / 9)) := by
  calc
    4 * distance =
        (((((9 : Fraction.Rational) * 9) / 4) * ((4 / 9) * (4 / 9))) *
          distance) := by rw [localChartSensitivity_scalar]
    _ = ((((9 : Fraction.Rational) * 9) / 4) * distance) *
          ((4 / 9) * (4 / 9)) := by ring1

/-- Square-root-free Lipschitz bound for the local Möbius reconstruction on the certified reduced disk. -/
theorem localChart_input_close {x y :
  Data.Gaussian.Basic.Canonical}
    (xBound : Data.Gaussian.Norm.Basic.normSq x ≤ 1 / 9) (yBound : Data.Gaussian.Norm.Basic.normSq y ≤
      1 / 9) :
    Data.Gaussian.Norm.Basic.normSq ((1 + x) / (1 - x) - (1 + y) / (1 - y)) ≤
      (((9 : Fraction.Rational) * 9) / 4) * Data.Gaussian.Norm.Basic.normSq (x - y) := by
  have xLower := one_sub_normSq_lower xBound
  have yLower := one_sub_normSq_lower yBound
  have denominatorLower :
      (4 / 9 : Fraction.Rational) * (4 / 9) ≤
        Data.Gaussian.Norm.Basic.normSq ((1 - x) * (1 - y)) := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct
      xLower yLower (show (0 : Fraction.Rational) ≤ 4 / 9 by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg (1 - x))
    exact product
  have denominatorPositive :
      0 < Data.Gaussian.Norm.Basic.normSq ((1 - x) * (1 - y)) := by
    exact (Fraction.Order.Arithmetic.mul_pos_direct
      four_ninths_pos
        four_ninths_pos).trans_le denominatorLower
  rw [localChart_sub_localChart xBound yBound,
    Data.Gaussian.Field.normSq_div _ _
      (Data.Gaussian.Field.mul_ne_zero_direct
        (one_sub_ne_zero xBound)
          (one_sub_ne_zero yBound)),
    Scale.normSq_scale]
  rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
  rw [← ExplicitField.div_eq_mul_inv]
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  let distance := Data.Gaussian.Norm.Basic.normSq (x - y)
  let coefficient := (((9 : Fraction.Rational) * 9) / 4) * distance
  have coefficientNonnegative : 0 ≤ coefficient :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Data.Gaussian.Norm.Basic.normSq_nonneg (x - y))
  calc
    4 * Data.Gaussian.Norm.Basic.normSq (x - y) = coefficient * ((4 / 9) * (4 / 9)) := by
      exact localChartSensitivity_identity distance
    _ ≤ coefficient *
          Data.Gaussian.Norm.Basic.normSq ((1 - x) * (1 - y)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorLower coefficientNonnegative

/-- Square-root-free sensitivity bound comparing an independently sampled numerator/denominator quotient with a diagonal
reduced-coordinate sample. -/
theorem asynchronousScaledReduced_input_close
    (factor x y z : Data.Gaussian.Basic.Canonical) (lowerSq sourceBound : Fraction.Rational)
    (lowerPositive : 0 < lowerSq)
    (yLower : lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (factor * y + 1))
    (zLower : lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (factor * z + 1))
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ sourceBound) :
    Data.Gaussian.Norm.Basic.normSq
        ((factor * x - 1) / (factor * y + 1) -
          (factor * z - 1) / (factor * z + 1)) ≤
      (4 * (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
        sourceBound + Data.Gaussian.Norm.Basic.normSq factor) /
          (lowerSq * lowerSq)) *
        (Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (y - z)) := by
  have yPositive : 0 < Data.Gaussian.Norm.Basic.normSq (factor * y + 1) :=
    lowerPositive.trans_le yLower
  have zPositive : 0 < Data.Gaussian.Norm.Basic.normSq (factor * z + 1) :=
    lowerPositive.trans_le zLower
  have yNonzero : factor * y + 1 ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at yPositive
    exact (lt_irrefl _ yPositive).elim
  have zNonzero : factor * z + 1 ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at zPositive
    exact (lt_irrefl _ zPositive).elim
  let distance := Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (y - z)
  have distanceNonnegative : 0 ≤ distance :=
    add_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg (x - z)) (Data.Gaussian.Norm.Basic.normSq_nonneg (y - z))
  have reverseDistance : Data.Gaussian.Norm.Basic.normSq (z - y) = Data.Gaussian.Norm.Basic.normSq (y
    - z) := by
    have reverse : z - y = -(y - z) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
    rw [reverse, Data.Gaussian.Norm.Basic.normSq_neg]
  have xyBound : Data.Gaussian.Norm.Basic.normSq (x - y) ≤ 2 * distance := by
    calc
      Data.Gaussian.Norm.Basic.normSq (x - y) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (x - z) + Data.Gaussian.Norm.Basic.normSq (z - y)) :=
        Data.Gaussian.Norm.Bounds.normSq_sub_le_via x z y
      _ = 2 * distance := by rw [reverseDistance]
  have sumBound :
      Data.Gaussian.Norm.Basic.normSq ((x - z) + (y - z)) ≤ 2 * distance :=
    Data.Gaussian.Norm.Bounds.normSq_add_le_two (x - z) (y - z)
  have sourceBoundNonnegative : 0 ≤ sourceBound :=
    (Data.Gaussian.Norm.Basic.normSq_nonneg z).trans zBound
  let firstTerm := factor * factor * z * (x - y)
  let secondTerm := factor * ((x - z) + (y - z))
  have firstCoefficientNonnegative :
      0 ≤ Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
        Data.Gaussian.Norm.Basic.normSq z :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Data.Gaussian.Norm.Basic.normSq_nonneg factor) (Data.Gaussian.Norm.Basic.normSq_nonneg factor))
      (Data.Gaussian.Norm.Basic.normSq_nonneg z)
  have twiceDistanceNonnegative : 0 ≤ 2 * distance :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      distanceNonnegative
  have firstTermBound :
      Data.Gaussian.Norm.Basic.normSq firstTerm ≤
        (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
          sourceBound) *
          (2 * distance) := by
    change Data.Gaussian.Norm.Basic.normSq (factor * factor * z * (x - y)) ≤ _
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
    calc
      Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
        Data.Gaussian.Norm.Basic.normSq z * Data.Gaussian.Norm.Basic.normSq (x - y) ≤
          (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
            Data.Gaussian.Norm.Basic.normSq z) *
            (2 * distance) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct xyBound
          firstCoefficientNonnegative
      _ ≤ (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
        sourceBound) *
            (2 * distance) := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct _
          twiceDistanceNonnegative
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          zBound
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (Data.Gaussian.Norm.Basic.normSq_nonneg factor) (Data.Gaussian.Norm.Basic.normSq_nonneg factor))
  have secondTermBound :
      Data.Gaussian.Norm.Basic.normSq secondTerm ≤ Data.Gaussian.Norm.Basic.normSq factor * (2 *
        distance) := by
    change Data.Gaussian.Norm.Basic.normSq (factor * ((x - z) + (y - z))) ≤ _
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      sumBound (Data.Gaussian.Norm.Basic.normSq_nonneg factor)
  let numerator := firstTerm + secondTerm
  let numeratorScale :=
    4 * (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor * sourceBound
      + Data.Gaussian.Norm.Basic.normSq factor)
  have numeratorBound : Data.Gaussian.Norm.Basic.normSq numerator ≤ numeratorScale * distance := by
    calc
      Data.Gaussian.Norm.Basic.normSq numerator ≤
          2 * (Data.Gaussian.Norm.Basic.normSq firstTerm + Data.Gaussian.Norm.Basic.normSq secondTerm)
            :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two firstTerm secondTerm
      _ ≤ 2 *
          ((Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq factor *
            sourceBound) *
              (2 * distance) +
            Data.Gaussian.Norm.Basic.normSq factor * (2 * distance)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTermBound secondTermBound) (by decide)
      _ = numeratorScale * distance := by
        dsimp only [numeratorScale]
        ring1
  have numeratorNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq numerator :=
    Data.Gaussian.Norm.Basic.normSq_nonneg numerator
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    Fraction.Order.Arithmetic.mul_pos_direct lowerPositive lowerPositive
  have denominatorLower :
      lowerSq * lowerSq ≤
        Data.Gaussian.Norm.Basic.normSq (factor * y + 1) * Data.Gaussian.Norm.Basic.normSq (factor * z
          + 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_direct
      yLower zLower lowerPositive.le (Data.Gaussian.Norm.Basic.normSq_nonneg (factor * y + 1))
  have inverseNonnegative : 0 ≤ (lowerSq * lowerSq)⁻¹ :=
    (Fraction.Order.Field.inv_pos_direct lowerProductPositive).le
  rw [Geometry.Projective.Homography.Cayley.Basic.asynchronousScaledReduced_sub_scaledReduced factor x y z
      yNonzero zNonzero,
    Data.Gaussian.Field.normSq_div _ _
      (Data.Gaussian.Field.mul_ne_zero_direct
        yNonzero zNonzero), Data.Gaussian.Norm.Basic.normSq_mul]
  change Data.Gaussian.Norm.Basic.normSq numerator /
      (Data.Gaussian.Norm.Basic.normSq (factor * y + 1) * Data.Gaussian.Norm.Basic.normSq (factor * z
        + 1)) ≤ _
  calc
    Data.Gaussian.Norm.Basic.normSq numerator /
          (Data.Gaussian.Norm.Basic.normSq (factor * y + 1) * Data.Gaussian.Norm.Basic.normSq (factor
            * z + 1)) ≤
        Data.Gaussian.Norm.Basic.normSq numerator / (lowerSq * lowerSq) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ ≤ (numeratorScale * distance) / (lowerSq * lowerSq) := by
      change Data.Gaussian.Norm.Basic.normSq numerator * (lowerSq * lowerSq)⁻¹ ≤
        (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorBound inverseNonnegative
    _ = (numeratorScale / (lowerSq * lowerSq)) * distance := by
      change (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹ =
        (numeratorScale * (lowerSq * lowerSq)⁻¹) * distance
      calc
        (numeratorScale * distance) * (lowerSq * lowerSq)⁻¹ =
            numeratorScale *
              (distance * (lowerSq * lowerSq)⁻¹) :=
          Fraction.Field.mul_assoc _ _ _
        _ = numeratorScale *
              ((lowerSq * lowerSq)⁻¹ * distance) := by
          rw [Fraction.Field.mul_comm distance
            ((lowerSq * lowerSq)⁻¹)]
        _ = (numeratorScale * (lowerSq * lowerSq)⁻¹) * distance :=
          (Fraction.Field.mul_assoc _ _ _).symm

/-- Exact inverse of the scaled reduced-coordinate map on the certified local disk. -/
theorem scaledReduced_chart (factor value :
  Data.Gaussian.Basic.Canonical)
    (denominatorNonzero : factor * value + 1 ≠ 0)
    (reducedBound :
      Data.Gaussian.Norm.Basic.normSq ((factor * value - 1) / (factor * value + 1)) ≤ 1 / 9) :
    (1 + (factor * value - 1) / (factor * value + 1)) /
        (1 - (factor * value - 1) / (factor * value + 1)) =
      factor * value := by
  let scaled := factor * value
  let reduced := (scaled - 1) / (scaled + 1)
  have reducedIdentity : reduced * (scaled + 1) = scaled - 1 :=
    Division.gaussian_div_mul_cancel (scaled - 1) (scaled + 1) denominatorNonzero
  have oneSubNonzero : 1 - reduced ≠ 0 :=
    one_sub_ne_zero reducedBound
  have reducedCancellation :
      (1 - reduced) * (scaled + 1) = 1 + 1 := by
    calc
      (1 - reduced) * (scaled + 1) =
          (scaled + 1) - reduced * (scaled + 1) := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
            Basic.one_re, Basic.one_im] <;> ring1
      _ = (scaled + 1) - (scaled - 1) := by rw [reducedIdentity]
      _ = 1 + 1 := by
        apply Data.Gaussian.Basic.ext <;>
          simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im] <;> ring1
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    oneSubNonzero
  rw [Division.gaussian_div_mul_cancel (1 + reduced) (1 - reduced) oneSubNonzero]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (1 + reduced) * (scaled + 1) =
        (scaled + 1) + reduced * (scaled + 1) := by ring1
    _ = (scaled + 1) + (scaled - 1) := by rw [reducedIdentity]
    _ = scaled * (1 - reduced) * (scaled + 1) := by
      rw [Data.Gaussian.Basic.mul_assoc, reducedCancellation]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
          Basic.one_re, Basic.one_im] <;> ring1

/-- Finite sensitivity of the scaled reduced-coordinate map under one displayed positive denominator-quadrance lower
bound. -/
theorem scaledReduced_input_close (factor x y :
  Data.Gaussian.Basic.Canonical)
    (lowerSq : Fraction.Rational) (lowerPositive : 0 < lowerSq)
    (xLower : lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (factor * x + 1))
    (yLower : lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (factor * y + 1)) :
    Data.Gaussian.Norm.Basic.normSq
        ((factor * x - 1) / (factor * x + 1) -
          (factor * y - 1) / (factor * y + 1)) ≤
      ((4 * Data.Gaussian.Norm.Basic.normSq factor) / (lowerSq * lowerSq)) *
        Data.Gaussian.Norm.Basic.normSq (x - y) := by
  have xPositive : 0 < Data.Gaussian.Norm.Basic.normSq (factor * x + 1) :=
    lowerPositive.trans_le xLower
  have yPositive : 0 < Data.Gaussian.Norm.Basic.normSq (factor * y + 1) :=
    lowerPositive.trans_le yLower
  have xNonzero : factor * x + 1 ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at xPositive
    exact (lt_irrefl _ xPositive).elim
  have yNonzero : factor * y + 1 ≠ 0 := by
    intro equal
    rw [equal, Data.Gaussian.Norm.Basic.normSq_zero] at yPositive
    exact (lt_irrefl _ yPositive).elim
  have lowerProductPositive : 0 < lowerSq * lowerSq :=
    Fraction.Order.Arithmetic.mul_pos_direct lowerPositive lowerPositive
  have denominatorLower :
      lowerSq * lowerSq ≤
        Data.Gaussian.Norm.Basic.normSq (factor * x + 1) * Data.Gaussian.Norm.Basic.normSq (factor * y
          + 1) := by
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      xLower yLower lowerPositive.le (Data.Gaussian.Norm.Basic.normSq_nonneg (factor * x + 1))
  let numerator := 4 * Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq (x -
    y)
  have numeratorNonnegative : 0 ≤ numerator :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg factor))
      (Data.Gaussian.Norm.Basic.normSq_nonneg (x - y))
  rw [Geometry.Projective.Homography.Cayley.Basic.scaledReduced_sub_scaledReduced factor x y xNonzero yNonzero,
    Data.Gaussian.Field.normSq_div _ _
      (Data.Gaussian.Field.mul_ne_zero_direct
        xNonzero yNonzero),
    Scale.normSq_scale, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul]
  rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
  rw [← ExplicitField.div_eq_mul_inv]
  calc
    4 * (Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq (x - y)) /
          (Data.Gaussian.Norm.Basic.normSq (factor * x + 1) * Data.Gaussian.Norm.Basic.normSq (factor
            * y + 1)) =
        numerator /
          (Data.Gaussian.Norm.Basic.normSq (factor * x + 1) * Data.Gaussian.Norm.Basic.normSq (factor
            * y + 1)) := by
      dsimp only [numerator]
      congr 1
      ring1
    _ ≤ numerator / (lowerSq * lowerSq) :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ = ((4 * Data.Gaussian.Norm.Basic.normSq factor) / (lowerSq * lowerSq)) *
          Data.Gaussian.Norm.Basic.normSq (x - y) := by
      rw [ExplicitField.div_eq_mul_inv,
        ExplicitField.div_eq_mul_inv]
      dsimp only [numerator]
      calc
        (4 * Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq (x - y)) *
              (lowerSq * lowerSq)⁻¹ =
            (4 * Data.Gaussian.Norm.Basic.normSq factor) *
              (Data.Gaussian.Norm.Basic.normSq (x - y) * (lowerSq * lowerSq)⁻¹) :=
          Fraction.Field.mul_assoc _ _ _
        _ = (4 * Data.Gaussian.Norm.Basic.normSq factor) *
              ((lowerSq * lowerSq)⁻¹ * Data.Gaussian.Norm.Basic.normSq (x - y)) := by
          rw [Fraction.Field.mul_comm
            (Data.Gaussian.Norm.Basic.normSq (x - y)) ((lowerSq * lowerSq)⁻¹)]
        _ = ((4 * Data.Gaussian.Norm.Basic.normSq factor) * (lowerSq * lowerSq)⁻¹) *
              Data.Gaussian.Norm.Basic.normSq (x - y) :=
          (Fraction.Field.mul_assoc _ _ _).symm
end Purelib.Geometry.Projective.Homography.Cayley.Bounds

end
