module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds
public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Root-free optimal determinant-index-two window

The centered index-two chamber has the same optimal window boundary as the
index-one chamber, but its determinant gap is twice as large.  This module
keeps that boundary entirely rational.  For a displayed gap cut `t`, put
`s = t / 3`.  The condition

`t ^ 2 - 12 * t + 9 >= 0`

becomes

`s ^ 2 - 4 * s + 1 >= 0`.

The affine function

`(s / (1 - s ^ 2)) * (X + 1)`

is then a rational minorant for the larger coordinate of a normalized vector
of quadrance `X`.  At the omitted algebraic endpoint it agrees with the usual
square-root expression, but neither the definition nor its proof constructs a
square root or a completed real number.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal

/-- The norm polynomial obtained from the optimal gap polynomial by the
substitution `t = 3 * s`. -/
def normPolynomial (value :
  Fraction.Rational) : Fraction.Rational :=
  value ^ 2 - 4 * value + 1

/-- The displayed norm cut corresponding to a displayed determinant-gap cut. -/
def normCut (gap : Fraction.Rational) :
  Fraction.Rational := gap / 3

/-- The rational slope of the endpoint-exact affine coordinate minorant. -/
def componentSlope (gap : Fraction.Rational)
  : Fraction.Rational :=
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  cut / (1 - cut ^ 2)

/-- The endpoint-exact rational affine minorant for a larger coordinate. -/
def componentLower (gap norm :
  Fraction.Rational) : Fraction.Rational :=
  Dirichlet.Window.IndexTwo.Optimal.componentSlope gap * (norm + 1)

/-- The useful displayed part of the exact centered cut.  The lower bound
`3/4` is internal proof slack: it contains the previous `205/256` cut and all
rational cuts approaching the optimal quadratic boundary. -/
def IsCenteredGapThreshold (gap :
  Fraction.Rational) : Prop :=
  (3 / 4 : Fraction.Rational) ≤ gap ∧
    Dirichlet.Window.IndexOne.Optimal.IsGapThreshold gap

/-- Multiplying the norm cut by three recovers its displayed determinant-gap threshold. -/
theorem normCut_mul_three (gap :
  Fraction.Rational) : Dirichlet.Window.IndexTwo.Optimal.normCut gap * 3 = gap := by
  unfold Dirichlet.Window.IndexTwo.Optimal.normCut
  exact Fraction.Field.div_mul_cancel_of_ne gap 3 (by decide)

/-- A centered gap certificate gives a nonnegative norm cut. -/
private theorem normCut_nonnegative
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.normCut gap := by
  unfold Dirichlet.Window.IndexTwo.Optimal.normCut
  exact Fraction.Order.Field.div_nonneg_direct
    ((show (0 : Fraction.Rational) ≤ 3 / 4 by decide).trans certificate.1)
    (by decide)

/-- The norm cut of a centered gap certificate lies strictly below one third. -/
private theorem normCut_lt_oneThird
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.normCut gap < 1 / 3 := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (show (0 : Fraction.Rational) < 3 by decide)).mpr
  calc
    gap < 1 := certificate.2.1
    _ = (1 / 3 : Fraction.Rational) * 3 :=
      (Fraction.Field.div_mul_cancel_of_ne 1 3
        (by decide)).symm

/-- The norm cut of a centered gap certificate lies strictly inside the unit interval. -/
private theorem normCut_lt_one
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.normCut gap < 1 :=
  (Dirichlet.Window.IndexTwo.Optimal.normCut_lt_oneThird certificate).trans (by decide)

/-- The lower bound three quarters on the gap places its norm cut at least one quarter. -/
private theorem oneFourth_le_normCut
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    (1 / 4 : Fraction.Rational) ≤ Dirichlet.Window.IndexTwo.Optimal.normCut gap := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (show (0 : Fraction.Rational) < 3 by decide)).mpr
  calc
    (1 / 4 : Fraction.Rational) * 3 = 3 / 4 := by decide
    _ ≤ gap := certificate.1

/-- The centered gap polynomial certifies nonnegativity of the corresponding norm polynomial.

Substitution of the norm cut rescales the original gap polynomial by nine. -/
private theorem
  normCut_polynomial_nonnegative
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial (Dirichlet.Window.IndexTwo.Optimal.normCut gap) := by
  have identity :
      Dirichlet.Window.IndexTwo.Optimal.normPolynomial (Dirichlet.Window.IndexTwo.Optimal.normCut gap) * 9 =
        Dirichlet.Window.IndexOne.Optimal.gapPolynomial gap := by
    unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial Dirichlet.Window.IndexOne.Optimal.gapPolynomial
    calc
      (Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2 - 4 * Dirichlet.Window.IndexTwo.Optimal.normCut gap + 1) * 9 =
          (Dirichlet.Window.IndexTwo.Optimal.normCut gap * 3) ^ 2 - 12 * (Dirichlet.Window.IndexTwo.Optimal.normCut gap
            * 3) + 9 := by
        ring1
      _ = gap ^ 2 - 12 * gap + 9 := by rw [Dirichlet.Window.IndexTwo.Optimal.normCut_mul_three]
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 9)
  · calc
      (0 : Fraction.Rational) * 9 = 0 := by ring1
      _ ≤ Dirichlet.Window.IndexOne.Optimal.gapPolynomial gap := certificate.2.2
      _ = Dirichlet.Window.IndexTwo.Optimal.normPolynomial (Dirichlet.Window.IndexTwo.Optimal.normCut gap) * 9 :=
        identity.symm
  · decide

/-- The nonnegative centered norm cut has square strictly below one. -/
private theorem normCut_sq_lt_one
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2 < 1 := by
  have cutNonnegative := Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have cutLtOne := Dirichlet.Window.IndexTwo.Optimal.normCut_lt_one certificate
  have cutSqLeCut : Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2 ≤ Dirichlet.Window.IndexTwo.Optimal.normCut gap :=
    by
    rw [pow_two]
    calc
      Dirichlet.Window.IndexTwo.Optimal.normCut gap * Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ 1 *
        Dirichlet.Window.IndexTwo.Optimal.normCut gap :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          cutLtOne.le cutNonnegative
      _ = Dirichlet.Window.IndexTwo.Optimal.normCut gap := by ring1
  exact cutSqLeCut.trans_lt cutLtOne

/-- The denominator defining the affine coordinate slope is strictly positive for a centered gap certificate. -/
private theorem slopeDenominator_pos
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    0 < 1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2 :=
  Fraction.Order.Arithmetic.sub_pos_direct
    (Dirichlet.Window.IndexTwo.Optimal.normCut_sq_lt_one certificate)

/-- Multiplication by its positive denominator recovers the centered norm cut from the coordinate slope. -/
private theorem
  componentSlope_mul_denominator
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.componentSlope gap * (1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2) =
      Dirichlet.Window.IndexTwo.Optimal.normCut gap := by
  unfold Dirichlet.Window.IndexTwo.Optimal.componentSlope
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Dirichlet.Window.IndexTwo.Optimal.slopeDenominator_pos certificate).ne'

/-- The affine coordinate slope is nonnegative for a centered gap certificate. -/
private theorem componentSlope_nonnegative
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.componentSlope gap := by
  unfold Dirichlet.Window.IndexTwo.Optimal.componentSlope
  exact Fraction.Order.Field.div_nonneg_direct
    (Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate)
    (Dirichlet.Window.IndexTwo.Optimal.slopeDenominator_pos certificate).le

/-- The centered norm polynomial bounds twelve times the squared coordinate slope by one.

The proof factors the denominator difference into the norm polynomial and its nonnegative companion, then cancels the
positive squared denominator. -/
private theorem
  twelve_mul_componentSlope_sq_le_one
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    12 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 ≤ 1 := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let denominator := 1 - cut ^ 2
  let slope := Dirichlet.Window.IndexTwo.Optimal.componentSlope gap
  have cutNonnegative : (0 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have polynomialNonnegative : 0 ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_polynomial_nonnegative certificate
  have companionNonnegative : 0 ≤ cut ^ 2 + 4 * cut + 1 :=
    add_nonneg
      (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct cut)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          cutNonnegative))
      (by decide)
  have denominatorDifferenceNonnegative :
      0 ≤ denominator ^ 2 - 12 * cut ^ 2 := by
    calc
      0 ≤ (cut ^ 2 + 4 * cut + 1) * Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut :=
        Fraction.Order.Arithmetic.mul_nonneg_direct companionNonnegative
          polynomialNonnegative
      _ = denominator ^ 2 - 12 * cut ^ 2 := by
        dsimp only [denominator]
        unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial
        ring1
  have scaledCutBound : 12 * cut ^ 2 ≤ denominator ^ 2 :=
    Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      denominatorDifferenceNonnegative
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator, cut]
    exact Dirichlet.Window.IndexTwo.Optimal.slopeDenominator_pos certificate
  have denominatorSquarePositive : 0 < denominator ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct denominatorPositive 2
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := denominator ^ 2)
  · calc
      (12 * slope ^ 2) * denominator ^ 2 =
          12 * (slope * denominator) ^ 2 := by ring1
      _ = 12 * cut ^ 2 := by
        have slopeIdentity : slope * denominator = cut := by
          dsimp only [slope, denominator, cut]
          exact Dirichlet.Window.IndexTwo.Optimal.componentSlope_mul_denominator certificate
        rw [slopeIdentity]
      _ ≤ denominator ^ 2 := scaledCutBound
      _ = 1 * denominator ^ 2 := by ring1
  · exact denominatorSquarePositive

/-- Four times the squared coordinate slope is at most one half for a centered gap certificate. -/
private theorem
  four_mul_componentSlope_sq_le_half
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    4 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 ≤ 1 / 2 := by
  have scaled := Dirichlet.Window.IndexTwo.Optimal.twelve_mul_componentSlope_sq_le_one certificate
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 3)
  · calc
      (4 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2) * 3 =
          12 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 := by ring1
      _ ≤ 1 := scaled
      _ ≤ (1 / 2 : Fraction.Rational) * 3 := by decide
  · decide

/-- The affine coordinate minorant is nonnegative at every nonnegative norm for a centered gap certificate. -/
private theorem componentLower_nonnegative
    {gap norm : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (normNonnegative : 0 ≤ norm) :
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.componentLower gap norm := by
  unfold Dirichlet.Window.IndexTwo.Optimal.componentLower
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Dirichlet.Window.IndexTwo.Optimal.componentSlope_nonnegative certificate)
    (add_nonneg normNonnegative (by decide))

/-- At the norm cut, multiplying the coordinate minorant by the complementary gap recovers the cut. -/
private theorem
  componentLower_cut_mul_complement
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.componentLower gap (Dirichlet.Window.IndexTwo.Optimal.normCut gap) * (1 -
      Dirichlet.Window.IndexTwo.Optimal.normCut gap) = Dirichlet.Window.IndexTwo.Optimal.normCut gap := by
  unfold Dirichlet.Window.IndexTwo.Optimal.componentLower
  calc
    Dirichlet.Window.IndexTwo.Optimal.componentSlope gap * (Dirichlet.Window.IndexTwo.Optimal.normCut gap + 1) * (1 -
      Dirichlet.Window.IndexTwo.Optimal.normCut gap) =
        Dirichlet.Window.IndexTwo.Optimal.componentSlope gap * (1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap ^ 2)
          := by ring1
    _ = Dirichlet.Window.IndexTwo.Optimal.normCut gap :=
      Dirichlet.Window.IndexTwo.Optimal.componentSlope_mul_denominator certificate

/-- The centered norm polynomial bounds twice the cut by the square of its complementary gap. -/
private theorem
  two_mul_normCut_le_complement_sq
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    2 * Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ (1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap) ^ 2 := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial (Dirichlet.Window.IndexTwo.Optimal.normCut gap) :=
      Dirichlet.Window.IndexTwo.Optimal.normCut_polynomial_nonnegative certificate
    _ = (1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap) ^ 2 - 2 * Dirichlet.Window.IndexTwo.Optimal.normCut gap :=
      by
      unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial
      ring1

/-- At the norm cut, the square of the coordinate minorant is at most half the cut.

The endpoint identity and centered norm polynomial give the estimate after cancellation of the positive squared
complement. -/
private theorem
  componentLower_cut_sq_le_half
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.componentLower gap (Dirichlet.Window.IndexTwo.Optimal.normCut gap) ^ 2 ≤
      Dirichlet.Window.IndexTwo.Optimal.normCut gap / 2 := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let complement := 1 - cut
  let lower := Dirichlet.Window.IndexTwo.Optimal.componentLower gap cut
  have cutNonnegative : (0 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have complementPositive : 0 < complement := by
    dsimp only [complement, cut]
    exact Fraction.Order.Arithmetic.sub_pos_direct
      (Dirichlet.Window.IndexTwo.Optimal.normCut_lt_one certificate)
  have complementSquarePositive : 0 < complement ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct complementPositive 2
  have scaledQuadratic : 2 * cut ^ 2 ≤ cut * complement ^ 2 := by
    have multiplied :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Dirichlet.Window.IndexTwo.Optimal.two_mul_normCut_le_complement_sq certificate) cutNonnegative
    dsimp only [cut, complement] at multiplied ⊢
    convert multiplied using 1
    all_goals ring1
  apply (Fraction.Order.Field.le_div_iff_pos
    (show (0 : Fraction.Rational) < 2 by decide)).mpr
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := complement ^ 2)
  · calc
      (lower ^ 2 * 2) * complement ^ 2 =
          2 * (lower * complement) ^ 2 := by ring1
      _ = 2 * cut ^ 2 := by
        have lowerIdentity : lower * complement = cut := by
          dsimp only [lower, complement, cut]
          exact Dirichlet.Window.IndexTwo.Optimal.componentLower_cut_mul_complement certificate
        rw [lowerIdentity]
      _ ≤ cut * complement ^ 2 := scaledQuadratic
  · exact complementSquarePositive

/-- On the exact rational norm chamber, the endpoint-dependent affine
minorant has square at most half the quadrance. -/
theorem componentLower_sq_le_half
    {gap norm : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (cutLe : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ norm) (normLeOne : norm ≤ 1) :
    Dirichlet.Window.IndexTwo.Optimal.componentLower gap norm ^ 2 ≤ norm / 2 := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let slope := Dirichlet.Window.IndexTwo.Optimal.componentSlope gap
  have cutLeOne : cut ≤ (1 : Fraction.Rational) :=
    (Dirichlet.Window.IndexTwo.Optimal.normCut_lt_one certificate).le
  have normPlusCutPlusTwoLeFour : norm + cut + 2 ≤ (4 : Fraction.Rational) := by
    have first := Fraction.Order.Arithmetic.add_le_add_direct
      normLeOne cutLeOne
    have second := Fraction.Order.Arithmetic.add_le_add_right_direct first 2
    calc
      norm + cut + 2 ≤ (1 : Fraction.Rational) + 1 + 2 := second
      _ = 4 := by ring1
  have slopeSquareNonnegative : 0 ≤ slope ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct slope
  have scaledLeHalf :
      slope ^ 2 * (norm + cut + 2) ≤ 1 / 2 := by
    calc
      slope ^ 2 * (norm + cut + 2) ≤ slope ^ 2 * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          normPlusCutPlusTwoLeFour slopeSquareNonnegative
      _ = 4 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 := by
        dsimp only [slope]
        ring1
      _ ≤ 1 / 2 := Dirichlet.Window.IndexTwo.Optimal.four_mul_componentSlope_sq_le_half certificate
  have factorNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) - slope ^ 2 * (norm + cut + 2) :=
    Fraction.Order.Arithmetic.sub_nonneg_direct scaledLeHalf
  have endpointNonnegative :
      0 ≤ cut / 2 - Dirichlet.Window.IndexTwo.Optimal.componentLower gap cut ^ 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct
      (Dirichlet.Window.IndexTwo.Optimal.componentLower_cut_sq_le_half certificate)
  have offsetNonnegative : 0 ≤ norm - cut :=
    Fraction.Order.Arithmetic.sub_nonneg_direct cutLe
  have certificateNonnegative :
      0 ≤ (cut / 2 - Dirichlet.Window.IndexTwo.Optimal.componentLower gap cut ^ 2) +
        (norm - cut) *
          (1 / 2 - slope ^ 2 * (norm + cut + 2)) :=
    add_nonneg endpointNonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
        factorNonnegative)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (cut / 2 - Dirichlet.Window.IndexTwo.Optimal.componentLower gap cut ^ 2) +
        (norm - cut) *
          (1 / 2 - slope ^ 2 * (norm + cut + 2)) :=
      certificateNonnegative
    _ = norm / 2 - Dirichlet.Window.IndexTwo.Optimal.componentLower gap norm ^ 2 := by
      unfold Dirichlet.Window.IndexTwo.Optimal.componentLower
      dsimp only [slope]
      rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul cut,
        Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul norm]
      ring1

/-- The affine minorant bounds the larger of two nonnegative coordinates from below.

The norm must be their squared sum and lie between the centered cut and one; comparison of squares yields the coordinate
inequality. -/
private theorem
  componentLower_le_largerCoordinate
    {gap large small norm : Fraction.Rational}
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (largeNonnegative : 0 ≤ large) (smallNonnegative : 0 ≤ small)
    (smallLeLarge : small ≤ large)
    (normIdentity : norm = large ^ 2 + small ^ 2)
    (cutLe : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ norm) (normLeOne : norm ≤ 1) :
    Dirichlet.Window.IndexTwo.Optimal.componentLower gap norm ≤ large := by
  have smallSquareLeLargeSquare : small ^ 2 ≤ large ^ 2 := by
    simpa only [pow_two] using
      Fraction.Order.Arithmetic.mul_le_mul_direct smallLeLarge smallLeLarge
        smallNonnegative largeNonnegative
  have halfNormLeLargeSquare : norm / 2 ≤ large ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (norm / 2) * 2 = norm :=
          Fraction.Field.div_mul_cancel_of_ne norm 2 (by decide)
        _ = large ^ 2 + small ^ 2 := normIdentity
        _ ≤ large ^ 2 + large ^ 2 :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            smallSquareLeLargeSquare
        _ = large ^ 2 * 2 := by ring1
    · decide
  exact Fraction.Order.Arithmetic.le_of_sq_le_sq_direct largeNonnegative
    ((Dirichlet.Window.IndexTwo.Optimal.componentLower_sq_le_half certificate cutLe normLeOne).trans
      halfNormLeLargeSquare)

/-- The coordinate slope of a centered gap certificate is at most one half. -/
private theorem componentSlope_le_half
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ≤ 1 / 2 := by
  have slopeNonnegative := Dirichlet.Window.IndexTwo.Optimal.componentSlope_nonnegative certificate
  have slopeSquareLeTwelfth :
      Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 ≤ 1 / 12 := by
    apply (Fraction.Order.Field.le_div_iff_pos
      (show (0 : Fraction.Rational) < 12 by decide)).mpr
    calc
      Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 * 12 =
          12 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 := by ring1
      _ ≤ 1 := Dirichlet.Window.IndexTwo.Optimal.twelve_mul_componentSlope_sq_le_one certificate
  have slopeSquareLeQuarter :
      Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 ≤ (1 / 2 : Fraction.Rational) ^ 2 :=
    slopeSquareLeTwelfth.trans (by decide)
  exact Fraction.Order.Arithmetic.le_of_sq_le_sq_direct (by decide)
    slopeSquareLeQuarter

/-- The centered norm cut is no larger than its coordinate slope. -/
private theorem normCut_le_componentSlope
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ Dirichlet.Window.IndexTwo.Optimal.componentSlope gap := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let denominator := 1 - cut ^ 2
  have cutNonnegative : (0 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator, cut]
    exact Dirichlet.Window.IndexTwo.Optimal.slopeDenominator_pos certificate
  have denominatorLeOne : denominator ≤ (1 : Fraction.Rational) := by
    dsimp only [denominator]
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ cut ^ 2 := Fraction.Order.Arithmetic.sq_nonneg_direct cut
      _ = 1 - (1 - cut ^ 2) := by ring1
  unfold Dirichlet.Window.IndexTwo.Optimal.componentSlope
  apply (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mpr
  calc
    cut * denominator ≤ cut * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorLeOne cutNonnegative
    _ = cut := by ring1

/-- The aligned-floor increment coefficient is nonnegative at the centered norm cut.

The lower cut bound of one quarter and the slope lower bound certify the displayed cubic expression directly over the
rationals. -/
private theorem cutFactor_nonnegative
    {gap : Fraction.Rational} (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap) :
    0 ≤ Dirichlet.Window.IndexTwo.Optimal.normCut gap +
      2 * Dirichlet.Window.IndexTwo.Optimal.componentSlope gap ^ 2 * (Dirichlet.Window.IndexTwo.Optimal.normCut gap + 1)
        -
        (1 - Dirichlet.Window.IndexTwo.Optimal.normCut gap) / 2 := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let slope := Dirichlet.Window.IndexTwo.Optimal.componentSlope gap
  let base := fun value : Fraction.Rational =>
    value + 2 * value ^ 2 * (value + 1) - (1 - value) / 2
  have cutNonnegative : (0 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have quarterLeCut : (1 / 4 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.oneFourth_le_normCut certificate
  have cutLeSlope : cut ≤ slope := by
    dsimp only [cut, slope]
    exact Dirichlet.Window.IndexTwo.Optimal.normCut_le_componentSlope certificate
  have cutSquareLeSlopeSquare : cut ^ 2 ≤ slope ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct cutNonnegative cutLeSlope 2
  have cutPlusOneNonnegative : 0 ≤ cut + 1 :=
    add_nonneg cutNonnegative (by decide)
  have scaledSquareLower :
      2 * cut ^ 2 * (cut + 1) ≤ 2 * slope ^ 2 * (cut + 1) := by
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        cutSquareLeSlopeSquare (by decide)) cutPlusOneNonnegative
  have baseQuarterPositive : (0 : Fraction.Rational) < base (1 / 4) := by
    dsimp only [base]
    decide
  have offsetNonnegative : 0 ≤ cut - 1 / 4 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct quarterLeCut
  have multiplierNonnegative :
      0 ≤ 2 * (cut ^ 2 + cut * (1 / 4) + (1 / 4) ^ 2) +
        2 * (cut + 1 / 4) + 1 + 1 / 2 := by
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg
              (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct cut)
                (Fraction.Order.Arithmetic.mul_nonneg_direct cutNonnegative
                  (by decide)))
              (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 4))))
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (add_nonneg cutNonnegative (by decide))))
        (by decide))
      (by decide)
  have baseMonotone : base (1 / 4) ≤ base cut := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (cut - 1 / 4) *
          (2 * (cut ^ 2 + cut * (1 / 4) + (1 / 4) ^ 2) +
            2 * (cut + 1 / 4) + 1 + 1 / 2) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          multiplierNonnegative
      _ = base cut - base (1 / 4) := by
        dsimp only [base]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - cut),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - 1 / 4)]
        ring1
  calc
    (0 : Fraction.Rational) ≤ base (1 / 4) := baseQuarterPositive.le
    _ ≤ base cut := baseMonotone
    _ ≤ cut + 2 * slope ^ 2 * (cut + 1) - (1 - cut) / 2 := by
      dsimp only [base]
      calc
        cut + 2 * cut ^ 2 * (cut + 1) - (1 - cut) / 2 =
            2 * cut ^ 2 * (cut + 1) +
              (cut - (1 - cut) / 2) := by ring1
        _ ≤ 2 * slope ^ 2 * (cut + 1) +
              (cut - (1 - cut) / 2) :=
          Fraction.Order.Arithmetic.add_le_add_right_direct
            scaledSquareLower _
        _ = cut + 2 * slope ^ 2 * (cut + 1) -
              (1 - cut) / 2 := by ring1

/-- A rational lower bound for determinant-gap excess when the larger coordinates align.

It combines the norm product, the product of the two affine coordinate minorants, and half the product of complementary
norms. -/
private def alignedExcessFloor
    (gap firstNorm secondNorm : Fraction.Rational) : Fraction.Rational :=
  firstNorm * secondNorm +
    2 * (Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm *
      Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm) +
    ((1 - firstNorm) * (1 - secondNorm)) / 2

/-- A rational lower bound for determinant-gap excess when the larger coordinates cross.

It combines the norm product with each affine coordinate minorant multiplied by the opposite complementary norm. -/
private def crossExcessFloor
    (gap firstNorm secondNorm : Fraction.Rational) : Fraction.Rational :=
  firstNorm * secondNorm +
    Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm * (1 - secondNorm) +
    (1 - firstNorm) * Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm

/-- Twice the product of two rational halves equals half the product. -/
private theorem twice_half_mul_half
    (first second : Fraction.Rational) :
    2 * ((first / 2) * (second / 2)) = (first * second) / 2 := by
  rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul first,
    Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul second,
    Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (first * second)]
  have halfCertificate :
      (2 : Fraction.Rational) * (1 / 2) * (1 / 2) = 1 / 2 := by decide
  calc
    2 * ((1 / 2 * first) * (1 / 2 * second)) =
        (2 * (1 / 2) * (1 / 2)) * (first * second) := by ring1
    _ = (1 / 2) * (first * second) := by rw [halfCertificate]

/-- The crossed floor exceeds the target determinant-gap excess above both centered norm cuts.

The nonnegative product coefficient makes the endpoint estimate persist for every pair of norms above the cut. -/
private theorem targetExcess_le_crossFloor
    {gap firstNorm secondNorm : Fraction.Rational}
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (firstLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ firstNorm)
    (secondLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ secondNorm) :
    2 * gap - 1 ≤ Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap firstNorm secondNorm := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let slope := Dirichlet.Window.IndexTwo.Optimal.componentSlope gap
  have cutNonnegative : (0 : Fraction.Rational) ≤ cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_nonnegative certificate
  have firstNonnegative : (0 : Fraction.Rational) ≤ firstNorm :=
    cutNonnegative.trans firstLower
  have productLower : cut ^ 2 ≤ firstNorm * secondNorm := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct firstLower secondLower
      cutNonnegative firstNonnegative
  have coefficientNonnegative : 0 ≤ (1 : Fraction.Rational) - 2 * slope := by
    apply Fraction.Order.Arithmetic.sub_nonneg_direct
    calc
      2 * slope ≤ 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Dirichlet.Window.IndexTwo.Optimal.componentSlope_le_half certificate) (by decide)
      _ = 1 := by decide
  have scaledProductLower :
      (1 - 2 * slope) * cut ^ 2 ≤
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productLower
      coefficientNonnegative
  have endpointIdentity :
      2 * slope + (1 - 2 * slope) * cut ^ 2 = cut ^ 2 + 2 * cut := by
    have slopeIdentity : slope * (1 - cut ^ 2) = cut := by
      dsimp only [slope, cut]
      exact Dirichlet.Window.IndexTwo.Optimal.componentSlope_mul_denominator certificate
    calc
      2 * slope + (1 - 2 * slope) * cut ^ 2 =
          cut ^ 2 + 2 * (slope * (1 - cut ^ 2)) := by ring1
      _ = cut ^ 2 + 2 * cut := by rw [slopeIdentity]
  have thresholdIdentity : gap = cut * 3 := by
    dsimp only [cut]
    exact (Dirichlet.Window.IndexTwo.Optimal.normCut_mul_three gap).symm
  have endpointLower : 2 * gap - 1 ≤ cut ^ 2 + 2 * cut := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut :=
        Dirichlet.Window.IndexTwo.Optimal.normCut_polynomial_nonnegative certificate
      _ = (cut ^ 2 + 2 * cut) - (2 * gap - 1) := by
        rw [thresholdIdentity]
        unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial
        ring1
  calc
    2 * gap - 1 ≤ cut ^ 2 + 2 * cut := endpointLower
    _ = 2 * slope + (1 - 2 * slope) * cut ^ 2 := endpointIdentity.symm
    _ ≤ 2 * slope +
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledProductLower
    _ = Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap firstNorm secondNorm := by
      unfold Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor Dirichlet.Window.IndexTwo.Optimal.componentLower
      dsimp only [slope]
      ring1

/-- At the common norm cut, the aligned floor is at least the crossed floor.

Their difference is twice the square of the affine minorant minus half the complementary norm. -/
private theorem
  crossFloor_cut_cut_le_alignedFloor_cut_cut
    {gap : Fraction.Rational} :
    Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap (Dirichlet.Window.IndexTwo.Optimal.normCut gap)
      (Dirichlet.Window.IndexTwo.Optimal.normCut gap) ≤
      Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap (Dirichlet.Window.IndexTwo.Optimal.normCut gap)
        (Dirichlet.Window.IndexTwo.Optimal.normCut gap) := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let lower := Dirichlet.Window.IndexTwo.Optimal.componentLower gap cut
  have squareNonnegative :
      0 ≤ 2 * (lower - (1 - cut) / 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ 2 * (lower - (1 - cut) / 2) ^ 2 := squareNonnegative
    _ = 2 * lower ^ 2 - 2 * lower * (1 - cut) +
        2 * ((1 - cut) / 2) ^ 2 := by
      have halfDouble : ((1 - cut) / 2) * 2 = 1 - cut :=
        Fraction.Field.div_mul_cancel_of_ne (1 - cut) 2
          (by decide)
      calc
        2 * (lower - (1 - cut) / 2) ^ 2 =
            2 * lower ^ 2 -
              2 * lower * (((1 - cut) / 2) * 2) +
              2 * ((1 - cut) / 2) ^ 2 := by ring1
        _ = 2 * lower ^ 2 - 2 * lower * (1 - cut) +
              2 * ((1 - cut) / 2) ^ 2 := by rw [halfDouble]
    _ = Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut cut -
      Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap cut cut := by
      unfold Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor
      dsimp only [lower]
      rw [← Dirichlet.Window.IndexTwo.Optimal.twice_half_mul_half (1 - cut) (1 - cut)]
      ring1

/-- The aligned floor exceeds the target determinant-gap excess above both centered norm cuts.

Each coordinate increment has a nonnegative coefficient, so the endpoint crossed-floor estimate extends in both norm
variables. -/
private theorem targetExcess_le_alignedFloor
    {gap firstNorm secondNorm : Fraction.Rational}
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (firstLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ firstNorm)
    (secondLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ secondNorm) :
    2 * gap - 1 ≤ Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap firstNorm secondNorm := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  let slope := Dirichlet.Window.IndexTwo.Optimal.componentSlope gap
  let factor := fun value : Fraction.Rational =>
    value + 2 * slope ^ 2 * (value + 1) - (1 - value) / 2
  have cutFactorNonnegative : 0 ≤ factor cut := by
    dsimp only [factor, slope, cut]
    exact Dirichlet.Window.IndexTwo.Optimal.cutFactor_nonnegative certificate
  have factorMonotone : ∀ value : Fraction.Rational, cut ≤ value →
      factor cut ≤ factor value := by
    intro value cutLe
    have offsetNonnegative : 0 ≤ value - cut :=
      Fraction.Order.Arithmetic.sub_nonneg_direct cutLe
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (value - cut) * (1 + 2 * slope ^ 2 + 1 / 2) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          (add_nonneg
            (add_nonneg (by decide)
              (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                (Fraction.Order.Arithmetic.sq_nonneg_direct slope)))
            (by decide))
      _ = factor value - factor cut := by
        dsimp only [factor]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - value),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - cut)]
        ring1
  have secondFactorNonnegative : 0 ≤ factor secondNorm :=
    cutFactorNonnegative.trans (factorMonotone secondNorm secondLower)
  have firstStep :
      Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut secondNorm ≤
        Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap firstNorm secondNorm := by
    have offsetNonnegative : 0 ≤ firstNorm - cut :=
      Fraction.Order.Arithmetic.sub_nonneg_direct firstLower
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (firstNorm - cut) * factor secondNorm :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          secondFactorNonnegative
      _ = Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap firstNorm secondNorm -
          Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut secondNorm := by
        unfold Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor Dirichlet.Window.IndexTwo.Optimal.componentLower
        dsimp only [factor, slope]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - firstNorm) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - cut) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - secondNorm)]
        ring1
  have secondStep :
      Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut cut ≤
        Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut secondNorm := by
    have offsetNonnegative : 0 ≤ secondNorm - cut :=
      Fraction.Order.Arithmetic.sub_nonneg_direct secondLower
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (secondNorm - cut) * factor cut :=
        Fraction.Order.Arithmetic.mul_nonneg_direct offsetNonnegative
          cutFactorNonnegative
      _ = Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut secondNorm -
          Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut cut := by
        unfold Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor Dirichlet.Window.IndexTwo.Optimal.componentLower
        dsimp only [factor, slope]
        rw [Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - cut) * (1 - secondNorm)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul
            ((1 - cut) * (1 - cut)),
          Dirichlet.Window.IndexTwo.Bounds.div_two_eq_half_mul (1 - cut)]
        ring1
  calc
    2 * gap - 1 ≤ Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap cut cut :=
      Dirichlet.Window.IndexTwo.Optimal.targetExcess_le_crossFloor certificate le_rfl le_rfl
    _ ≤ Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut cut :=
      Dirichlet.Window.IndexTwo.Optimal.crossFloor_cut_cut_le_alignedFloor_cut_cut
    _ ≤ Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap cut secondNorm := secondStep
    _ ≤ Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap firstNorm secondNorm := firstStep

/-- A norm below one satisfying the complementary-square bound lies above every certified centered cut.

A hypothetical smaller norm makes its norm polynomial positive, contradicting the supplied quadratic inequality. -/
private theorem normCut_le_of_normQuadratic
    {gap value : Fraction.Rational}
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (valueInside : value < 1)
    (quadraticBound : (1 - value) ^ 2 ≤ 2 * value) :
    Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ value := by
  let cut := Dirichlet.Window.IndexTwo.Optimal.normCut gap
  have cutLtOne : cut < (1 : Fraction.Rational) := Dirichlet.Window.IndexTwo.Optimal.normCut_lt_one certificate
  have cutPolynomialNonnegative : 0 ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_polynomial_nonnegative certificate
  by_cases cutLe : cut ≤ value
  · exact cutLe
  · have valueLtCut : value < cut :=
      Fraction.Order.Arithmetic.lt_of_not_ge_direct cutLe
    have valuePlusCutLtTwo : value + cut < (2 : Fraction.Rational) := by
      exact Fraction.Order.Arithmetic.add_lt_add_direct valueInside cutLtOne
    have valuePlusCutLtFour : value + cut < (4 : Fraction.Rational) :=
      valuePlusCutLtTwo.trans (by decide)
    have firstFactorPositive : (0 : Fraction.Rational) < cut - value :=
      Fraction.Order.Arithmetic.sub_pos_direct valueLtCut
    have secondFactorPositive :
        (0 : Fraction.Rational) < 4 - value - cut := by
      have identity : 4 - value - cut = 4 - (value + cut) := by ring1
      rw [identity]
      exact Fraction.Order.Arithmetic.sub_pos_direct valuePlusCutLtFour
    have productPositive :
        (0 : Fraction.Rational) < (cut - value) * (4 - value - cut) :=
      Fraction.Order.Arithmetic.mul_pos_direct firstFactorPositive
        secondFactorPositive
    have valuePolynomialPositive : 0 < Dirichlet.Window.IndexTwo.Optimal.normPolynomial value := by
      calc
        (0 : Fraction.Rational) = 0 + 0 := by ring1
        _ ≤ Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut + 0 :=
          Fraction.Order.Arithmetic.add_le_add_direct
            cutPolynomialNonnegative le_rfl
        _ < Dirichlet.Window.IndexTwo.Optimal.normPolynomial cut +
            (cut - value) * (4 - value - cut) :=
          Fraction.Order.Arithmetic.add_lt_add_left_direct productPositive _
        _ = Dirichlet.Window.IndexTwo.Optimal.normPolynomial value := by
          unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial
          ring1
    have differenceNonnegative :
        0 ≤ 2 * value - (1 - value) ^ 2 :=
      Fraction.Order.Arithmetic.sub_nonneg_direct quadraticBound
    have valuePolynomialNonpositive : Dirichlet.Window.IndexTwo.Optimal.normPolynomial value ≤ 0 := by
      calc
        Dirichlet.Window.IndexTwo.Optimal.normPolynomial value = -(2 * value - (1 - value) ^ 2) := by
          unfold Dirichlet.Window.IndexTwo.Optimal.normPolynomial
          ring1
        _ ≤ -0 :=
          Fraction.Order.Arithmetic.neg_le_neg_direct differenceNonnegative
        _ = 0 := by ring1
    exact (not_lt_of_ge valuePolynomialNonpositive
      valuePolynomialPositive).elim

/-- A doubled-coordinate projection inequality bounds half the complementary norm by that coordinate. -/
private theorem
  half_complement_le_of_projection
    (norm coordinate : Fraction.Rational)
    (projection : 1 - norm ≤ 2 * coordinate) :
    (1 - norm) / 2 ≤ coordinate := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      ((1 - norm) / 2) * 2 = 1 - norm :=
        Fraction.Field.div_mul_cancel_of_ne (1 - norm) 2
          (by decide)
      _ ≤ 2 * coordinate := projection
      _ = coordinate * 2 := by ring1
  · decide

/-- In a displayed first octant, every rational point of the exact centered
cut gives the determinant-gap family `2 * gap <= determinantGap`.  All
hypotheses and all intermediate bounds are rational coordinate inequalities. -/
theorem
  twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
    (gap : Fraction.Rational) (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (errorRatio denominatorRatio : Gaussian.Basic.Canonical)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : Data.Gaussian.Norm.Basic.normSq errorRatio < 1)
    (denominatorInside : Data.Gaussian.Norm.Basic.normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, GaussianInt.normNat unit = 1 →
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (errorRatio - GaussianInt.toGaussian unit) ∨
        2 ≤ Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian unit * denominatorRatio)) :
    2 * gap ≤ Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let u := -denominatorRatio.re
  let v := denominatorRatio.im
  let firstNorm := Data.Gaussian.Norm.Basic.normSq errorRatio
  let secondNorm := Data.Gaussian.Norm.Basic.normSq denominatorRatio
  let firstHalfGap := (1 - firstNorm) / 2
  let secondHalfGap := (1 - secondNorm) / 2
  obtain ⟨firstQuadratic, secondQuadratic⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.complement_sq_le_two_norms_of_centeredUnitObstructions
      errorRatio denominatorRatio errorInside denominatorInside obstruction
  have firstNormLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ firstNorm :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_le_of_normQuadratic certificate errorInside firstQuadratic
  have secondNormLower : Dirichlet.Window.IndexTwo.Optimal.normCut gap ≤ secondNorm :=
    Dirichlet.Window.IndexTwo.Optimal.normCut_le_of_normQuadratic certificate denominatorInside secondQuadratic
  obtain ⟨bProjection, uProjectionRaw, vProjection⟩ :=
    Dirichlet.Window.IndexTwo.Bounds.firstOctant_projectionBounds_of_centeredUnitObstructions
      errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      errorInside denominatorInside obstruction
  have firstNormLeOne : firstNorm ≤ (1 : Fraction.Rational) := errorInside.le
  have secondNormLeOne : secondNorm ≤ (1 : Fraction.Rational) :=
    denominatorInside.le
  have firstNormNonnegative : (0 : Fraction.Rational) ≤ firstNorm :=
    Gaussian.Norm.Basic.normSq_nonneg errorRatio
  have secondNormNonnegative : (0 : Fraction.Rational) ≤ secondNorm :=
    Gaussian.Norm.Basic.normSq_nonneg denominatorRatio
  have firstHalfGapNonnegative : (0 : Fraction.Rational) ≤ firstHalfGap := by
    dsimp only [firstHalfGap]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sub_nonneg_direct firstNormLeOne)
      (by decide)
  have secondHalfGapNonnegative : (0 : Fraction.Rational) ≤ secondHalfGap := by
    dsimp only [secondHalfGap]
    exact Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sub_nonneg_direct secondNormLeOne)
      (by decide)
  have bLower : firstHalfGap ≤ b := by
    dsimp only [firstHalfGap, firstNorm, b]
    exact Dirichlet.Window.IndexTwo.Optimal.half_complement_le_of_projection _ _ bProjection
  have uProjection : 1 - secondNorm ≤ 2 * u := by
    dsimp only [secondNorm, u]
    calc
      1 - Data.Gaussian.Norm.Basic.normSq denominatorRatio ≤ -2 * denominatorRatio.re :=
        uProjectionRaw
      _ = 2 * (-denominatorRatio.re) := by ring1
  have uLower : secondHalfGap ≤ u := by
    dsimp only [secondHalfGap]
    exact Dirichlet.Window.IndexTwo.Optimal.half_complement_le_of_projection secondNorm u uProjection
  have vLower : secondHalfGap ≤ v := by
    dsimp only [secondHalfGap, secondNorm, v]
    exact Dirichlet.Window.IndexTwo.Optimal.half_complement_le_of_projection _ _ vProjection
  have uNonnegative : (0 : Fraction.Rational) ≤ u :=
    secondHalfGapNonnegative.trans uLower
  have vNonnegative : (0 : Fraction.Rational) ≤ v :=
    secondHalfGapNonnegative.trans vLower
  have firstNormIdentity : firstNorm = a ^ 2 + b ^ 2 := by
    dsimp only [firstNorm, a, b, Data.Gaussian.Norm.Basic.normSq]
  have secondNormIdentity : secondNorm = u ^ 2 + v ^ 2 := by
    dsimp only [secondNorm, u, v, Data.Gaussian.Norm.Basic.normSq]
    ring1
  have firstComponentLower : Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm ≤ a :=
    Dirichlet.Window.IndexTwo.Optimal.componentLower_le_largerCoordinate
      (gap := gap) (large := a) (small := b) (norm := firstNorm) certificate
      realNonnegative imaginaryNonnegative imaginaryLeReal firstNormIdentity
      firstNormLower firstNormLeOne
  have secondAffineNonnegative :
      (0 : Fraction.Rational) ≤ Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm :=
    Dirichlet.Window.IndexTwo.Optimal.componentLower_nonnegative certificate secondNormNonnegative
  have excessLeCore :
      2 * gap - 1 ≤ firstNorm * secondNorm + 2 * (a * u + b * v) := by
    by_cases uLeV : u ≤ v
    · have secondComponentLower : Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm ≤ v :=
        Dirichlet.Window.IndexTwo.Optimal.componentLower_le_largerCoordinate
          (gap := gap) (large := v) (small := u) (norm := secondNorm)
          certificate
          vNonnegative uNonnegative uLeV (by
            rw [secondNormIdentity]
            ring1)
          secondNormLower secondNormLeOne
      have firstProductLower :
          Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm * secondHalfGap ≤ a * u :=
        Fraction.Order.Arithmetic.mul_le_mul_direct firstComponentLower
          uLower secondHalfGapNonnegative realNonnegative
      have secondProductLower :
          firstHalfGap * Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm ≤ b * v :=
        Fraction.Order.Arithmetic.mul_le_mul_direct bLower
          secondComponentLower secondAffineNonnegative imaginaryNonnegative
      have productSumLower :
          Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm * secondHalfGap +
              firstHalfGap * Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm ≤ a * u + b * v :=
        Fraction.Order.Arithmetic.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        2 * gap - 1 ≤ Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor gap firstNorm secondNorm :=
          Dirichlet.Window.IndexTwo.Optimal.targetExcess_le_crossFloor certificate firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm * secondHalfGap +
              firstHalfGap * Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm) := by
          have firstDouble : secondHalfGap * 2 = 1 - secondNorm := by
            dsimp only [secondHalfGap]
            exact Fraction.Field.div_mul_cancel_of_ne
              (1 - secondNorm) 2 (by decide)
          have secondDouble : firstHalfGap * 2 = 1 - firstNorm := by
            dsimp only [firstHalfGap]
            exact Fraction.Field.div_mul_cancel_of_ne
              (1 - firstNorm) 2 (by decide)
          unfold Dirichlet.Window.IndexTwo.Optimal.crossExcessFloor
          rw [← firstDouble, ← secondDouble]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            twiceProductSumLower
    · have vLeU : v ≤ u := le_of_not_ge uLeV
      have secondComponentLower : Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm ≤ u :=
        Dirichlet.Window.IndexTwo.Optimal.componentLower_le_largerCoordinate
          (gap := gap) (large := u) (small := v) (norm := secondNorm)
          certificate
          uNonnegative vNonnegative vLeU secondNormIdentity secondNormLower
          secondNormLeOne
      have firstProductLower :
          Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm *
            Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm ≤
            a * u :=
        Fraction.Order.Arithmetic.mul_le_mul_direct firstComponentLower
          secondComponentLower secondAffineNonnegative realNonnegative
      have secondProductLower : firstHalfGap * secondHalfGap ≤ b * v :=
        Fraction.Order.Arithmetic.mul_le_mul_direct bLower vLower
          secondHalfGapNonnegative imaginaryNonnegative
      have productSumLower :
          Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm *
            Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm +
              firstHalfGap * secondHalfGap ≤ a * u + b * v :=
        Fraction.Order.Arithmetic.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Fraction.Rational) ≤ 2 by decide)
      calc
        2 * gap - 1 ≤ Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor gap firstNorm secondNorm :=
          Dirichlet.Window.IndexTwo.Optimal.targetExcess_le_alignedFloor certificate firstNormLower
            secondNormLower
        _ = firstNorm * secondNorm +
            2 * (Dirichlet.Window.IndexTwo.Optimal.componentLower gap firstNorm *
                Dirichlet.Window.IndexTwo.Optimal.componentLower gap secondNorm +
              firstHalfGap * secondHalfGap) := by
          unfold Dirichlet.Window.IndexTwo.Optimal.alignedExcessFloor
          rw [← Dirichlet.Window.IndexTwo.Optimal.twice_half_mul_half (1 - firstNorm) (1 - secondNorm)]
          dsimp only [firstHalfGap, secondHalfGap]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            twiceProductSumLower
  calc
    2 * gap = 1 + (2 * gap - 1) := by ring1
    _ ≤ 1 + (firstNorm * secondNorm + 2 * (a * u + b * v)) :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl excessLeCore
    _ = Data.Gaussian.Norm.Basic.normSq (1 - denominatorRatio * errorRatio) := by
      dsimp only [firstNorm, secondNorm, a, b, u, v, Data.Gaussian.Norm.Basic.normSq]
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im]
      ring1

end Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal

end
