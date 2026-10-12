module
import Purelib.Data.Rat.Fraction.Cast

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Ring.IntCast
public import Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Digits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.GaussianInt.Constants
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Square
public import Purelib.Geometry.Region.Gaussian.UnitSquare
import Purelib.Polynomial.Multivariate.Rational.QuadraticBox

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Group.Int.Defs

import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.QuotientFreeOmega

/-!
# Finite exceptional-digit contraction table

The original eight-by-eight digit enumeration retains its integer coefficient
table and exact decision procedure. Scalar cast certificates transport those
same original inequalities to the Gaussian norm difference.
-/

namespace Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Table

open Purelib
open Purelib.Algebra
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction.CoordinateFloor
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Region

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- The piecewise digit lower bound bounds every translate of a unit-square point when the digit real coordinate is
nonnegative.

The original nonnegative real digit coordinate and the half-open square
conditions bound the retained translation coordinates without changing the digit. -/
public theorem lambda_le_norm_translate (t : Data.GaussianInt) (realNonnegative : 0 ≤ t.re)
    (q : Basic.Canonical) (inside : Gaussian.UnitSquare.Sq q) :
    (Contraction.Digits.lambda t : Fraction.Rational) ≤ Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t + q) := by
  rcases inside with ⟨realQNonnegative, realQSmall,
    imagQNonnegative, imagQSmall⟩
  have realCastNonnegative : (0 : Fraction.Rational) ≤ (t.re : Fraction.Rational) :=
    Fraction.Cast.Order.cast_int_nonnegative realNonnegative
  have realGrowth := Fraction.Order.Square.square_le_square_add_of_nonnegative
    (t.re : Fraction.Rational) q.re realCastNonnegative realQNonnegative
  by_cases imagNonnegative : 0 ≤ t.im
  · have imagCastNonnegative : (0 : Fraction.Rational) ≤ (t.im : Fraction.Rational) :=
      Fraction.Cast.Order.cast_int_nonnegative imagNonnegative
    have imagGrowth := Fraction.Order.Square.square_le_square_add_of_nonnegative
      (t.im : Fraction.Rational) q.im imagCastNonnegative imagQNonnegative
    simp only [Contraction.Digits.lambda, if_pos imagNonnegative, Gaussian.Norm.Basic.normSq,
      Basic.add_re,
      Basic.add_im, GaussianInt.toGaussian,
      Ring.IntCast.add, Ring.IntCast.intCast_pow, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    exact Fraction.Order.Arithmetic.add_le_add_direct realGrowth imagGrowth
  · by_cases imagNegOne : t.im = -1
    · simp only [Contraction.Digits.lambda, if_neg imagNonnegative, if_pos imagNegOne,
        Gaussian.Norm.Basic.normSq, Basic.add_re,
        Basic.add_im, GaussianInt.toGaussian,
        Ring.IntCast.intCast_pow, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      exact realGrowth.trans
        (by
          have bound := Fraction.Order.Arithmetic.add_le_add_direct
            (show ((t.re : Fraction.Rational) + q.re) ^ 2 ≤
              ((t.re : Fraction.Rational) + q.re) ^ 2 from Fraction.Order.Basic.le_refl _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct ((t.im : Fraction.Rational) + q.im))
          calc
            ((t.re : Fraction.Rational) + q.re) ^ 2 =
                ((t.re : Fraction.Rational) + q.re) ^ 2 + 0 :=
              (_root_.add_zero _).symm
            _ ≤ ((t.re : Fraction.Rational) + q.re) ^ 2 +
                ((t.im : Fraction.Rational) + q.im) ^ 2 := bound)
    · have imagNegative : t.im < 0 := Int.Order.lt_of_not_le imagNonnegative
      have imagAtMostNegOne : t.im ≤ (-1 : Int) := by
        change t.im ≤ (0 : Int) - 1
        omega0
      have imagPlusOneNonpositive : t.im + 1 ≤ 0 := by
        calc
          t.im + 1 ≤ (-1 : Int) + 1 :=
            Int.Order.add_le_add imagAtMostNegOne (Int.Order.le_refl 1)
          _ = 0 := by ring1
      have basePlusOneNonpositive : (t.im : Fraction.Rational) + 1 ≤ 0 := by
        have castOrder :=
          (Fraction.Cast.Order.intCast_le_intCast_iff_direct
            (t.im + 1) 0).2 imagPlusOneNonpositive
        simpa only [Ring.IntCast.add, Int.cast_one, Ring.IntCast.cast_zero] using castOrder
      have imagGrowth := Fraction.Order.Square.negative_square_growth
        (t.im : Fraction.Rational) q.im imagQSmall.le basePlusOneNonpositive
      simp only [Contraction.Digits.lambda, if_neg imagNonnegative, if_neg imagNegOne,
        Gaussian.Norm.Basic.normSq, Basic.add_re,
        Basic.add_im, GaussianInt.toGaussian,
        Ring.IntCast.add, Int.cast_one, Ring.IntCast.intCast_pow, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      exact Fraction.Order.Arithmetic.add_le_add_direct realGrowth imagGrowth

/-- Compute the product of the two retained integer digits plus integer gamma.

Both original digits and integer gamma remain the exact owners of the
computed Gaussian integer product and sum. -/
@[expose] public def center (t t' : Data.GaussianInt) : Data.GaussianInt :=
  t * t' + GaussianInt.gammaInt

/-- Compute the first digit's integer squared norm minus four.

The original digit norm supplies the retained quadratic radial coefficient
through the exact integer subtraction of four. -/
@[expose] public def alpha (t : Data.GaussianInt) : Int :=
  GaussianInt.normInt t - 4

/-- Compute twice the real dot product of the first digit with the retained center.

Both coordinates of the original first digit and its retained center
contribute to the same scalar real dot product. -/
@[expose] public def beta (t t' : Data.GaussianInt) : Int :=
  2 * (t.re * (center t t').re + t.im * (center t t').im)

/-- Compute twice the imaginary cross-coordinate coefficient of the first digit and retained center.

Both signed coordinates of the original first digit and its retained center
contribute to the same scalar imaginary cross product. -/
@[expose] public def eta (t t' : Data.GaussianInt) : Int :=
  2 * (-t.im * (center t t').re + t.re * (center t t').im)

/-- Compute the integer squared norm of the retained center.

The original center retains the two digit owners and integer gamma; its
exact squared norm supplies the constant coefficient. -/
@[expose] public def kappa (t t' : Data.GaussianInt) : Int :=
  GaussianInt.normInt (center t t')

/-- Compute the translated product norm minus four times the remainder norm.

The translated product uses both retained integer digits and canonical gamma. Its exact coordinate expansion determines
the finite positivity certificate. -/
@[expose] public def delta (t t' : Data.GaussianInt) (w : Basic.Canonical) : Fraction.Rational :=
  Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t * (GaussianInt.toGaussian t' + w) + Basic.Canonical.gamma) - 4 *
    Gaussian.Norm.Basic.normSq w

/-- The norm difference equals the quadratic coordinate polynomial with the retained alpha, beta, eta and kappa
coefficients.

The original digit coordinates, retained center and Gaussian remainder
determine this exact scalar norm expansion through their integer cast laws. -/
public theorem delta_expansion (t t' : Data.GaussianInt) (w : Basic.Canonical) :
    delta t t' w =
      (alpha t : Fraction.Rational) * (w.re ^ 2 + w.im ^ 2) +
        (beta t t' : Fraction.Rational) * w.re +
        (eta t t' : Fraction.Rational) * w.im +
        (kappa t t' : Fraction.Rational) := by
  have oneCast : ((1 : Int) : Fraction.Rational) = 1 := by rfl
  have twoCast : ((2 : Int) : Fraction.Rational) = 2 := by rfl
  have fourCast : ((4 : Int) : Fraction.Rational) = 4 := by rfl
  have imagNegationCast : ((-t.im : Int) : Fraction.Rational) =
      -(t.im : Fraction.Rational) := by
    change ((Int.neg t.im : Int) : Fraction.Rational) = _
    exact Ring.IntCast.neg t.im
  simp only [delta, alpha, beta, eta,
    kappa, center,
    GaussianInt.normInt,
    Gaussian.Norm.Basic.normSq,
    Basic.mul_re,
    Basic.mul_im,
    Basic.add_re,
    Basic.add_im,
    Basic.Canonical.gamma,
    Basic.Canonical.gamma,
    GaussianInt.toGaussian,
    GaussianInt.mul_re,
    GaussianInt.mul_im,
    GaussianInt.add_re,
    GaussianInt.add_im,
    GaussianInt.gammaInt,
    Ring.IntCast.sub, Ring.IntCast.add, Ring.IntCast.intCast_mul, imagNegationCast,
    oneCast, twoCast, fourCast, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  ring1

/-- Require the exact integer coefficient inequalities proving positivity for a pair of exceptional digits.

A nonpositive quadratic coefficient uses four corner bounds. A positive coefficient uses nonnegative real slope and one
of the three retained imaginary-slope and endpoint conditions. -/
@[expose] public def TableCertificate (r c : Contraction.Digits.SmallDigit) : Prop :=
  let t := Contraction.Digits.tau r
  let t' := Contraction.Digits.tau c
  let A := alpha t
  let B := beta t t'
  let C := eta t t'
  let D := kappa t t'
  if A ≤ 0 then
    0 < D ∧ 0 ≤ A + B + D ∧ 0 ≤ A + C + D ∧
      0 ≤ 2 * A + B + C + D
  else
    0 ≤ B ∧
      ((0 ≤ C ∧ 0 < D) ∨
        ((2 * A + C ≤ 0 ∧ 0 < A + C + D) ∨
          (2 * A + C < 0 ∧ 0 ≤ A + C + D)))

/-- Decide the finite coefficient certificate using its explicit integer inequalities.

The original conditional certificate is reduced to the same retained
integer comparison decisions, preserving its exact proof-bearing record. -/
public instance tableCertificateDecidable (r c : Contraction.Digits.SmallDigit) :
    Decidable (TableCertificate r c) := by
  unfold TableCertificate
  infer_instance

/-- Every exceptional digit pair with lower-bound product below eight, apart from the excluded crossing, satisfies the
finite coefficient certificate.

The original eight-by-eight digit table is checked against its exact
integer inequalities; the retained crossing exclusion and bound remain unchanged. -/
public theorem table_certificate (r c : Contraction.Digits.SmallDigit) :
    Contraction.Digits.lambda (Contraction.Digits.tau r) * Contraction.Digits.lambda (Contraction.Digits.tau c) < 8 →
      ¬ (r = .d1 ∧ c = .d0) → TableCertificate r c := by
  cases r <;> cases c <;> decide

/-- A certified exceptional digit pair has positive norm difference throughout the half-open unit square.

The lower-bound product is below eight and the excluded crossing is absent. The retained integer certificate is
transported to the exact rational quadratic-box positivity theorem. -/
public theorem delta_pos_of_small (r c : Contraction.Digits.SmallDigit) (w : Basic.Canonical)
    (inside : Gaussian.UnitSquare.Sq w)
    (productSmall : Contraction.Digits.lambda (Contraction.Digits.tau r) * Contraction.Digits.lambda
      (Contraction.Digits.tau c) < 8)
    (notCrossed : ¬ (r = .d1 ∧ c = .d0)) :
    0 < delta (Contraction.Digits.tau r) (Contraction.Digits.tau c) w := by
  rcases inside with ⟨realNonnegative, realSmall,
    imagNonnegative, imagSmall⟩
  have certificate := table_certificate r c productSmall notCrossed
  rw [delta_expansion]
  change 0 < Polynomial.Multivariate.Rational.QuadraticBox.tablePolynomial
    (alpha (Contraction.Digits.tau r) : Fraction.Rational)
    (beta (Contraction.Digits.tau r) (Contraction.Digits.tau c) : Fraction.Rational)
    (eta (Contraction.Digits.tau r) (Contraction.Digits.tau c) : Fraction.Rational)
    (kappa (Contraction.Digits.tau r) (Contraction.Digits.tau c) : Fraction.Rational) w.re w.im
  unfold TableCertificate at certificate
  dsimp only at certificate
  split at certificate
  · rename_i alphaNonpositive
    rcases certificate with ⟨originPositive, realCorner,
      imagCorner, farCorner⟩
    apply Polynomial.Multivariate.Rational.QuadraticBox.concave_table_positive
      (Fraction.Cast.Order.cast_int_nonpositive alphaNonpositive)
      (Fraction.Cast.Order.cast_int_positive originPositive)
      (by simpa only [Ring.IntCast.add] using Fraction.Cast.Order.cast_int_nonnegative realCorner)
      (by simpa only [Ring.IntCast.add] using Fraction.Cast.Order.cast_int_nonnegative imagCorner)
      (by
          simpa only [Ring.IntCast.add, Ring.IntCast.intCast_mul, Int.cast_ofNat]
            using Fraction.Cast.Order.cast_int_nonnegative farCorner)
      realNonnegative realSmall imagNonnegative imagSmall
  · rename_i alphaNotNonpositive
    have alphaPositive : 0 < alpha (Contraction.Digits.tau r) :=
      Int.Order.lt_of_not_le alphaNotNonpositive
    rcases certificate with ⟨betaNonnegative,
      ⟨etaUp, originPositive⟩ | down⟩
    · apply Polynomial.Multivariate.Rational.QuadraticBox.convex_table_positive_up
        (Fraction.Cast.Order.cast_int_positive alphaPositive)
        (Fraction.Cast.Order.cast_int_nonnegative betaNonnegative)
        (Fraction.Cast.Order.cast_int_nonnegative etaUp)
        (Fraction.Cast.Order.cast_int_positive originPositive)
        realNonnegative imagNonnegative
    · rcases down with downCorner | downSlope
      · apply Polynomial.Multivariate.Rational.QuadraticBox.convex_table_positive_down_corner
          (Fraction.Cast.Order.cast_int_positive alphaPositive)
          (Fraction.Cast.Order.cast_int_nonnegative betaNonnegative)
          (by
              simpa only [Ring.IntCast.add, Ring.IntCast.intCast_mul, Int.cast_ofNat]
                using Fraction.Cast.Order.cast_int_nonpositive downCorner.1)
          (by
              simpa only [Ring.IntCast.add]
                using Fraction.Cast.Order.cast_int_positive downCorner.2)
          realNonnegative imagSmall
      · apply Polynomial.Multivariate.Rational.QuadraticBox.convex_table_positive_down_slope
          (Fraction.Cast.Order.cast_int_positive alphaPositive)
          (Fraction.Cast.Order.cast_int_nonnegative betaNonnegative)
          (by
              simpa only [Ring.IntCast.add, Ring.IntCast.intCast_mul, Int.cast_ofNat]
                using Fraction.Cast.Order.cast_int_negative downSlope.1)
          (by
              simpa only [Ring.IntCast.add]
                using Fraction.Cast.Order.cast_int_nonnegative downSlope.2)
          realNonnegative imagSmall

end Purelib.Data.ComplexContinuedFraction.CoordinateFloor.Contraction.Table
