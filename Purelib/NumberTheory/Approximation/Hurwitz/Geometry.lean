module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.List.Membership
import Purelib.Data.Int.Order
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Trace
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Finite geometry for Hurwitz approximation

This module contains the square-root-free geometric facts used in the
finite Lakein comparison.  They are kept separate from the trace algebra so
that every appeal to the Hurwitz fundamental square is explicit.
-/

namespace Purelib.NumberTheory.Approximation.Hurwitz.Geometry

/-- A residual in the selected half-open square is no nearer to the inverse
of a Gaussian unit than it is to zero.  This is Lakein's elementary unit
exterior law with no square roots. -/
theorem residual_normSq_le_unit_mul_sub_one (fraction : GaussianInt.Fraction)
    {unit : GaussianInt} (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit) :
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual fraction
        - 1) := by
  have square := GaussianInt.Nearest.remainder_mem fraction.value
  rcases unitProperty with positive | negative |
      positiveImaginary | negativeImaginary
  · rw [positive, GaussianInt.toGaussian_one,
      _root_.one_mul]
    have gap : 0 ≤ 1 - 2 * (GaussianInt.Division.Nearest.residual fraction).re :=
      Fraction.Order.Arithmetic.sub_nonneg_direct
        (Fraction.Order.Arithmetic.twice_le_one_of_lt_half square.2.1)
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) +
            (1 - 2 * (GaussianInt.Division.Nearest.residual fraction).re) :=
        (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
          (show a ≤ a + b from by
            simpa only [add_zero, -eq_self, -iff_self] using
              Fraction.Order.Arithmetic.add_le_add_direct
                (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction - 1) := by
        simp only [Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        ring1
  · rw [negative, GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one]
    have gap : 0 ≤ 1 + 2 * (GaussianInt.Division.Nearest.residual fraction).re := by
      have lower := Fraction.Order.Arithmetic.neg_one_le_twice_of_neg_half_le square.1
      have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
        lower 1
      calc
        0 = (-1 : Fraction.Rational) + 1 := by ring1
        _ ≤ 2 * (GaussianInt.Division.Nearest.residual fraction).re + 1 := translated
        _ = 1 + 2 * (GaussianInt.Division.Nearest.residual fraction).re := by ring1
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) +
            (1 + 2 * (GaussianInt.Division.Nearest.residual fraction).re) :=
        (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
          (show a ≤ a + b from by
            simpa only [add_zero, -eq_self, -iff_self] using
              Fraction.Order.Arithmetic.add_le_add_direct
                (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (-1 * GaussianInt.Division.Nearest.residual fraction - 1) := by
        simp only [Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        ring1
  · rw [positiveImaginary]
    have gap : 0 ≤ 1 + 2 * (GaussianInt.Division.Nearest.residual fraction).im := by
      have lower := Fraction.Order.Arithmetic.neg_one_le_twice_of_neg_half_le square.2.2.1
      have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
        lower 1
      calc
        0 = (-1 : Fraction.Rational) + 1 := by ring1
        _ ≤ 2 * (GaussianInt.Division.Nearest.residual fraction).im + 1 := translated
        _ = 1 + 2 * (GaussianInt.Division.Nearest.residual fraction).im := by ring1
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) +
            (1 + 2 * (GaussianInt.Division.Nearest.residual fraction).im) :=
        (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
          (show a ≤ a + b from by
            simpa only [add_zero, -eq_self, -iff_self] using
              Fraction.Order.Arithmetic.add_le_add_direct
                (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * GaussianInt.Division.Nearest.residual fraction
            - 1) := by
        simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im,
          Algebra.Ring.IntCast.cast_zero, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · rw [negativeImaginary, GaussianInt.toGaussian_neg]
    have gap : 0 ≤ 1 - 2 * (GaussianInt.Division.Nearest.residual fraction).im :=
      Fraction.Order.Arithmetic.sub_nonneg_direct
        (Fraction.Order.Arithmetic.twice_le_one_of_lt_half square.2.2.2)
    calc
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) +
            (1 - 2 * (GaussianInt.Division.Nearest.residual fraction).im) :=
        (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
          (show a ≤ a + b from by
            simpa only [add_zero, -eq_self, -iff_self] using
              Fraction.Order.Arithmetic.add_le_add_direct
                (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq
          (-GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * GaussianInt.Division.Nearest.residual fraction
            - 1) := by
        simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.neg_re,
          Gaussian.Basic.neg_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im,
          Algebra.Ring.IntCast.cast_zero, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1

/-- Every next complete quotient lies in the closed exterior of the unit
disc about each Gaussian unit. -/
theorem one_le_next_sub_unit_normSq (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) {unit : GaussianInt}
    (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value - GaussianInt.toGaussian unit) := by
  have residualNonzero := GaussianInt.Division.Nearest.residual_ne_zero nonterminal
  have residualNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction)
    :=
    Gaussian.Norm.Basic.normSq_pos residualNonzero
  have reciprocal :
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
        GaussianInt.Division.Nearest.residual fraction = 1 := by
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ residualNonzero]
  have factorIdentity :
      ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian unit) *
          GaussianInt.Division.Nearest.residual fraction =
        -(GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual fraction - 1) := by
    calc
      ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian unit) *
            GaussianInt.Division.Nearest.residual fraction =
          (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
            GaussianInt.Division.Nearest.residual fraction -
            GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual fraction := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = 1 - GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual fraction := by rw [reciprocal]
      _ = -(GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual fraction - 1) := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.neg_re,
            Gaussian.Basic.neg_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
  have productExterior :
      1 * Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) ≤
        Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
          nonterminal).value - GaussianInt.toGaussian unit) *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := by
    calc
      1 * Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := by ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit * GaussianInt.Division.Nearest.residual
        fraction - 1) :=
        residual_normSq_le_unit_mul_sub_one fraction unitProperty
      _ = Data.Gaussian.Norm.Basic.normSq
          (((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian unit)
            *
            GaussianInt.Division.Nearest.residual fraction) := by
        rw [factorIdentity, Gaussian.Norm.Basic.normSq_neg]
      _ = Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value - GaussianInt.toGaussian unit) *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) :=
            Gaussian.Norm.Basic.normSq_mul _ _
  exact Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    productExterior residualNormPositive

/-- A strict corner approach by the next complete quotient becomes the
corresponding strict corner approach by the current residual. -/
theorem residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    {corner : GaussianInt} (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner)
    (nextCloser :
      Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
        - GaussianInt.toGaussian corner) < 1) :
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction + GaussianInt.toGaussian
      (GaussianInt.Norm.Small.cornerTurn corner)) < 1 := by
  have residualNonzero := GaussianInt.Division.Nearest.residual_ne_zero nonterminal
  have residualPositive : 0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) :=
    Gaussian.Norm.Basic.normSq_pos residualNonzero
  have reciprocal :
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
        GaussianInt.Division.Nearest.residual fraction = 1 := by
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ residualNonzero]
  have factorIdentity :
      ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian corner) *
          GaussianInt.Division.Nearest.residual fraction =
        1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual fraction := by
    calc
      ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian corner) *
            GaussianInt.Division.Nearest.residual fraction =
          (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
            GaussianInt.Division.Nearest.residual fraction -
            GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual fraction := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = 1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual fraction := by rw [reciprocal]
  have scaledCloser :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      nextCloser residualPositive
  have transformedCloser :
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual
        fraction) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := by
    calc
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual
        fraction) =
          Data.Gaussian.Norm.Basic.normSq
            (((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value - GaussianInt.toGaussian
              corner) *
              GaussianInt.Division.Nearest.residual fraction) := by rw [factorIdentity]
      _ = Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value - GaussianInt.toGaussian corner) *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) :=
            Gaussian.Norm.Basic.normSq_mul _ _
      _ < 1 * Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := scaledCloser
      _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := by ring1
  have differenceIdentity :
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual
        fraction) -
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction + GaussianInt.toGaussian
          (GaussianInt.Norm.Small.cornerTurn corner)) - 1 := by
    rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
      simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
        Data.Gaussian.Norm.Basic.normSq,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Gaussian.Basic.one_re,
        Gaussian.Basic.one_im,
        GaussianInt.neg_re,
        GaussianInt.neg_im,
        Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
      ring1
  have negativeDifference :
      Data.Gaussian.Norm.Basic.normSq (1 - GaussianInt.toGaussian corner * GaussianInt.Division.Nearest.residual
        fraction) -
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct transformedCloser
  rw [differenceIdentity] at negativeDifference
  exact Fraction.Order.Arithmetic.lt_of_sub_neg_direct negativeDifference

/-- The two discs used in one backward Lakein step have the same signed
quadrance difference. -/
theorem corner_norm_difference_identity {corner : GaussianInt}
    (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner) (value base : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq value - Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian corner *
      value + base) =
      Data.Gaussian.Norm.Basic.normSq base -
        Data.Gaussian.Norm.Basic.normSq (value - GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner) *
          base) := by
  rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
    simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
      Data.Gaussian.Norm.Basic.normSq,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] <;>
    ring1

/-- A corner non-growth condition for `a q + q₋` is equivalently a unit
disc condition for `(a-cornerTurn s) q + q₋`. -/
theorem corner_combination_norm_le_iff {corner : GaussianInt}
    (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner)
    (coefficient current previous : GaussianInt) :
    GaussianInt.normNat
          (corner * (coefficient * current + previous) + current) ≤
        GaussianInt.normNat (coefficient * current + previous) ↔
      GaussianInt.normNat
          ((coefficient - GaussianInt.Norm.Small.cornerTurn corner) * current + previous) ≤
        GaussianInt.normNat current := by
  have transformedIdentity :
      GaussianInt.toGaussian ((coefficient - GaussianInt.Norm.Small.cornerTurn corner) * current + previous) =
        GaussianInt.toGaussian (coefficient * current + previous) -
          GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner) * GaussianInt.toGaussian current := by
    simp only [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_sub]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  have cornerIdentity :
      GaussianInt.toGaussian
          (corner * (coefficient * current + previous) + current) =
        GaussianInt.toGaussian corner *
            GaussianInt.toGaussian (coefficient * current + previous) +
          GaussianInt.toGaussian current := by
    rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  have differenceIdentity := corner_norm_difference_identity
    cornerDiagonal (GaussianInt.toGaussian (coefficient * current + previous))
      (GaussianInt.toGaussian current)
  rw [← cornerIdentity, ← transformedIdentity,
    GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian,
    GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian] at differenceIdentity
  constructor
  · intro original
    have originalCast := Fraction.Cast.Order.natCast_le_direct original
    have originalGap :
        0 ≤
          (GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) -
            (GaussianInt.normNat
              (corner * (coefficient * current + previous) + current) :
                Fraction.Rational) :=
      Fraction.Order.Arithmetic.sub_nonneg_direct originalCast
    rw [differenceIdentity] at originalGap
    exact (Fraction.Cast.Order.natCast_le_iff_direct).1
      (Fraction.Order.Arithmetic.le_of_sub_nonneg_direct originalGap)
  · intro transformed
    have transformedCast := Fraction.Cast.Order.natCast_le_direct transformed
    have transformedGap :
        0 ≤ (GaussianInt.normNat current : Fraction.Rational) -
          (GaussianInt.normNat
            ((coefficient - GaussianInt.Norm.Small.cornerTurn corner) * current + previous) :
              Fraction.Rational) :=
      Fraction.Order.Arithmetic.sub_nonneg_direct transformedCast
    rw [← differenceIdentity] at transformedGap
    exact (Fraction.Cast.Order.natCast_le_iff_direct).1
      (Fraction.Order.Arithmetic.le_of_sub_nonneg_direct transformedGap)

/-- The finite corner calculation which rules out every diagonal difference
except the one continuing the backward succession. -/
theorem diagonal_eq_cornerTurn_of_local_geometry
    (rho : Gaussian.Basic.Canonical) (rhoSquare : GaussianInt.Nearest.InFundamentalSquare rho)
    (rhoNorm : Data.Gaussian.Norm.Basic.normSq rho ≤ 1 / 2)
    {corner difference : GaussianInt}
    (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner)
    (differenceDiagonal : GaussianInt.Norm.Small.IsDiagonal difference)
    (cornerApproach :
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner)) < 1)
    (completeLower :
      2 ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn
        corner) + rho))
    (unitExterior : ∀ unit, GaussianInt.Norm.Small.IsGaussianUnit unit →
      1 ≤ Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn corner) + rho -
          GaussianInt.toGaussian unit)) :
    difference = GaussianInt.Norm.Small.cornerTurn corner := by
  have zeroImpossible
      (sumZero : difference + GaussianInt.Norm.Small.cornerTurn corner = 0) : False := by
    have lower : 2 ≤ Data.Gaussian.Norm.Basic.normSq rho := by
      calc
        2 ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn
          corner) + rho) :=
          completeLower
        _ = Data.Gaussian.Norm.Basic.normSq rho := by
          rw [sumZero, GaussianInt.toGaussian_zero,
            Gaussian.Basic.zero_add]
    exact (not_lt_of_ge lower
      (rhoNorm.trans_lt (show (1 / 2 : Fraction.Rational) < 2 by decide)))
  have unitImpossible (unit : GaussianInt)
      (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit)
      (sumTwice : difference + GaussianInt.Norm.Small.cornerTurn corner = unit + unit)
      (comparison :
        Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian unit) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner)))
            : False := by
    have exterior := unitExterior unit unitProperty
    have valueDifference :
        GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn corner) + rho - GaussianInt.toGaussian
          unit =
          rho + GaussianInt.toGaussian unit := by
      rw [sumTwice, GaussianInt.toGaussian_add]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im] <;>
        ring1

    rw [valueDifference] at exterior
    exact (not_lt_of_ge exterior (comparison.trans_lt cornerApproach))
  rcases cornerDiagonal with rfl | rfl | rfl | rfl <;>
    rcases differenceDiagonal with rfl | rfl | rfl | rfl
  · apply False.elim
    apply (unitImpossible GaussianInt.Norm.Small.imaginaryUnit
      GaussianInt.Norm.Small.imaginaryUnit_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_sub_twice_nonneg_of_lt_half rhoSquare.2.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) +
            (1 - 2 * rho.re) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨1, 1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate,
          GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          Int.cast_one, Algebra.Ring.IntCast.cast_zero, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · rfl
  · apply False.elim
    apply (unitImpossible (-1) GaussianInt.Norm.Small.negOne_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_add_twice_nonneg_of_neg_half_le rhoSquare.2.2.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-1)) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-1)) +
            (1 + 2 * rho.im) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨1, 1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible (-GaussianInt.Norm.Small.imaginaryUnit)
      GaussianInt.Norm.Small.negImaginaryUnit_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_sub_twice_nonneg_of_lt_half rhoSquare.2.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) +
            (1 - 2 * rho.re) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨1, -1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate,
          GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · apply False.elim
    apply (unitImpossible (-1) GaussianInt.Norm.Small.negOne_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_sub_twice_nonneg_of_lt_half rhoSquare.2.2.2
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-1)) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-1)) +
            (1 - 2 * rho.im) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨1, -1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · rfl
  · rfl
  · apply False.elim
    apply (unitImpossible 1 GaussianInt.Norm.Small.one_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_add_twice_nonneg_of_neg_half_le rhoSquare.2.2.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian 1) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian 1) +
            (1 + 2 * rho.im) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨-1, 1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im,
          Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · apply False.elim
    apply (unitImpossible GaussianInt.Norm.Small.imaginaryUnit
      GaussianInt.Norm.Small.imaginaryUnit_isGaussianUnit
      (by decide))
    have gap := Fraction.Order.Arithmetic.one_add_twice_nonneg_of_neg_half_le rhoSquare.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit) +
            (1 + 2 * rho.re) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨-1, 1⟩))
        := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate,
          GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          Int.cast_one, Algebra.Ring.IntCast.cast_zero, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible 1 GaussianInt.Norm.Small.one_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_sub_twice_nonneg_of_lt_half rhoSquare.2.2.2
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian 1) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian 1) +
            (1 - 2 * rho.im) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨-1,
        -1⟩)) := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.one_re,
          GaussianInt.one_im,
          Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1
  · rfl
  · exact (zeroImpossible (by decide)).elim
  · apply False.elim
    apply (unitImpossible (-GaussianInt.Norm.Small.imaginaryUnit)
      GaussianInt.Norm.Small.negImaginaryUnit_isGaussianUnit (by decide))
    have gap := Fraction.Order.Arithmetic.one_add_twice_nonneg_of_neg_half_le rhoSquare.1
    calc
      Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) ≤
          Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit)) +
            (1 + 2 * rho.re) := (fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
              (show a ≤ a + b from by
                simpa only [add_zero, -eq_self, -iff_self] using
                  Fraction.Order.Arithmetic.add_le_add_direct
                    (Fraction.Order.Basic.le_refl a) h)) gap
      _ = Data.Gaussian.Norm.Basic.normSq (rho + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn ⟨-1,
        -1⟩)) := by
        simp only [GaussianInt.Norm.Small.cornerTurn, GaussianInt.Norm.Basic.conjugate,
          GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
          Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
        ring1

/-- Multiplying a unit-centred exterior factor by any nonzero integral
associate preserves the quadrance-one lower bound. -/
theorem one_le_associated_factor_normSq (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) (s t unit : GaussianInt)
    (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit) (associated : s = t * unit)
    (oneLeMultiplierNorm : 1 ≤ GaussianInt.normNat t) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
  have factorIdentity :
      GaussianInt.toGaussian s -
          GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value =
        GaussianInt.toGaussian t *
          (GaussianInt.toGaussian unit - (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value)
            := by
    rw [associated, GaussianInt.toGaussian_mul]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  have multiplierCast :
      (1 : Fraction.Rational) ≤ (GaussianInt.normNat t : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct oneLeMultiplierNorm
  have unitExterior :
      1 ≤ Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian unit - (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) :=
          by
    rw [GaussianInt.Norm.Small.normSq_sub_comm]
    exact one_le_next_sub_unit_normSq fraction nonterminal unitProperty
  have productExterior := Fraction.Order.Arithmetic.mul_le_mul_direct
    multiplierCast unitExterior (show (0 : Fraction.Rational) ≤ 1 by decide)
    (show (0 : Fraction.Rational) ≤ (GaussianInt.normNat t : Fraction.Rational) by
      exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
  rw [factorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian]
  calc
    1 = (1 : Fraction.Rational) * 1 := by ring1
    _ ≤ (GaussianInt.normNat t : Fraction.Rational) *
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian unit -
          (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) :=
      productExterior

/-- A Lakein factor with two Gaussian-unit coefficients has quadrance at least one.

Factoring one unit coefficient through the other reduces the claim to the unit-centered exterior inequality for the next
nonterminal quotient. -/
theorem one_le_factor_normSq_of_unit_coefficients (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) {s t : GaussianInt}
    (sNorm : GaussianInt.normNat s = 1) (tNorm : GaussianInt.normNat t = 1) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
  have sUnit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one sNorm
  have tUnit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one tNorm
  rcases GaussianInt.Norm.Small.exists_unit_right_factor_of_units sUnit tUnit with
    ⟨unit, unitProperty, associated⟩
  apply one_le_associated_factor_normSq fraction nonterminal s t unit
    unitProperty associated
  rw [tNorm]

/-- A Lakein factor with two diagonal coefficients has quadrance at least one.

The coefficients differ by a Gaussian unit, and their common norm-two factor preserves the unit exterior lower bound. -/
theorem one_le_factor_normSq_of_diagonal_coefficients (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) {s t : GaussianInt}
    (sNorm : GaussianInt.normNat s = 2) (tNorm : GaussianInt.normNat t = 2) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
  have sDiagonal := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two sNorm
  have tDiagonal := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two tNorm
  rcases GaussianInt.Norm.Small.exists_unit_right_factor_of_diagonals sDiagonal tDiagonal with
    ⟨unit, unitProperty, associated⟩
  apply one_le_associated_factor_normSq fraction nonterminal s t unit
    unitProperty associated
  rw [tNorm]
  decide

/-- The next complete quotient has quadrance at least two.  This is just the
reciprocal of a nonzero residual of quadrance at most one half. -/
theorem next_normSq_ge_two (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    2 ≤ Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
      := by
  have residualNonzero := GaussianInt.Division.Nearest.residual_ne_zero nonterminal
  have reciprocal :
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
        GaussianInt.Division.Nearest.residual fraction = 1 := by
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ residualNonzero]
  have productIdentity :
      Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) = 1 := by
    rw [← Gaussian.Norm.Basic.normSq_mul, reciprocal, Gaussian.Norm.Basic.normSq_one]
  have nextPositive : 0 < Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
    nonterminal).value :=
    Gaussian.Norm.Basic.normSq_pos (fun zero => by
      have productZero := congrArg
        (fun value => value * GaussianInt.Division.Nearest.residual fraction) zero
      rw [reciprocal, Gaussian.Basic.zero_mul] at productZero
      exact (show (1 : Gaussian.Basic.Canonical) ≠ 0 by decide) productZero)
  have scaledResidual :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (GaussianInt.Nearest.remainder_normSq_le_half fraction.value)
      nextPositive.le
  have oneLeHalf :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value * (1 / 2) := by
    calc
      1 = Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.Division.Nearest.residual fraction) := productIdentity.symm
      _ ≤ Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value * (1 / 2) :=
        scaledResidual
  have doubled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLeHalf
      (show (0 : Fraction.Rational) ≤ 2 by decide)
  calc
    2 = 1 * 2 := by ring1
    _ ≤ (Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value * (1 / 2)) * 2 :=
      doubled
    _ = Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
      * 1 := by
      rw [_root_.mul_assoc,
        show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
    _ = Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
      := by
      ring1

/-- A noninitial Hurwitz partial quotient cannot be zero or a Gaussian unit. -/
theorem two_le_next_digit_normNat (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    2 ≤ GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
      fraction nonterminal)) := by
  apply Nat.le_of_not_gt
  intro digitSmall
  have zeroOrOne : GaussianInt.normNat (GaussianInt.Division.Nearest.digit
    (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) = 0 ∨
      GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal)) = 1 := by
    generalize normEquality :
      GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal)) = norm
    cases norm with
    | zero => exact Or.inl rfl
    | succ remaining =>
        cases remaining with
        | zero => exact Or.inr rfl
        | succ tail =>
            rw [normEquality] at digitSmall
            have twoLe : 2 ≤ Nat.succ (Nat.succ tail) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le tail))
            exact (Nat.not_lt_of_ge twoLe digitSmall).elim
  rcases zeroOrOne with zeroNorm | unitNorm
  · have digitZero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero zeroNorm
    have valueResidual : (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value =
        GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) :=
          by
      calc
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value =
            GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
              fraction nonterminal)) +
              GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
                nonterminal) :=
          GaussianInt.Division.Nearest.value_eq_digit_add_residual (Data.ComplexContinuedFraction.Hurwitz.Step.next
            fraction nonterminal)
        _ = GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)
          := by
          rw [digitZero, GaussianInt.toGaussian_zero,
            Gaussian.Basic.zero_add]
    have lower := next_normSq_ge_two fraction nonterminal
    have upper :=
      GaussianInt.Nearest.remainder_normSq_le_half
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
    rw [valueResidual] at lower
    exact (not_lt_of_ge lower
      (upper.trans_lt (show (1 / 2 : Fraction.Rational) < 2 by decide)))
  · have digitUnit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one unitNorm
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal digitUnit
    have differenceResidual :
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value -
            GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
              fraction nonterminal)) =
          GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)
            := by
      rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im] <;>
        ring1
    rw [differenceResidual] at exterior
    have upper :=
      GaussianInt.Nearest.remainder_normSq_le_half
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
    exact (not_lt_of_ge exterior
      (upper.trans_lt (show (1 / 2 : Fraction.Rational) < 1 by decide)))

/-- If adding an integral multiple of a shorter previous denominator does
not increase quadrance, that multiplier has quadrance below four. -/
theorem coefficient_normNat_lt_four_of_combination_norm_le
    (coefficient current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    (combinationNotLarger :
      GaussianInt.normNat (coefficient * current + previous) ≤ GaussianInt.normNat current) :
    GaussianInt.normNat coefficient < 4 := by
  have currentPositiveNat : 0 < GaussianInt.normNat current :=
    (Nat.zero_le (GaussianInt.normNat previous)).trans_lt previousShorter
  have currentPositive :
      (0 : Fraction.Rational) < (GaussianInt.normNat current : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct currentPositiveNat
  have previousCastShorter :
      (GaussianInt.normNat previous : Fraction.Rational) < (GaussianInt.normNat current : Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_lt_iff_direct).2 previousShorter
  have combinationCastNotLarger :
      (GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) ≤
        (GaussianInt.normNat current : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct combinationNotLarger
  have coefficientDifference :
      GaussianInt.toGaussian (coefficient * current) =
        GaussianInt.toGaussian (coefficient * current + previous) - GaussianInt.toGaussian previous := by
    rw [GaussianInt.toGaussian_add]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im] <;>
      ring1
  have normBound :
      (GaussianInt.normNat coefficient : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) ≤
        2 *
          ((GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) +
            (GaussianInt.normNat previous : Fraction.Rational)) := by
    calc
      (GaussianInt.normNat coefficient : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (coefficient * current)) := by
        rw [GaussianInt.normSq_toGaussian, GaussianInt.Embedding.normNat_mul, Algebra.NatCast.mul]
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian (coefficient * current + previous) -
            GaussianInt.toGaussian previous) := by rw [coefficientDifference]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (coefficient * current + previous)) +
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian previous)) :=
              Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ = 2 *
          ((GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) +
            (GaussianInt.normNat previous : Fraction.Rational)) := by
        rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
  have sumStrict :
      (GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) +
          (GaussianInt.normNat previous : Fraction.Rational) <
        2 * (GaussianInt.normNat current : Fraction.Rational) := by
    have firstLeg := Fraction.Order.Arithmetic.add_le_add_right_direct
      combinationCastNotLarger (GaussianInt.normNat previous : Fraction.Rational)
    have secondLeg := Fraction.Order.Arithmetic.add_lt_add_right_direct
      previousCastShorter (GaussianInt.normNat current : Fraction.Rational)
    have secondLegOrdered :
        (GaussianInt.normNat current : Fraction.Rational) + (GaussianInt.normNat previous : Fraction.Rational) <
          (GaussianInt.normNat current : Fraction.Rational) + (GaussianInt.normNat current : Fraction.Rational) := by
      calc
        (GaussianInt.normNat current : Fraction.Rational) + (GaussianInt.normNat previous : Fraction.Rational) =
            (GaussianInt.normNat previous : Fraction.Rational) +
              (GaussianInt.normNat current : Fraction.Rational) := by ring1
        _ < (GaussianInt.normNat current : Fraction.Rational) +
            (GaussianInt.normNat current : Fraction.Rational) := secondLeg
    calc
      (GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) +
          (GaussianInt.normNat previous : Fraction.Rational) <
        (GaussianInt.normNat current : Fraction.Rational) +
          (GaussianInt.normNat current : Fraction.Rational) := firstLeg.trans_lt secondLegOrdered
      _ = 2 * (GaussianInt.normNat current : Fraction.Rational) := by ring1
  have scaledStrict :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) sumStrict
  have productStrict :
      (GaussianInt.normNat coefficient : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) <
        4 * (GaussianInt.normNat current : Fraction.Rational) := by
    exact normBound.trans_lt (by
      calc
        2 *
            ((GaussianInt.normNat (coefficient * current + previous) : Fraction.Rational) +
              (GaussianInt.normNat previous : Fraction.Rational)) <
          2 * (2 * (GaussianInt.normNat current : Fraction.Rational)) := scaledStrict
        _ = 4 * (GaussianInt.normNat current : Fraction.Rational) := by ring1)
  have coefficientCastSmall :
      (GaussianInt.normNat coefficient : Fraction.Rational) < 4 :=
    Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      productStrict currentPositive
  exact (Fraction.Cast.Order.natCast_lt_iff_direct).1 coefficientCastSmall

/-- With a diagonal coefficient on the previous denominator, a strictly
shorter combination forces the current coefficient to have quadrance below
six.  This is the square-root-free triangle estimate used before the two
exceptional lattice shapes are analysed. -/
theorem currentCoefficient_normNat_lt_six_of_diagonal_previous
    (s t current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    (tNorm : GaussianInt.normNat t = 2)
    (combinationShorter :
      GaussianInt.normNat (s * current + t * previous) < GaussianInt.normNat current) :
    GaussianInt.normNat s < 6 := by
  have currentPositiveNat : 0 < GaussianInt.normNat current :=
    (Nat.zero_le (GaussianInt.normNat previous)).trans_lt previousShorter
  have currentPositive :
      (0 : Fraction.Rational) < (GaussianInt.normNat current : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct currentPositiveNat
  have previousCastShorter :
      (GaussianInt.normNat previous : Fraction.Rational) < (GaussianInt.normNat current : Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_lt_iff_direct).2 previousShorter
  have combinationCastShorter :
      (GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) <
        (GaussianInt.normNat current : Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_lt_iff_direct).2 combinationShorter
  have coefficientDifference :
      GaussianInt.toGaussian (s * current) =
        GaussianInt.toGaussian (s * current + t * previous) -
          GaussianInt.toGaussian (t * previous) := by
    rw [GaussianInt.toGaussian_add]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im] <;>
      ring1
  have normBound :
      (GaussianInt.normNat s : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) ≤
        2 *
          ((GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) +
            2 * (GaussianInt.normNat previous : Fraction.Rational)) := by
    calc
      (GaussianInt.normNat s : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) =
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (s * current)) := by
        rw [GaussianInt.normSq_toGaussian, GaussianInt.Embedding.normNat_mul, Algebra.NatCast.mul]
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian (s * current + t * previous) -
            GaussianInt.toGaussian (t * previous)) := by rw [coefficientDifference]
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (s * current + t * previous)) +
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (t * previous))) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ = 2 *
          ((GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) +
            2 * (GaussianInt.normNat previous : Fraction.Rational)) := by
        rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian, GaussianInt.Embedding.normNat_mul, tNorm,
          Algebra.NatCast.mul, Nat.cast_ofNat]
  have twicePreviousShorter :
      2 * (GaussianInt.normNat previous : Fraction.Rational) <
        2 * (GaussianInt.normNat current : Fraction.Rational) :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) previousCastShorter
  have sumStrict :
      (GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) +
          2 * (GaussianInt.normNat previous : Fraction.Rational) <
        3 * (GaussianInt.normNat current : Fraction.Rational) := by
    have sum := Fraction.Order.Arithmetic.add_lt_add_direct
      combinationCastShorter twicePreviousShorter
    calc
      (GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) +
            2 * (GaussianInt.normNat previous : Fraction.Rational) <
          (GaussianInt.normNat current : Fraction.Rational) +
            2 * (GaussianInt.normNat current : Fraction.Rational) := sum
      _ = 3 * (GaussianInt.normNat current : Fraction.Rational) := by ring1
  have scaledStrict :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) sumStrict
  have productStrict :
      (GaussianInt.normNat s : Fraction.Rational) * (GaussianInt.normNat current : Fraction.Rational) <
        6 * (GaussianInt.normNat current : Fraction.Rational) := by
    exact normBound.trans_lt (by
      calc
        2 *
              ((GaussianInt.normNat (s * current + t * previous) : Fraction.Rational) +
                2 * (GaussianInt.normNat previous : Fraction.Rational)) <
            2 * (3 * (GaussianInt.normNat current : Fraction.Rational)) := scaledStrict
        _ = 6 * (GaussianInt.normNat current : Fraction.Rational) := by ring1)
  have coefficientCastSmall : (GaussianInt.normNat s : Fraction.Rational) < 6 :=
    Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      productStrict currentPositive
  exact (Fraction.Cast.Order.natCast_lt_iff_direct).1
    coefficientCastSmall

/-- The only possible noninitial digit in a non-growing continuant step is
a diagonal digit. -/
theorem next_digit_isDiagonal_of_combination_norm_le
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    (combinationNotLarger :
      GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal) * current + previous) ≤
        GaussianInt.normNat current) :
    GaussianInt.Norm.Small.IsDiagonal (GaussianInt.Division.Nearest.digit
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) := by
  have digitSmall := coefficient_normNat_lt_four_of_combination_norm_le
    (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) current
      previous
    previousShorter combinationNotLarger
  have digitAtLeastTwo := two_le_next_digit_normNat fraction nonterminal
  have digitCases := GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four
    (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal))
      digitSmall
  have digitNorm : GaussianInt.normNat (GaussianInt.Division.Nearest.digit
    (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) = 2 := by
    rcases digitCases with zero | one | two
    · omega
    · omega
    · exact two
  exact GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two digitNorm

/-- A strict future corner approach together with denominator non-growth
forces the unique doubled-corner digit which continues the backward
succession. -/
theorem next_digit_eq_two_cornerTurn_of_corner_failure
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    {corner : GaussianInt} (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner)
    (denominatorFailure :
      GaussianInt.normNat
          (corner *
              (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)
                * current + previous) +
            current) ≤
        GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
          fraction nonterminal) * current + previous))
    (futureCorner :
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
            nonterminal) nextNonterminal).value -
            GaussianInt.toGaussian corner) < 1) :
    GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) =
      GaussianInt.Norm.Small.cornerTurn corner + GaussianInt.Norm.Small.cornerTurn corner := by
  let nextFraction := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let difference := GaussianInt.Division.Nearest.digit nextFraction - GaussianInt.Norm.Small.cornerTurn corner
  have transformedFailure :
      GaussianInt.normNat (difference * current + previous) ≤ GaussianInt.normNat current := by
    dsimp only [difference, nextFraction]
    exact (corner_combination_norm_le_iff cornerDiagonal
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal))
        current previous).1
        denominatorFailure
  have differenceSmall : GaussianInt.normNat difference < 4 :=
    coefficient_normNat_lt_four_of_combination_norm_le
      difference current previous previousShorter transformedFailure
  have differenceCases :=
    GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four difference differenceSmall
  have rhoApproach :
      Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.Division.Nearest.residual nextFraction + GaussianInt.toGaussian
            (GaussianInt.Norm.Small.cornerTurn corner)) < 1 := by
    dsimp only [nextFraction]
    exact residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal cornerDiagonal futureCorner
  have coefficientRecovery :
      difference + GaussianInt.Norm.Small.cornerTurn corner = GaussianInt.Division.Nearest.digit nextFraction := by
    dsimp only [difference]
    apply GaussianInt.ext <;>
      simp only [GaussianInt.add_re,
        GaussianInt.add_im,
        GaussianInt.sub_re,
        GaussianInt.sub_im] <;>
      ring1
  have valueAsDifference :
      nextFraction.value =
        GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn corner) +
          GaussianInt.Division.Nearest.residual nextFraction := by
    calc
      nextFraction.value =
          GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit nextFraction) +
            GaussianInt.Division.Nearest.residual nextFraction :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual nextFraction
      _ = GaussianInt.toGaussian (difference + GaussianInt.Norm.Small.cornerTurn corner) +
          GaussianInt.Division.Nearest.residual nextFraction := by rw [coefficientRecovery]
  have completeLower : 2 ≤ Data.Gaussian.Norm.Basic.normSq nextFraction.value := by
    dsimp only [nextFraction]
    exact next_normSq_ge_two fraction nonterminal
  rcases differenceCases with differenceZero | differenceUnit | differenceDiagonal
  · have zero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero differenceZero
    have valueCorner : nextFraction.value =
        GaussianInt.Division.Nearest.residual nextFraction + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn
          corner) := by
      rw [valueAsDifference, zero,
        GaussianInt.zero_add,
        Gaussian.Basic.add_comm]
    rw [valueCorner] at completeLower
    exact (not_lt_of_ge completeLower
      (rhoApproach.trans_le (by decide))).elim
  · have differenceIsUnit :=
      GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one differenceUnit
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      differenceIsUnit
    have valueSubDifference :
        nextFraction.value - GaussianInt.toGaussian difference =
          GaussianInt.Division.Nearest.residual nextFraction + GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn
            corner) := by
      rw [valueAsDifference, GaussianInt.toGaussian_add]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im] <;>
        ring1
    rw [valueSubDifference] at exterior
    exact (not_lt_of_ge exterior rhoApproach).elim
  · have differenceIsDiagonal :=
      GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two differenceDiagonal
    have differenceTurn := diagonal_eq_cornerTurn_of_local_geometry
      (GaussianInt.Division.Nearest.residual nextFraction)
      (GaussianInt.Nearest.remainder_mem nextFraction.value)
      (GaussianInt.Nearest.remainder_normSq_le_half nextFraction.value)
      cornerDiagonal differenceIsDiagonal rhoApproach
      (by rw [← valueAsDifference]; exact completeLower)
      (by
        intro unit unitProperty
        rw [← valueAsDifference]
        exact one_le_next_sub_unit_normSq fraction nonterminal unitProperty)
    calc
      GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) =
          difference + GaussianInt.Norm.Small.cornerTurn corner := by
        dsimp only [nextFraction] at coefficientRecovery
        exact coefficientRecovery.symm
      _ = GaussianInt.Norm.Small.cornerTurn corner + GaussianInt.Norm.Small.cornerTurn corner := by rw [differenceTurn]

/-- One exceptional corner failure transfers to the preceding continuant
with the transformed corner.  Iterating this lemma reaches the explicit
initial pair; no infinite continued fraction is introduced. -/
theorem corner_failure_transfers_backward
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    {corner : GaussianInt} (cornerDiagonal : GaussianInt.Norm.Small.IsDiagonal corner)
    (denominatorFailure :
      GaussianInt.normNat
          (corner *
              (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)
                * current + previous) +
            current) ≤
        GaussianInt.normNat (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
          fraction nonterminal) * current + previous))
    (futureCorner :
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
            nonterminal) nextNonterminal).value -
            GaussianInt.toGaussian corner) < 1) :
    GaussianInt.normNat (GaussianInt.Norm.Small.cornerTurn corner * current + previous) ≤ GaussianInt.normNat current ∧
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value -
            GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner)) < 1 := by
  have digitForced := next_digit_eq_two_cornerTurn_of_corner_failure
    fraction nonterminal nextNonterminal current previous previousShorter
    cornerDiagonal denominatorFailure futureCorner
  have transformed := (corner_combination_norm_le_iff cornerDiagonal
    (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) current
      previous).1
      denominatorFailure
  have denominatorTransferred :
      GaussianInt.normNat (GaussianInt.Norm.Small.cornerTurn corner * current + previous) ≤ GaussianInt.normNat current
        := by
    have combinationIdentity :
        (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) -
          GaussianInt.Norm.Small.cornerTurn corner) * current +
            previous =
          GaussianInt.Norm.Small.cornerTurn corner * current + previous := by
      rw [digitForced]
      apply GaussianInt.ext <;>
        simp only [GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im] <;>
        ring1
    rw [combinationIdentity] at transformed
    exact transformed
  have residualTransferred :=
    residual_add_cornerTurn_normSq_lt_one_of_next_sub_corner
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal cornerDiagonal futureCorner
  have futureTransferred :
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value -
            GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner)) < 1 := by
    have valueDifference :
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value -
            GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner) =
          GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) +
            GaussianInt.toGaussian (GaussianInt.Norm.Small.cornerTurn corner) := by
      rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual, digitForced, GaussianInt.toGaussian_add]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im] <;>
        ring1
    rw [valueDifference]
    exact residualTransferred
  exact ⟨denominatorTransferred, futureTransferred⟩

/-- The finite natural-extension invariant needed for Hurwitz denominator
growth.  Besides strict growth of the adjacent denominator, it excludes the
four corner configurations which would start Lakein's exceptional backward
succession. -/
structure StageGeometry {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage
  source) : Prop where
  /-- The previous denominator has strictly smaller natural quadrance than the current denominator. -/ denominatorGrowth
    :
    GaussianInt.normNat stage.previous.denominator < GaussianInt.normNat stage.current.denominator
  /-- No diagonal corner simultaneously prevents denominator growth and lies within unit distance of the next complete
    quotient. -/ cornerSafe : ∀ (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) corner,
    GaussianInt.Norm.Small.IsDiagonal corner → ¬
      (GaussianInt.normNat
          (corner * stage.current.denominator + stage.previous.denominator) ≤
          GaussianInt.normNat stage.current.denominator ∧
        Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value - GaussianInt.toGaussian
            corner) < 1)

/-- The sole exceptional denominator shape left by the elementary Lakein
coefficient estimates.  It is finite up to the eight quadrance-five values
and four diagonal values. -/
@[expose] def NormFiveDenominatorSafe {source : GaussianInt.Fraction} (stage :
  Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) : Prop :=
  ∀ s t : GaussianInt, GaussianInt.normNat s = 5 → GaussianInt.normNat t = 2 →
    GaussianInt.normNat stage.current.denominator ≤
      GaussianInt.normNat
        (s * stage.current.denominator + t * stage.previous.denominator)

/-- The norm-five quadratic form with positive linear terms is at least one when the first coordinate is at least -3/4.

Completing both coordinate squares gives an exact rational certificate with denominator eight. -/
private theorem one_le_normFive_form_of_lower
    (x y : Fraction.Rational) (lower : -(3 / 4 : Fraction.Rational) ≤ x) :
    1 ≤ 5 + 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2 := by
  have scaledLower :
      4 * (-(3 / 4 : Fraction.Rational)) ≤ 4 * x :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower
      (show (0 : Fraction.Rational) ≤ 4 by decide)
  have linearLower : (3 : Fraction.Rational) ≤ 4 * x + 6 := by
    calc
      (3 : Fraction.Rational) = 4 * (-(3 / 4)) + 6 := by decide
      _ ≤ 4 * x + 6 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct scaledLower 6
  have linearNonnegative : (0 : Fraction.Rational) ≤ 4 * x + 6 :=
    (show (0 : Fraction.Rational) ≤ 3 by decide).trans linearLower
  have squareLower : (9 : Fraction.Rational) ≤ (4 * x + 6) ^ 2 := by
    rw [show (9 : Fraction.Rational) = 3 * 3 by decide, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct linearLower linearLower
      (show (0 : Fraction.Rational) ≤ 3 by decide) linearNonnegative
  have otherSquareNonnegative :
      (0 : Fraction.Rational) ≤ (4 * y + 2) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have sumLower :
      (8 : Fraction.Rational) ≤ (4 * x + 6) ^ 2 + (4 * y + 2) ^ 2 :=
    (show (8 : Fraction.Rational) ≤ 9 by decide).trans
      (squareLower.trans ((fun {a b : Fraction.Rational} (h : 0 ≤ b) =>
        (show a ≤ a + b from by
          simpa only [add_zero, -eq_self, -iff_self] using
            Fraction.Order.Arithmetic.add_le_add_direct
              (Fraction.Order.Basic.le_refl a) h)) otherSquareNonnegative))
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 8)
  · calc
      (1 : Fraction.Rational) * 8 = 8 := by ring1
      _ ≤ (4 * x + 6) ^ 2 + (4 * y + 2) ^ 2 := sumLower
      _ = (5 + 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2) * 8 := by
        ring1
  · decide

/-- The norm-five form with negative second-coordinate linear term is at least one when the first coordinate is at least
-3/4. -/
private theorem one_le_normFive_form_of_lower_negative
    (x y : Fraction.Rational) (lower : -(3 / 4 : Fraction.Rational) ≤ x) :
    1 ≤ 5 + 6 * x + 2 * x ^ 2 - 2 * y + 2 * y ^ 2 := by
  have bound := one_le_normFive_form_of_lower x (-y) lower
  convert bound using 1
  all_goals ring1

/-- The norm-five form with negative first-coordinate linear term is at least one when the first coordinate is at most
3/4. -/
private theorem one_le_normFive_form_of_upper
    (x y : Fraction.Rational) (upper : x ≤ (3 / 4 : Fraction.Rational)) :
    1 ≤ 5 - 6 * x + 2 * x ^ 2 + 2 * y + 2 * y ^ 2 := by
  have reflectedLower : -(3 / 4 : Fraction.Rational) ≤ -x :=
    Fraction.Order.Arithmetic.neg_le_neg_direct upper
  have bound := one_le_normFive_form_of_lower (-x) y reflectedLower
  convert bound using 1
  all_goals ring1

/-- The norm-five form with both linear terms negative is at least one when the first coordinate is at most 3/4. -/
private theorem one_le_normFive_form_of_upper_negative
    (x y : Fraction.Rational) (upper : x ≤ (3 / 4 : Fraction.Rational)) :
    1 ≤ 5 - 6 * x + 2 * x ^ 2 - 2 * y + 2 * y ^ 2 := by
  have bound := one_le_normFive_form_of_upper x (-y) upper
  convert bound using 1
  all_goals ring1

/-- The quadrance-five/diagonal combination is exterior whenever the
normalised preceding denominator lies in the coordinate box
`[-3/4,3/4]²`. -/
theorem one_le_normSq_normFive_add_diagonal_mul_of_coordinate_bounds
    (ratio : Gaussian.Basic.Canonical) (s t : GaussianInt) (sNorm : GaussianInt.normNat s = 5)
    (tNorm : GaussianInt.normNat t = 2)
    (realLower : -(3 / 4 : Fraction.Rational) ≤ ratio.re)
    (realUpper : ratio.re ≤ (3 / 4 : Fraction.Rational))
    (imaginaryLower : -(3 / 4 : Fraction.Rational) ≤ ratio.im)
    (imaginaryUpper : ratio.im ≤ (3 / 4 : Fraction.Rational)) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s + GaussianInt.toGaussian t * ratio) := by
  have sCases := GaussianInt.Norm.Small.normFive_cases_of_normNat_eq_five sNorm
  have tCases := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two tNorm
  rcases sCases with sCase | sCase | sCase | sCase | sCase | sCase |
      sCase | sCase <;>
    rcases tCases with tCase | tCase | tCase | tCase <;>
    subst s <;> subst t
  all_goals simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
    Gaussian.Basic.add_re,
    Gaussian.Basic.add_im,
    Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  all_goals solve
    | (convert one_le_normFive_form_of_lower ratio.re ratio.im realLower
        using 1; ring1)
    | (convert one_le_normFive_form_of_lower_negative ratio.re ratio.im
        realLower using 1; ring1)
    | (convert one_le_normFive_form_of_upper ratio.re ratio.im realUpper
        using 1; ring1)
    | (convert one_le_normFive_form_of_upper_negative ratio.re ratio.im
        realUpper using 1; ring1)
    | (convert one_le_normFive_form_of_lower ratio.im ratio.re imaginaryLower
        using 1; ring1)
    | (convert one_le_normFive_form_of_lower_negative ratio.im ratio.re
        imaginaryLower using 1; ring1)
    | (convert one_le_normFive_form_of_upper ratio.im ratio.re imaginaryUpper
        using 1; ring1)
    | (convert one_le_normFive_form_of_upper_negative ratio.im ratio.re
        imaginaryUpper using 1; ring1)

/-- Stages obtained by finitely iterating the executable transition. -/
inductive Generated (source : GaussianInt.Fraction) : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source → Prop
  /-- The initial stage belongs to the finite executable generation relation. -/ | first :
    Generated source
    (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source)
  /-- A nonterminal executable transition preserves membership in the finite generation relation. -/ | advance {stage :
    Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source} :
    Generated source stage →
      (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) →
      Generated source
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal)

/-- The initial Hurwitz stage has strictly growing denominators and excludes every diagonal corner failure.

Its retained adjacent denominators are zero and one, so the corner condition reduces to the impossible natural-number
inequality two at most one. -/
theorem firstStage_geometry (source : GaussianInt.Fraction) :
    StageGeometry (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) := by
  constructor
  · change GaussianInt.normNat 0 < GaussianInt.normNat 1
    decide
  · intro nonterminal corner cornerDiagonal failure
    have cornerNorm := GaussianInt.Norm.Small.normNat_eq_two_of_isDiagonal cornerDiagonal
    have denominatorFailure := failure.1
    change GaussianInt.normNat (corner * 1 + 0) ≤ GaussianInt.normNat 1 at denominatorFailure
    simp only [GaussianInt.mul_one,
      GaussianInt.add_zero,
      cornerNorm] at denominatorFailure
    change 2 ≤ 1 at denominatorFailure
    exact False.elim ((by decide : ¬(2 : Nat) ≤ 1) denominatorFailure)

/-- The initial Hurwitz stage satisfies every norm-five/diagonal denominator comparison. -/
theorem firstStage_normFiveDenominatorSafe (source : GaussianInt.Fraction) :
    NormFiveDenominatorSafe (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) := by
  intro s t sNorm _tNorm
  change GaussianInt.normNat 1 ≤ GaussianInt.normNat (s * 1 + t * 0)
  rw [GaussianInt.mul_one,
    GaussianInt.mul_zero,
    GaussianInt.add_zero, sNorm]
  decide

/-- A nonterminal Hurwitz transition preserves denominator growth and diagonal corner safety.

Any failure at the new stage transfers backward to a corner failure at the supplied stage, contradicting its retained
geometric invariant. -/
theorem advanceStage_geometry {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage
  source}
    (geometry : StageGeometry stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) :
    StageGeometry (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal) := by
  let nextFraction := Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal
  let nextDigit := GaussianInt.Division.Nearest.digit nextFraction
  have nextDenominator :
      (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal).current.denominator =
        nextDigit * stage.current.denominator + stage.previous.denominator := rfl
  have nextPrevious :
      (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal).previous.denominator =
        stage.current.denominator := rfl
  have growth :
      GaussianInt.normNat stage.current.denominator <
        GaussianInt.normNat
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal).current.denominator := by
    apply Nat.lt_of_not_ge
    intro notGrowing
    have combinationNotLarger :
        GaussianInt.normNat (nextDigit * stage.current.denominator +
            stage.previous.denominator) ≤
          GaussianInt.normNat stage.current.denominator := by
      rw [← nextDenominator]
      exact notGrowing
    have digitDiagonal : GaussianInt.Norm.Small.IsDiagonal nextDigit := by
      dsimp only [nextDigit, nextFraction]
      exact next_digit_isDiagonal_of_combination_norm_le
        stage.quotient nonterminal stage.current.denominator
        stage.previous.denominator geometry.denominatorGrowth
        combinationNotLarger
    have futureClose :
        Data.Gaussian.Norm.Basic.normSq (nextFraction.value - GaussianInt.toGaussian nextDigit) < 1 := by
      have residualIdentity :
          nextFraction.value - GaussianInt.toGaussian nextDigit = GaussianInt.Division.Nearest.residual nextFraction :=
            by
        rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual]
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im] <;>
          ring1
      rw [residualIdentity]
      exact (GaussianInt.Nearest.remainder_normSq_le_half nextFraction.value).trans_lt
        (show (1 / 2 : Fraction.Rational) < 1 by decide)
    exact (geometry.cornerSafe nonterminal nextDigit digitDiagonal
      ⟨combinationNotLarger, futureClose⟩)
  refine
    { denominatorGrowth := by rw [nextPrevious]; exact growth
      cornerSafe := ?_ }
  intro nextNonterminal corner cornerDiagonal failure
  have transferred := corner_failure_transfers_backward
    stage.quotient nonterminal
    (by
      change GaussianInt.Division.Nearest.remainder nextFraction ≠ 0
      exact nextNonterminal)
    stage.current.denominator stage.previous.denominator
    geometry.denominatorGrowth cornerDiagonal
    (by
      change GaussianInt.normNat
          (corner * (nextDigit * stage.current.denominator +
            stage.previous.denominator) + stage.current.denominator) ≤
        GaussianInt.normNat (nextDigit * stage.current.denominator +
          stage.previous.denominator)
      rw [← nextDenominator, ← nextPrevious]
      exact failure.1)
    (by
      change Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next nextFraction nextNonterminal).value - GaussianInt.toGaussian
            corner) < 1
      exact failure.2)
  exact geometry.cornerSafe nonterminal (GaussianInt.Norm.Small.cornerTurn corner)
    (GaussianInt.Norm.Small.cornerTurn_isDiagonal cornerDiagonal) transferred

/-- Every stage reached by finitely many executable Hurwitz transitions satisfies the stage geometry invariant. -/
theorem geometry_of_generated {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage
  source}
    (generated : Generated source stage) : StageGeometry stage := by
  induction generated with
  | first => exact firstStage_geometry source
  | advance generated nonterminal inductionHypothesis =>
      exact advanceStage_geometry inductionHypothesis nonterminal

/-- Every stage in a finite fuel-bounded trace is generated when its starting stage is generated.

The induction preserves the exact starting source and follows only transitions whose remainders are nonzero. -/
private theorem generated_of_mem_stagesFromFuel {source : GaussianInt.Fraction}
    (fuel : Nat)
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) (stageGenerated : Generated
      source stage)
    {candidate : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (member : candidate ∈
      Data.ComplexContinuedFraction.Hurwitz.Trace.stagesFromFuel fuel stage) :
    Generated source candidate := by
  induction fuel generalizing stage with
  | zero =>
      change candidate ∈ [stage] at member
      have equal := Data.List.Membership.mem_singleton.mp member
      rw [equal]
      exact stageGenerated
  | succ fuel inductionHypothesis =>
      by_cases terminal : GaussianInt.Division.Nearest.remainder stage.quotient = 0
      · simp only [Data.ComplexContinuedFraction.Hurwitz.Trace.stagesFromFuel, dif_pos terminal] at member
        have equal := Data.List.Membership.mem_singleton.mp member
        rw [equal]
        exact stageGenerated
      · simp only [Data.ComplexContinuedFraction.Hurwitz.Trace.stagesFromFuel, dif_neg terminal] at member
        rcases Data.List.Membership.mem_cons.mp member with current | later
        · rw [current]
          exact stageGenerated
        · exact inductionHypothesis
            (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage terminal)
            (Hurwitz.Geometry.Generated.advance stageGenerated terminal) later

/-- Every member of the terminating trace from a generated stage is generated. -/
theorem generated_of_mem_stagesFrom {source : GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) (stageGenerated : Generated
      source stage)
    {candidate : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (member : candidate ∈ Data.ComplexContinuedFraction.Hurwitz.Trace.stagesFrom stage) :
    Generated source candidate := by
  exact generated_of_mem_stagesFromFuel
    (Nat.succ (GaussianInt.normNat stage.quotient.denominator))
    stage stageGenerated member

/-- Every member of the finite Hurwitz stage list is generated from its original rational source. -/
theorem generated_of_mem_stages {source : GaussianInt.Fraction} {stage :
  Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (member : stage ∈ Data.ComplexContinuedFraction.Hurwitz.Trace.stages source) :
    Generated source stage := by
  exact generated_of_mem_stagesFrom (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source)
    Hurwitz.Geometry.Generated.first member

/-- A generated Hurwitz stage has current denominator quadrance strictly larger than its previous denominator quadrance.
-/
theorem stage_denominatorGrowth {source : GaussianInt.Fraction} {stage :
  Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Generated source stage) :
    GaussianInt.normNat stage.previous.denominator < GaussianInt.normNat stage.current.denominator :=
  (geometry_of_generated generated).denominatorGrowth

/-- Every stage in the finite Hurwitz trace has strictly increasing adjacent denominator quadrances. -/
theorem stage_denominatorGrowth_of_mem_stages
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (member : stage ∈ Data.ComplexContinuedFraction.Hurwitz.Trace.stages source) :
    GaussianInt.normNat stage.previous.denominator < GaussianInt.normNat stage.current.denominator :=
  stage_denominatorGrowth (generated_of_mem_stages member)

/-- Advancing once multiplies the old complete denominator by the new
complete quotient.  This is the finite continuant identity
`xₙ₊₂ (xₙ₊₁ qₙ + qₙ₋₁) = xₙ₊₂ qₙ₊₁ + qₙ`. -/
theorem advanceStage_completeDenominator {source : GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (nextNonterminal :
      GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage
        nonterminal).quotient ≠
        0) :
    (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal).completeDenominator
        nextNonterminal =
      (Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
        nonterminal) nextNonterminal).value *
        stage.completeDenominator nonterminal := by
  let nextFraction := Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal
  let nextValue := (Data.ComplexContinuedFraction.Hurwitz.Step.next nextFraction nextNonterminal).value
  have residualNonzero : GaussianInt.Division.Nearest.residual nextFraction ≠ 0 :=
    GaussianInt.Division.Nearest.residual_ne_zero nextNonterminal
  have reciprocal : nextValue * GaussianInt.Division.Nearest.residual nextFraction = 1 := by
    dsimp only [nextValue]
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ residualNonzero]
  have decomposition :
      (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value =
        GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit nextFraction) + GaussianInt.Division.Nearest.residual
          nextFraction := by
    dsimp only [nextFraction]
    exact GaussianInt.Division.Nearest.value_eq_digit_add_residual (Data.ComplexContinuedFraction.Hurwitz.Step.next
      stage.quotient nonterminal)
  change nextValue *
        GaussianInt.toGaussian
          (GaussianInt.Division.Nearest.digit nextFraction * stage.current.denominator +
            stage.previous.denominator) +
      GaussianInt.toGaussian stage.current.denominator =
    nextValue *
      ((Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value *
          GaussianInt.toGaussian stage.current.denominator +
        GaussianInt.toGaussian stage.previous.denominator)
  rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, decomposition]
  calc
    nextValue *
          (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit nextFraction) *
              GaussianInt.toGaussian stage.current.denominator +
            GaussianInt.toGaussian stage.previous.denominator) +
        GaussianInt.toGaussian stage.current.denominator =
      nextValue *
          (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit nextFraction) *
              GaussianInt.toGaussian stage.current.denominator +
            GaussianInt.toGaussian stage.previous.denominator) +
        (nextValue * GaussianInt.Division.Nearest.residual nextFraction) *
          GaussianInt.toGaussian stage.current.denominator := by
      rw [reciprocal, _root_.one_mul]
    _ = nextValue *
        ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit nextFraction) +
          GaussianInt.Division.Nearest.residual nextFraction) *
            GaussianInt.toGaussian stage.current.denominator +
          GaussianInt.toGaussian stage.previous.denominator) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re,
          Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1

/-- If the complete denominator at a generated step were no larger than its
current continuant denominator, the next complete quotient would have
quadrance below three.  The hypothesis involving `x * previous` is exactly
what the preceding complete-denominator inequality becomes after one Hurwitz
transition. -/
theorem quotient_normSq_lt_three_of_complete_failure
    (x current previous : Gaussian.Basic.Canonical)
    (currentNonzero : current ≠ 0)
    (scaledPreviousStrict :
      Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq previous <
        Data.Gaussian.Norm.Basic.normSq (x * current + previous))
    (completeFailure :
      Data.Gaussian.Norm.Basic.normSq (x * current + previous) ≤ Data.Gaussian.Norm.Basic.normSq current) :
    Data.Gaussian.Norm.Basic.normSq x < 3 := by
  have currentPositive : 0 < Data.Gaussian.Norm.Basic.normSq current := Gaussian.Norm.Basic.normSq_pos
    currentNonzero
  have previousNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq previous := Gaussian.Norm.Basic.normSq_nonneg
    previous
  have currentNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq current := currentPositive.le
  apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
  intro threeLe
  have threePreviousLe :
      3 * Data.Gaussian.Norm.Basic.normSq previous ≤ Data.Gaussian.Norm.Basic.normSq x *
        Data.Gaussian.Norm.Basic.normSq previous :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      threeLe previousNonnegative
  have threePreviousLtCurrent :
      3 * Data.Gaussian.Norm.Basic.normSq previous < Data.Gaussian.Norm.Basic.normSq current :=
    threePreviousLe.trans_lt
      (scaledPreviousStrict.trans_le completeFailure)
  have twoPreviousLeThreePrevious :
      2 * Data.Gaussian.Norm.Basic.normSq previous ≤ 3 * Data.Gaussian.Norm.Basic.normSq previous := by
    have oneLeThree : (2 : Fraction.Rational) ≤ 3 := by decide
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      oneLeThree previousNonnegative
  have twoPreviousLtCurrent :
      2 * Data.Gaussian.Norm.Basic.normSq previous < Data.Gaussian.Norm.Basic.normSq current :=
    twoPreviousLeThreePrevious.trans_lt threePreviousLtCurrent
  have sumStrict :
      2 * (Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq previous) <
        3 * Data.Gaussian.Norm.Basic.normSq current := by
    have shifted :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct
        twoPreviousLtCurrent (2 * Data.Gaussian.Norm.Basic.normSq current)
    calc
      2 * (Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq previous) =
          2 * Data.Gaussian.Norm.Basic.normSq current + 2 * Data.Gaussian.Norm.Basic.normSq previous := by ring1
      _ < 2 * Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq current := shifted
      _ = 3 * Data.Gaussian.Norm.Basic.normSq current := by ring1
  have productUpper :
      Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq current < 3 *
        Data.Gaussian.Norm.Basic.normSq current := by
    calc
      Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq current =
        Data.Gaussian.Norm.Basic.normSq (x * current) := by
        rw [Gaussian.Norm.Basic.normSq_mul]
      _ = Data.Gaussian.Norm.Basic.normSq ((x * current + previous) - previous) := by
        congr 1
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im] <;>
          ring1
      _ ≤ 2 *
          (Data.Gaussian.Norm.Basic.normSq (x * current + previous) + Data.Gaussian.Norm.Basic.normSq previous)
            :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq previous) := by
        have sumLe := add_le_add_right completeFailure (Data.Gaussian.Norm.Basic.normSq previous)
        have reordered :
            Data.Gaussian.Norm.Basic.normSq (x * current + previous) + Data.Gaussian.Norm.Basic.normSq previous
              ≤
              Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq previous := by
          calc
            Data.Gaussian.Norm.Basic.normSq (x * current + previous) + Data.Gaussian.Norm.Basic.normSq previous
              =
                Data.Gaussian.Norm.Basic.normSq previous + Data.Gaussian.Norm.Basic.normSq (x * current +
                  previous) := by ring1
            _ ≤ Data.Gaussian.Norm.Basic.normSq previous + Data.Gaussian.Norm.Basic.normSq current := sumLe
            _ = Data.Gaussian.Norm.Basic.normSq current + Data.Gaussian.Norm.Basic.normSq previous := by ring1
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          reordered (show (0 : Fraction.Rational) ≤ 2 by decide)
      _ < 3 * Data.Gaussian.Norm.Basic.normSq current := sumStrict
  have productLower :
      3 * Data.Gaussian.Norm.Basic.normSq current ≤ Data.Gaussian.Norm.Basic.normSq x *
        Data.Gaussian.Norm.Basic.normSq current :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      threeLe currentNonnegative
  exact (not_lt_of_ge productLower productUpper)

/-- A noninitial complete quotient of quadrance below three must have a
diagonal nearest Gaussian integer.  The exterior tests against the four
units rule out a rounded coordinate of magnitude at least two. -/
theorem next_digit_isDiagonal_of_normSq_lt_three
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value < 3) :
    GaussianInt.Norm.Small.IsDiagonal (GaussianInt.Division.Nearest.digit
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)) := by
  let nextFraction := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let nextValue := nextFraction.value
  let nextDigit := GaussianInt.Division.Nearest.digit nextFraction
  let rho := GaussianInt.Division.Nearest.residual nextFraction
  have decomposition :
      nextValue = GaussianInt.toGaussian nextDigit + rho :=
    GaussianInt.Division.Nearest.value_eq_digit_add_residual nextFraction
  have realDecomposition :
      nextValue.re = (nextDigit.re : Fraction.Rational) + rho.re := by
    simpa only [Gaussian.Basic.add_re, GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using congrArg Gaussian.Basic.re decomposition
  have imaginaryDecomposition :
      nextValue.im = (nextDigit.im : Fraction.Rational) + rho.im := by
    simpa only [Gaussian.Basic.add_im, GaussianInt.toGaussian,
      ← Rat.Fraction.Cast.intCast_eq_fromInt] using congrArg Gaussian.Basic.im decomposition
  have rhoSquare := GaussianInt.Nearest.remainder_mem nextFraction.value
  have realUpper : nextDigit.re < 2 := by
    apply Data.Int.Order.lt_of_not_le
    intro twoLeDigit
    have castTwoLe :
        (2 : Fraction.Rational) ≤ (nextDigit.re : Fraction.Rational) :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct 2
        nextDigit.re).2 twoLeDigit
    have nextRealLower : (3 / 2 : Fraction.Rational) ≤ nextValue.re := by
      calc
        (3 / 2 : Fraction.Rational) = 2 + (-(1 / 2 : Fraction.Rational)) := by decide
        _ ≤ (nextDigit.re : Fraction.Rational) + rho.re := by
          exact Fraction.Order.Arithmetic.add_le_add_direct
            castTwoLe rhoSquare.1
        _ = nextValue.re := realDecomposition.symm
    have doubledRealLower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        nextRealLower (show (0 : Fraction.Rational) ≤ 2 by decide)
    have radialGap : (2 : Fraction.Rational) ≤ 2 * nextValue.re - 1 := by
      calc
        (2 : Fraction.Rational) = 2 * (3 / 2 : Fraction.Rational) - 1 := by decide
        _ ≤ 2 * nextValue.re - 1 :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            doubledRealLower 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := 1) GaussianInt.Norm.Small.one_isGaussianUnit
    have threeLe : (3 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq nextValue := by
      calc
        (3 : Fraction.Rational) = 1 + 2 := by ring1
        _ ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian 1) +
            (2 * nextValue.re - 1) :=
          Fraction.Order.Arithmetic.add_le_add_direct exterior radialGap
        _ = Data.Gaussian.Norm.Basic.normSq nextValue := by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.one_re,
            GaussianInt.one_im,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    exact (not_lt_of_ge threeLe small)
  have realLower : -(2 : Int) < nextDigit.re := by
    apply Data.Int.Order.lt_of_not_le
    intro digitLeNegTwo
    have castLeNegTwo :
        (nextDigit.re : Fraction.Rational) ≤ (-2 : Fraction.Rational) :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct
        nextDigit.re (-2)).2 digitLeNegTwo
    have nextRealUpper : nextValue.re < -(3 / 2 : Fraction.Rational) := by
      calc
        nextValue.re = (nextDigit.re : Fraction.Rational) + rho.re :=
          realDecomposition
        _ < (-2 : Fraction.Rational) + (1 / 2 : Fraction.Rational) := by
          have first := Fraction.Order.Arithmetic.add_le_add_right_direct
            castLeNegTwo rho.re
          have second := Fraction.Order.Arithmetic.add_lt_add_left_direct
            rhoSquare.2.1 (-2)
          exact first.trans_lt second
        _ = -(3 / 2 : Fraction.Rational) := by decide
    have doubledRealUpper :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Fraction.Rational) < 2 by decide) nextRealUpper
    have radialGap : (2 : Fraction.Rational) < -(2 * nextValue.re) - 1 := by
      have negated :
          -(2 * (-(3 / 2 : Fraction.Rational))) < -(2 * nextValue.re) :=
        Fraction.Order.Arithmetic.neg_lt_neg_direct doubledRealUpper
      calc
        (2 : Fraction.Rational) = -(2 * (-(3 / 2 : Fraction.Rational))) - 1 := by decide
        _ < -(2 * nextValue.re) - 1 :=
          Fraction.Order.Arithmetic.sub_lt_sub_right_direct negated 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := -1) GaussianInt.Norm.Small.negOne_isGaussianUnit
    have threeLt : (3 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq nextValue := by
      calc
        (3 : Fraction.Rational) = 1 + 2 := by ring1
        _ < Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian (-1)) +
            (-(2 * nextValue.re) - 1) := by
          have first := Fraction.Order.Arithmetic.add_le_add_right_direct
            exterior 2
          have second := Fraction.Order.Arithmetic.add_lt_add_left_direct
            radialGap (Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian (-1)))
          exact first.trans_lt second
        _ = Data.Gaussian.Norm.Basic.normSq nextValue := by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im,
            GaussianInt.one_re,
            GaussianInt.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    exact (not_lt_of_ge threeLt.le small)
  have imaginaryUpper : nextDigit.im < 2 := by
    apply Data.Int.Order.lt_of_not_le
    intro twoLeDigit
    have castTwoLe :
        (2 : Fraction.Rational) ≤ (nextDigit.im : Fraction.Rational) :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct 2
        nextDigit.im).2 twoLeDigit
    have nextImaginaryLower : (3 / 2 : Fraction.Rational) ≤ nextValue.im := by
      calc
        (3 / 2 : Fraction.Rational) = 2 + (-(1 / 2 : Fraction.Rational)) := by decide
        _ ≤ (nextDigit.im : Fraction.Rational) + rho.im := by
          exact Fraction.Order.Arithmetic.add_le_add_direct
            castTwoLe rhoSquare.2.2.1
        _ = nextValue.im := imaginaryDecomposition.symm
    have doubledImaginaryLower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        nextImaginaryLower (show (0 : Fraction.Rational) ≤ 2 by decide)
    have radialGap : (2 : Fraction.Rational) ≤ 2 * nextValue.im - 1 := by
      calc
        (2 : Fraction.Rational) = 2 * (3 / 2 : Fraction.Rational) - 1 := by decide
        _ ≤ 2 * nextValue.im - 1 :=
          Fraction.Order.Arithmetic.sub_le_sub_right_direct
            doubledImaginaryLower 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.imaginaryUnit_isGaussianUnit
    have threeLe : (3 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq nextValue := by
      calc
        (3 : Fraction.Rational) = 1 + 2 := by ring1
        _ ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
          GaussianInt.Norm.Small.imaginaryUnit) +
            (2 * nextValue.im - 1) :=
          Fraction.Order.Arithmetic.add_le_add_direct exterior radialGap
        _ = Data.Gaussian.Norm.Basic.normSq nextValue := by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian, Algebra.Ring.IntCast.cast_zero, Int.cast_one, ←
              Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    exact (not_lt_of_ge threeLe small)
  have imaginaryLower : -(2 : Int) < nextDigit.im := by
    apply Data.Int.Order.lt_of_not_le
    intro digitLeNegTwo
    have castLeNegTwo :
        (nextDigit.im : Fraction.Rational) ≤ (-2 : Fraction.Rational) :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct
        nextDigit.im (-2)).2 digitLeNegTwo
    have nextImaginaryUpper : nextValue.im < -(3 / 2 : Fraction.Rational) := by
      calc
        nextValue.im = (nextDigit.im : Fraction.Rational) + rho.im :=
          imaginaryDecomposition
        _ < (-2 : Fraction.Rational) + (1 / 2 : Fraction.Rational) := by
          have first := Fraction.Order.Arithmetic.add_le_add_right_direct
            castLeNegTwo rho.im
          have second := Fraction.Order.Arithmetic.add_lt_add_left_direct
            rhoSquare.2.2.2 (-2)
          exact first.trans_lt second
        _ = -(3 / 2 : Fraction.Rational) := by decide
    have doubledImaginaryUpper :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Fraction.Rational) < 2 by decide) nextImaginaryUpper
    have radialGap : (2 : Fraction.Rational) < -(2 * nextValue.im) - 1 := by
      have negated :
          -(2 * (-(3 / 2 : Fraction.Rational))) < -(2 * nextValue.im) :=
        Fraction.Order.Arithmetic.neg_lt_neg_direct doubledImaginaryUpper
      calc
        (2 : Fraction.Rational) = -(2 * (-(3 / 2 : Fraction.Rational))) - 1 := by decide
        _ < -(2 * nextValue.im) - 1 :=
          Fraction.Order.Arithmetic.sub_lt_sub_right_direct negated 1
    have exterior := one_le_next_sub_unit_normSq fraction nonterminal
      (unit := -GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.negImaginaryUnit_isGaussianUnit
    have threeLt : (3 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq nextValue := by
      calc
        (3 : Fraction.Rational) = 1 + 2 := by ring1
        _ < Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
          (-GaussianInt.Norm.Small.imaginaryUnit)) +
            (-(2 * nextValue.im) - 1) := by
          have first := Fraction.Order.Arithmetic.add_le_add_right_direct
            exterior 2
          have second := Fraction.Order.Arithmetic.add_lt_add_left_direct
            radialGap (Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
              (-GaussianInt.Norm.Small.imaginaryUnit)))
          exact first.trans_lt second
        _ = Data.Gaussian.Norm.Basic.normSq nextValue := by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    exact (not_lt_of_ge threeLt.le small)
  have realCases : nextDigit.re = -1 ∨ nextDigit.re = 0 ∨
      nextDigit.re = 1 :=
    GaussianInt.Norm.Small.coordinate_cases_of_neg_two_lt_lt_two realLower realUpper
  have imaginaryCases : nextDigit.im = -1 ∨ nextDigit.im = 0 ∨
      nextDigit.im = 1 :=
    GaussianInt.Norm.Small.coordinate_cases_of_neg_two_lt_lt_two imaginaryLower imaginaryUpper
  have realSquareLe : nextDigit.re * nextDigit.re ≤ 1 := by
    rcases realCases with real | real | real <;> rw [real] <;> decide
  have imaginarySquareLe : nextDigit.im * nextDigit.im ≤ 1 := by
    rcases imaginaryCases with imaginary | imaginary | imaginary <;>
      rw [imaginary] <;> decide
  have digitNormLeTwo : GaussianInt.normNat nextDigit ≤ 2 := by
    have normIntLe : GaussianInt.normInt nextDigit ≤ 2 := by
      dsimp only [GaussianInt.normInt]
      exact (Data.Int.Order.add_le_add realSquareLe imaginarySquareLe).trans_eq rfl
    rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat] at normIntLe
    exact Data.Int.Order.natCast_le_iff.mp normIntLe
  have digitNormAtLeastTwo := two_le_next_digit_normNat fraction nonterminal
  change 2 ≤ GaussianInt.normNat nextDigit at digitNormAtLeastTwo
  have digitNorm : GaussianInt.normNat nextDigit = 2 :=
    Nat.le_antisymm digitNormLeTwo digitNormAtLeastTwo
  exact GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two digitNorm

/-- In the diagonal case, failure of complete-denominator growth would force
the following ordinary continuant step not to grow.  This is the integral
form of the four reflected copies of `northeast_lune_exterior`. -/
theorem diagonal_combination_norm_le_of_complete_failure
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (current previous : GaussianInt)
    (previousShorter : GaussianInt.normNat previous < GaussianInt.normNat current)
    (digitDiagonal : GaussianInt.Norm.Small.IsDiagonal (GaussianInt.Division.Nearest.digit
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)))
    (completeFailure :
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value * GaussianInt.toGaussian current
            +
            GaussianInt.toGaussian previous) ≤
        (GaussianInt.normNat current : Fraction.Rational)) :
    GaussianInt.normNat
        (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) *
          current + previous) ≤
      GaussianInt.normNat current := by
  let nextFraction := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let nextValue := nextFraction.value
  let nextDigit := GaussianInt.Division.Nearest.digit nextFraction
  let rho := GaussianInt.Division.Nearest.residual nextFraction
  let currentValue := GaussianInt.toGaussian current
  let previousValue := GaussianInt.toGaussian previous
  have currentNonzero : current ≠ 0 := by
    intro currentZero
    rw [currentZero] at previousShorter
    change GaussianInt.normNat previous < 0 at previousShorter
    omega
  have currentValueNonzero : currentValue ≠ 0 := by
    intro currentValueZero
    exact currentNonzero (GaussianInt.toGaussian_eq_zero.mp currentValueZero)
  let ratio := previousValue * currentValue⁻¹
  have ratioMulCurrent : ratio * currentValue = previousValue := by
    dsimp only [ratio]
    calc
      (previousValue * currentValue⁻¹) * currentValue =
          previousValue * (currentValue⁻¹ * currentValue) := by
        rw [Gaussian.Basic.mul_assoc]
      _ = previousValue * 1 := by
        rw [Gaussian.Field.inv_eq,
          Gaussian.Field.inv_mul _ currentValueNonzero]
      _ = previousValue :=
        Gaussian.Basic.mul_one _
  have ratioInside : Data.Gaussian.Norm.Basic.normSq ratio < 1 := by
    have currentNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq currentValue :=
      Gaussian.Norm.Basic.normSq_pos currentValueNonzero
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq currentValue) _ currentNormPositive
    calc
      Data.Gaussian.Norm.Basic.normSq ratio * Data.Gaussian.Norm.Basic.normSq currentValue =
          Data.Gaussian.Norm.Basic.normSq (ratio * currentValue) := by
        exact (Gaussian.Norm.Basic.normSq_mul ratio currentValue).symm
      _ = Data.Gaussian.Norm.Basic.normSq previousValue := by rw [ratioMulCurrent]
      _ = (GaussianInt.normNat previous : Fraction.Rational) := GaussianInt.normSq_toGaussian previous
      _ < (GaussianInt.normNat current : Fraction.Rational) :=
        Fraction.Cast.Order.natCast_lt_direct previousShorter
      _ = Data.Gaussian.Norm.Basic.normSq currentValue := (GaussianInt.normSq_toGaussian current).symm
      _ = 1 * Data.Gaussian.Norm.Basic.normSq currentValue := by ring1
  have decomposition : nextValue = GaussianInt.toGaussian nextDigit + rho :=
    GaussianInt.Division.Nearest.value_eq_digit_add_residual nextFraction
  have completeIdentity :
      (nextValue + ratio) * currentValue =
        nextValue * currentValue + previousValue := by
    rw [← ratioMulCurrent]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  have normalizedComplete : Data.Gaussian.Norm.Basic.normSq (nextValue + ratio) ≤ 1 := by
    have currentNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq currentValue :=
      Gaussian.Norm.Basic.normSq_pos currentValueNonzero
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq currentValue) _ currentNormPositive
    calc
      Data.Gaussian.Norm.Basic.normSq (nextValue + ratio) * Data.Gaussian.Norm.Basic.normSq currentValue =
          Data.Gaussian.Norm.Basic.normSq ((nextValue + ratio) * currentValue) := by rw
            [Gaussian.Norm.Basic.normSq_mul]
      _ = Data.Gaussian.Norm.Basic.normSq (nextValue * currentValue + previousValue) := by
        rw [completeIdentity]
      _ ≤ (GaussianInt.normNat current : Fraction.Rational) := completeFailure
      _ = Data.Gaussian.Norm.Basic.normSq currentValue := (GaussianInt.normSq_toGaussian current).symm
      _ = 1 * Data.Gaussian.Norm.Basic.normSq currentValue := by ring1
  have rhoSquare := GaussianInt.Nearest.remainder_mem nextFraction.value
  have rhoRealUpper : rho.re ≤ (1 / 2 : Fraction.Rational) := rhoSquare.2.1.le
  have rhoImaginaryUpper :
      rho.im ≤ (1 / 2 : Fraction.Rational) := rhoSquare.2.2.2.le
  have ratioCoordinates : ratio.re ^ 2 + ratio.im ^ 2 < 1 := by
    exact ratioInside
  have baseNorm : Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian nextDigit + ratio) ≤ 1 := by
    change GaussianInt.Norm.Small.IsDiagonal nextDigit at digitDiagonal
    rcases digitDiagonal with digitCase | digitCase | digitCase | digitCase
    · rw [digitCase] at decomposition ⊢
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.imaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := 1) GaussianInt.Norm.Small.one_isGaussianUnit
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
        GaussianInt.Norm.Small.imaginaryUnit) at verticalExterior
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian 1) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := Gaussian.Norm.Bounds.northeast_lune_exterior
        rho.re rho.im ratio.re ratio.im rhoSquare.1 rhoSquare.2.2.1
        ratioCoordinates
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian, Algebra.Ring.IntCast.cast_zero, Int.cast_one, ←
              Rat.Fraction.Cast.intCast_eq_fromInt] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.one_re,
            GaussianInt.one_im,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im, GaussianInt.toGaussian,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at normalizedComplete
          exact normalizedComplete)
      simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, GaussianInt.toGaussian,
        Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      exact lune
    · rw [digitCase] at decomposition ⊢
      have reflectedImaginaryLower :
          -(1 / 2 : Fraction.Rational) ≤ -rho.im := by
        have reversed :=
          Fraction.Order.Arithmetic.neg_le_neg_direct rhoImaginaryUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.negImaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := 1) GaussianInt.Norm.Small.one_isGaussianUnit
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
        (-GaussianInt.Norm.Small.imaginaryUnit)) at verticalExterior
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian 1) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := Gaussian.Norm.Bounds.northeast_lune_exterior
        rho.re (-rho.im) ratio.re (-ratio.im) rhoSquare.1
        reflectedImaginaryLower
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.one_re,
            GaussianInt.one_im,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im, GaussianInt.toGaussian,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, GaussianInt.toGaussian,
        Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      convert lune using 1
      all_goals ring1
    · rw [digitCase] at decomposition ⊢
      have reflectedRealLower :
          -(1 / 2 : Fraction.Rational) ≤ -rho.re := by
        have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct rhoRealUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.imaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -1) GaussianInt.Norm.Small.negOne_isGaussianUnit
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
        GaussianInt.Norm.Small.imaginaryUnit) at verticalExterior
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian (-1)) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := Gaussian.Norm.Bounds.northeast_lune_exterior
        (-rho.re) rho.im (-ratio.re) ratio.im reflectedRealLower
        rhoSquare.2.2.1
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian, Algebra.Ring.IntCast.cast_zero, Int.cast_one, ←
              Rat.Fraction.Cast.intCast_eq_fromInt] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im,
            GaussianInt.one_re,
            GaussianInt.one_im,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im, GaussianInt.toGaussian,
            Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, GaussianInt.toGaussian,
        Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      convert lune using 1
      all_goals ring1
    · rw [digitCase] at decomposition ⊢
      have reflectedRealLower :
          -(1 / 2 : Fraction.Rational) ≤ -rho.re := by
        have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct rhoRealUpper
        simpa only [neg_neg] using reversed
      have reflectedImaginaryLower :
          -(1 / 2 : Fraction.Rational) ≤ -rho.im := by
        have reversed :=
          Fraction.Order.Arithmetic.neg_le_neg_direct rhoImaginaryUpper
        simpa only [neg_neg] using reversed
      have verticalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -GaussianInt.Norm.Small.imaginaryUnit) GaussianInt.Norm.Small.negImaginaryUnit_isGaussianUnit
      have horizontalExterior := one_le_next_sub_unit_normSq fraction nonterminal
          (unit := -1) GaussianInt.Norm.Small.negOne_isGaussianUnit
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian
        (-GaussianInt.Norm.Small.imaginaryUnit)) at verticalExterior
      change 1 ≤ Data.Gaussian.Norm.Basic.normSq (nextValue - GaussianInt.toGaussian (-1)) at horizontalExterior
      rw [decomposition] at verticalExterior horizontalExterior
      have lune := Gaussian.Norm.Bounds.northeast_lune_exterior
        (-rho.re) (-rho.im) (-ratio.re) (-ratio.im) reflectedRealLower
        reflectedImaginaryLower
        (by
          convert ratioCoordinates using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.Norm.Small.imaginaryUnit,
            GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im, ← Rat.Fraction.Cast.intCast_eq_fromInt] at verticalExterior
          convert verticalExterior using 1
          all_goals ring1)
        (by
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im, GaussianInt.toGaussian,
            GaussianInt.neg_re,
            GaussianInt.neg_im,
            GaussianInt.one_re,
            GaussianInt.one_im, ← Rat.Fraction.Cast.intCast_eq_fromInt] at horizontalExterior
          convert horizontalExterior using 1
          all_goals ring1)
        (by
          rw [decomposition] at normalizedComplete
          simp only [Data.Gaussian.Norm.Basic.normSq,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt] at normalizedComplete
          convert normalizedComplete using 1
          all_goals ring1)
      simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      convert lune using 1
      all_goals ring1
  change GaussianInt.normNat (nextDigit * current + previous) ≤ GaussianInt.normNat current
  apply (Fraction.Cast.Order.natCast_le_iff_direct).1
  have combinationIdentity :
      (GaussianInt.toGaussian nextDigit + ratio) * currentValue =
        GaussianInt.toGaussian (nextDigit * current + previous) := by
    calc
      (GaussianInt.toGaussian nextDigit + ratio) * currentValue =
          GaussianInt.toGaussian nextDigit * currentValue + ratio * currentValue := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = GaussianInt.toGaussian nextDigit * currentValue + previousValue := by
        rw [ratioMulCurrent]
      _ = GaussianInt.toGaussian (nextDigit * current + previous) := by
        rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  have currentNormNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq currentValue :=
    Gaussian.Norm.Basic.normSq_nonneg currentValue
  calc
    (GaussianInt.normNat (nextDigit * current + previous) : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian (nextDigit * current + previous)) :=
      (GaussianInt.normSq_toGaussian _).symm
    _ = Data.Gaussian.Norm.Basic.normSq ((GaussianInt.toGaussian nextDigit + ratio) * currentValue) := by
      rw [combinationIdentity]
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian nextDigit + ratio) *
      Data.Gaussian.Norm.Basic.normSq currentValue :=
      Gaussian.Norm.Basic.normSq_mul _ _
    _ ≤ 1 * Data.Gaussian.Norm.Basic.normSq currentValue :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        baseNorm currentNormNonnegative
    _ = Data.Gaussian.Norm.Basic.normSq currentValue := by ring1
    _ = (GaussianInt.normNat current : Fraction.Rational) := GaussianInt.normSq_toGaussian current

/-- Every nonterminal stage of the finite Hurwitz trace has a complete
denominator strictly larger than its current continuant denominator.  The
proof is induction on the displayed trace: a hypothetical failure forces a
diagonal digit, the lune calculation forces the following ordinary
continuant not to grow, and finite denominator growth rules that out. -/
theorem completeDenominatorGrowth_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) :
    (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
      Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal) := by
  induction generated with
  | first =>
      have nextLarge := next_normSq_ge_two source nonterminal
      change (1 : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next source nonterminal).value * GaussianInt.toGaussian 1 +
            GaussianInt.toGaussian 0)
      rw [GaussianInt.toGaussian_one, GaussianInt.toGaussian_zero,
        Gaussian.Basic.mul_one,
        Gaussian.Basic.add_zero]
      exact (show (1 : Fraction.Rational) < 2 by decide).trans_le nextLarge
  | @advance previousStage generated previousNonterminal inductionHypothesis =>
      let advanced :=
        Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage previousStage previousNonterminal
      let nextValue := (Data.ComplexContinuedFraction.Hurwitz.Step.next advanced.quotient nonterminal).value
      have previousCompleteGrowth :=
        inductionHypothesis previousNonterminal
      have nextNormPositive : 0 < Data.Gaussian.Norm.Basic.normSq nextValue := by
        have nextLarge := next_normSq_ge_two advanced.quotient nonterminal
        exact (show (0 : Fraction.Rational) < 2 by decide).trans_le nextLarge
      have scaledPreviousGrowth :
          Data.Gaussian.Norm.Basic.normSq nextValue *
              Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian advanced.previous.denominator) <
            Data.Gaussian.Norm.Basic.normSq
              (nextValue * GaussianInt.toGaussian advanced.current.denominator +
                GaussianInt.toGaussian advanced.previous.denominator) := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            nextNormPositive previousCompleteGrowth
        calc
          Data.Gaussian.Norm.Basic.normSq nextValue *
                Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian advanced.previous.denominator) =
              Data.Gaussian.Norm.Basic.normSq nextValue *
                (GaussianInt.normNat previousStage.current.denominator : Fraction.Rational) := by
            change Data.Gaussian.Norm.Basic.normSq nextValue *
                Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian previousStage.current.denominator) =
              Data.Gaussian.Norm.Basic.normSq nextValue *
                (GaussianInt.normNat previousStage.current.denominator : Fraction.Rational)
            rw [GaussianInt.normSq_toGaussian]
          _ < Data.Gaussian.Norm.Basic.normSq nextValue *
                Data.Gaussian.Norm.Basic.normSq
                  (previousStage.completeDenominator previousNonterminal) :=
            scaled
          _ = Data.Gaussian.Norm.Basic.normSq
                (nextValue *
                  previousStage.completeDenominator previousNonterminal) := by
            rw [Gaussian.Norm.Basic.normSq_mul]
          _ = Data.Gaussian.Norm.Basic.normSq (advanced.completeDenominator nonterminal) := by
            change Data.Gaussian.Norm.Basic.normSq
                ((Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next
                  previousStage.quotient previousNonterminal)
                    nonterminal).value *
                  previousStage.completeDenominator previousNonterminal) =
              Data.Gaussian.Norm.Basic.normSq
                ((Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage previousStage
                  previousNonterminal).completeDenominator nonterminal)
            rw [advanceStage_completeDenominator previousStage
              previousNonterminal nonterminal]
          _ = Data.Gaussian.Norm.Basic.normSq
                (nextValue * GaussianInt.toGaussian advanced.current.denominator +
                  GaussianInt.toGaussian advanced.previous.denominator) := rfl
      have currentNonzero : advanced.current.denominator ≠ 0 := by
        intro currentZero
        have growth := stage_denominatorGrowth
          (Hurwitz.Geometry.Generated.advance generated previousNonterminal)
        rw [currentZero] at growth
        change GaussianInt.normNat advanced.previous.denominator < 0 at growth
        omega
      have currentValueNonzero :
          GaussianInt.toGaussian advanced.current.denominator ≠ 0 := by
        intro currentValueZero
        exact currentNonzero (GaussianInt.toGaussian_eq_zero.mp currentValueZero)
      apply Fraction.Order.Arithmetic.lt_of_not_ge_direct
      intro completeFailure
      have completeFailureValue :
          Data.Gaussian.Norm.Basic.normSq
                (nextValue * GaussianInt.toGaussian advanced.current.denominator +
                  GaussianInt.toGaussian advanced.previous.denominator) ≤
            Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian advanced.current.denominator) := by
        calc
          Data.Gaussian.Norm.Basic.normSq
                (nextValue * GaussianInt.toGaussian advanced.current.denominator +
                  GaussianInt.toGaussian advanced.previous.denominator) =
              Data.Gaussian.Norm.Basic.normSq (advanced.completeDenominator nonterminal) := rfl
          _ ≤ (GaussianInt.normNat advanced.current.denominator : Fraction.Rational) :=
            completeFailure
          _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian advanced.current.denominator) :=
            (GaussianInt.normSq_toGaussian advanced.current.denominator).symm
      have nextSmall : Data.Gaussian.Norm.Basic.normSq nextValue < 3 :=
        quotient_normSq_lt_three_of_complete_failure
          nextValue (GaussianInt.toGaussian advanced.current.denominator)
          (GaussianInt.toGaussian advanced.previous.denominator) currentValueNonzero
          scaledPreviousGrowth completeFailureValue
      have nextDiagonal :
          GaussianInt.Norm.Small.IsDiagonal (GaussianInt.Division.Nearest.digit
            (Data.ComplexContinuedFraction.Hurwitz.Step.next advanced.quotient nonterminal)) :=
        next_digit_isDiagonal_of_normSq_lt_three advanced.quotient
          nonterminal nextSmall
      have followingFailure :=
        diagonal_combination_norm_le_of_complete_failure advanced.quotient
          nonterminal advanced.current.denominator
          advanced.previous.denominator
          (stage_denominatorGrowth
            (Hurwitz.Geometry.Generated.advance generated previousNonterminal))
          nextDiagonal
          (by
            exact completeFailure)
      have followingGrowth := stage_denominatorGrowth
        (Hurwitz.Geometry.Generated.advance
          (Hurwitz.Geometry.Generated.advance generated previousNonterminal) nonterminal)
      change GaussianInt.normNat advanced.current.denominator <
        GaussianInt.normNat
          (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next advanced.quotient
            nonterminal) *
              advanced.current.denominator +
            advanced.previous.denominator) at followingGrowth
      exact (not_lt_of_ge followingFailure followingGrowth)

/-- A Lakein factor with unit current coefficient and diagonal previous coefficient has quadrance at least one.

The next complete quotient has norm at least two, so multiplying by the diagonal produces a norm at least four before
subtracting the unit. -/
theorem one_le_factor_normSq_of_unit_and_diagonal
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    {s t : GaussianInt} (sNorm : GaussianInt.normNat s = 1)
    (tNorm : GaussianInt.normNat t = 2) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
  have sUnit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one sNorm
  have productLarge :
      4 ≤ Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
    rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, tNorm]
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (next_normSq_ge_two fraction nonterminal)
      (show (0 : Fraction.Rational) ≤ 2 by decide)
    calc
      4 = (2 : Fraction.Rational) * 2 := by ring1
      _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal).value := scaled
  rw [GaussianInt.Norm.Small.normSq_sub_comm]
  exact GaussianInt.Norm.Small.one_le_normSq_sub_unit_of_four_le sUnit productLarge

/-- If the previous-basis coefficient is a unit, a denominator shorter than
the current continuant forces the Lakein factor outside the unit circle.
After multiplying by the conjugate unit, the only nontrivial coefficient is
a diagonal corner; that case is exactly `StageGeometry.cornerSafe`. -/
theorem one_le_factor_normSq_of_unit_previousCoefficient
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (tNorm : GaussianInt.normNat t = 1)
    (denominatorSmaller :
      GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        GaussianInt.normNat stage.current.denominator) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value)
          := by
  let coefficient := GaussianInt.Norm.Basic.conjugate t * s
  have tUnit := GaussianInt.Norm.Small.isGaussianUnit_of_normNat_eq_one tNorm
  have unitCancellation : t * GaussianInt.Norm.Basic.conjugate t = 1 :=
    GaussianInt.Norm.Small.self_mul_conjugate_of_isGaussianUnit tUnit
  have associated : t * coefficient = s := by
    dsimp only [coefficient]
    calc
      t * (GaussianInt.Norm.Basic.conjugate t * s) = (t * GaussianInt.Norm.Basic.conjugate t) * s := by
        apply GaussianInt.ext <;>
          simp only [GaussianInt.mul_re,
            GaussianInt.mul_im] <;>
          ring1
      _ = 1 * s := by rw [unitCancellation]
      _ = s := _root_.one_mul s
  have normalizedDenominator :
      GaussianInt.normNat
          (coefficient * stage.current.denominator +
            stage.previous.denominator) <
        GaussianInt.normNat stage.current.denominator := by
    have multipliedIdentity :
        t *
            (coefficient * stage.current.denominator +
              stage.previous.denominator) =
          s * stage.current.denominator +
            t * stage.previous.denominator := by
      rw [← associated]
      apply GaussianInt.ext <;>
        simp only [GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im] <;>
        ring1
    have multipliedNorm :
        GaussianInt.normNat
            (t *
              (coefficient * stage.current.denominator +
                stage.previous.denominator)) =
          GaussianInt.normNat
            (coefficient * stage.current.denominator +
              stage.previous.denominator) := by
      rw [GaussianInt.Embedding.normNat_mul, tNorm, Nat.one_mul]
    rw [← multipliedIdentity] at denominatorSmaller
    rw [multipliedNorm] at denominatorSmaller
    exact denominatorSmaller
  have coefficientSmall : GaussianInt.normNat coefficient < 4 :=
    coefficient_normNat_lt_four_of_combination_norm_le coefficient
      stage.current.denominator stage.previous.denominator
      (stage_denominatorGrowth generated) normalizedDenominator.le
  have coefficientCases :=
    GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four coefficient coefficientSmall
  rcases coefficientCases with coefficientZero | coefficientUnit |
      coefficientDiagonal
  · have coefficientIsZero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero coefficientZero
    have sIsZero : s = 0 := by
      rw [← associated, coefficientIsZero,
        GaussianInt.mul_zero]
    rw [sIsZero, GaussianInt.toGaussian_zero]
    have nextLarge := next_normSq_ge_two stage.quotient nonterminal
    have factorNorm :
        Data.Gaussian.Norm.Basic.normSq
            (0 - GaussianInt.toGaussian t *
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) =
          Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
            nonterminal).value := by
      rw [Gaussian.Basic.zero_sub, Gaussian.Norm.Basic.normSq_neg,
        Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, tNorm]
      ring1
    rw [factorNorm]
    exact (show (1 : Fraction.Rational) ≤ 2 by decide).trans nextLarge
  · have sNorm : GaussianInt.normNat s = 1 := by
      rw [← associated, GaussianInt.Embedding.normNat_mul, tNorm, Nat.one_mul,
        coefficientUnit]
    exact one_le_factor_normSq_of_unit_coefficients stage.quotient
      nonterminal sNorm tNorm
  · have coefficientIsDiagonal :=
      GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two coefficientDiagonal
    apply Fraction.Order.Arithmetic.le_of_not_gt_direct
    intro factorInside
    have factorIdentity :
        GaussianInt.toGaussian s -
            GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
              nonterminal).value =
          GaussianInt.toGaussian t *
            (GaussianInt.toGaussian coefficient -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) := by
      rw [← associated, GaussianInt.toGaussian_mul]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    have futureCorner :
        Data.Gaussian.Norm.Basic.normSq
            ((Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value -
              GaussianInt.toGaussian coefficient) < 1 := by
      rw [factorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, tNorm,
        Nat.cast_one] at factorInside
      rw [GaussianInt.Norm.Small.normSq_sub_comm]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian coefficient -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) =
          1 * Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian coefficient -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) := by ring1
        _ < 1 := factorInside
    exact (geometry_of_generated generated).cornerSafe nonterminal
      coefficient coefficientIsDiagonal
      ⟨normalizedDenominator.le, futureCorner⟩

/-- The quadrance-four current coefficient in the diagonal-previous branch
also reduces to `cornerSafe`: it factors as the prescribed diagonal times a
second diagonal. -/
theorem one_le_factor_normSq_of_four_and_diagonal
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (sNorm : GaussianInt.normNat s = 4)
    (tNorm : GaussianInt.normNat t = 2)
    (denominatorSmaller :
      GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        GaussianInt.normNat stage.current.denominator) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value)
          := by
  have tDiagonal := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two tNorm
  rcases GaussianInt.Norm.Small.exists_diagonal_right_factor_of_four_and_diagonal sNorm tDiagonal with
    ⟨corner, cornerDiagonal, associated⟩
  have denominatorIdentity :
      s * stage.current.denominator + t * stage.previous.denominator =
        t *
          (corner * stage.current.denominator +
            stage.previous.denominator) := by
    rw [associated]
    apply GaussianInt.ext <;>
      simp only [GaussianInt.add_re,
        GaussianInt.add_im,
        GaussianInt.mul_re,
        GaussianInt.mul_im] <;>
      ring1
  have cornerCombinationNotLarger :
      GaussianInt.normNat
          (corner * stage.current.denominator +
            stage.previous.denominator) ≤
        GaussianInt.normNat stage.current.denominator := by
    rw [denominatorIdentity, GaussianInt.Embedding.normNat_mul, tNorm] at denominatorSmaller
    omega
  apply Fraction.Order.Arithmetic.le_of_not_gt_direct
  intro factorInside
  have factorIdentity :
      GaussianInt.toGaussian s -
          GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value
            =
        GaussianInt.toGaussian t *
          (GaussianInt.toGaussian corner -
            (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) := by
    rw [associated, GaussianInt.toGaussian_mul]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  rw [factorIdentity, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, tNorm,
    Nat.cast_ofNat] at factorInside
  have cornerDistanceNonnegative :
      0 ≤ Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian corner -
          (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have cornerDistanceScaled :
      Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian corner -
            (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) ≤
        2 * Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian corner -
            (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) := by
    calc
      Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian corner -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) =
          1 * Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian corner -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) := by ring1
      _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian corner -
              (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Fraction.Rational) ≤ 2 by decide) cornerDistanceNonnegative
  have futureCorner :
      Data.Gaussian.Norm.Basic.normSq
          ((Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value -
            GaussianInt.toGaussian corner) < 1 := by
    rw [GaussianInt.Norm.Small.normSq_sub_comm]
    exact cornerDistanceScaled.trans_lt factorInside
  exact (geometry_of_generated generated).cornerSafe nonterminal corner
    cornerDiagonal ⟨cornerCombinationNotLarger, futureCorner⟩

/-- All nonexceptional current coefficients in the diagonal-previous branch.
The only omitted lattice shape is quadrance five. -/
theorem one_le_factor_normSq_of_diagonal_previousCoefficient_of_not_five
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (s t : GaussianInt) (tNorm : GaussianInt.normNat t = 2)
    (sSmall : GaussianInt.normNat s < 6) (sNotFive : GaussianInt.normNat s ≠ 5)
    (denominatorSmaller :
      GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        GaussianInt.normNat stage.current.denominator) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal).value)
          := by
  have coefficientCases :=
    GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six s sSmall
  rcases coefficientCases with sZero | sUnit | sDiagonal | sFour | sFive
  · have sIsZero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero sZero
    rw [sIsZero, GaussianInt.toGaussian_zero,
      Gaussian.Basic.zero_sub, Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_mul,
      GaussianInt.normSq_toGaussian, tNorm, Nat.cast_ofNat]
    have nextLarge := next_normSq_ge_two stage.quotient nonterminal
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      nextLarge (show (0 : Fraction.Rational) ≤ 2 by decide)
    calc
      1 ≤ (4 : Fraction.Rational) := by decide
      _ = 2 * 2 := by ring1
      _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
        nonterminal).value := scaled
  · exact one_le_factor_normSq_of_unit_and_diagonal stage.quotient
      nonterminal sUnit tNorm
  · exact one_le_factor_normSq_of_diagonal_coefficients stage.quotient
      nonterminal sDiagonal tNorm
  · exact one_le_factor_normSq_of_four_and_diagonal generated nonterminal
      s t sFour tNorm denominatorSmaller
  · exact (sNotFive sFive).elim

/-- Once the complete denominator is strictly larger than the current
continuant denominator, failure of Lakein's large-`t` test leaves only the
three integral quadrances below four. -/
theorem previousCoefficient_normNat_lt_four_of_not_large
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (competitor : GaussianInt.Pair.Basic.ConvergentPair)
    (completeDenominatorGrowth :
      (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
        Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal))
    (notLarge : ¬
      (4 : Fraction.Rational) *
          (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
        (GaussianInt.normNat
            (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) :
              Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal)) :
    GaussianInt.normNat
        (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) < 4 := by
  let coefficient :=
    GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor
  have smallProduct :
      (GaussianInt.normNat coefficient : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal) ≤
        4 * (GaussianInt.normNat stage.current.denominator : Fraction.Rational) :=
    Fraction.Order.Arithmetic.le_of_not_gt_direct notLarge
  apply Nat.lt_of_not_ge
  intro fourLeCoefficient
  have castFourLeCoefficient :
      (4 : Fraction.Rational) ≤ (GaussianInt.normNat coefficient : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct fourLeCoefficient
  have fourPositive : (0 : Fraction.Rational) < 4 := by decide
  have completeNonnegative :=
    Gaussian.Norm.Basic.normSq_nonneg (stage.completeDenominator nonterminal)
  have scaledGrowth :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      fourPositive completeDenominatorGrowth
  have scaledCoefficient :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      castFourLeCoefficient completeNonnegative
  have impossible :
      4 * (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
        (GaussianInt.normNat coefficient : Fraction.Rational) *
          Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal) :=
    scaledGrowth.trans_le scaledCoefficient
  exact (not_lt_of_ge smallProduct impossible)

/-- Clearing the next complete quotient denominator turns a Lakein factor
into an exact Gaussian-integer numerator. -/
theorem factor_mul_remainder (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) (s t : GaussianInt) :
    (GaussianInt.toGaussian s - GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value) *
        GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) =
      GaussianInt.toGaussian (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator) := by
  have nextClears :
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value * GaussianInt.toGaussian
        (GaussianInt.Division.Nearest.remainder fraction) =
        GaussianInt.toGaussian fraction.denominator :=
    (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value_mul_denominator
  calc
    (GaussianInt.toGaussian s - GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value) *
          GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) =
        GaussianInt.toGaussian s * GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) -
          GaussianInt.toGaussian t *
            ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value *
              GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction)) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im] <;>
        ring1
    _ = GaussianInt.toGaussian s * GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder fraction) -
          GaussianInt.toGaussian t * GaussianInt.toGaussian fraction.denominator := by
      rw [nextClears]
    _ = GaussianInt.toGaussian (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator) := by
      rw [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul]

/-- Clearing a Lakein factor multiplies its rational quadrance by the remainder norm to give an exact Gaussian-integer
numerator norm. -/
theorem factor_normSq_mul_remainder_norm
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (s t : GaussianInt) :
    Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian s -
            GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) *
        (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) =
      (GaussianInt.normNat (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator) :
        Fraction.Rational) := by
  rw [← GaussianInt.normSq_toGaussian, ← Gaussian.Norm.Basic.normSq_mul,
    factor_mul_remainder, GaussianInt.normSq_toGaussian]

/-- Square-root-free cancellation after clearing the nonzero Euclidean
remainder. -/
theorem one_le_factor_normSq_of_remainder_norm_le
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (s t : GaussianInt)
    (clearedExterior :
      GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) ≤
        GaussianInt.normNat (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator)) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq
      (GaussianInt.toGaussian s -
        GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) := by
  have remainderPositive :
      (0 : Fraction.Rational) < (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) :
        Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (GaussianInt.normNat_pos nonterminal)
  have castExterior :
      (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) ≤
        (GaussianInt.normNat (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator) :
          Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct clearedExterior
  have productExterior :
      1 * (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) ≤
        Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian s -
              GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) *
          (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) := by
    calc
      1 * (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) =
          (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) := by ring1
      _ ≤ (GaussianInt.normNat
            (s * GaussianInt.Division.Nearest.remainder fraction - t * fraction.denominator) :
              Fraction.Rational) := castExterior
      _ = Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian s -
              GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value) *
          (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction) : Fraction.Rational) :=
        (factor_normSq_mul_remainder_norm fraction nonterminal s t).symm
  exact Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    productExterior remainderPositive

/-- Lakein's second-kind comparison, conditional only on the finite
quadrance-five denominator certificate.  All other branches are discharged
by complete-denominator growth and the explicit unit/diagonal geometry. -/
theorem Stage.atLeastAsGoodAs_of_generated_of_normFiveDenominatorSafe
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (generated : Generated source stage)
    (exceptionalSafe : NormFiveDenominatorSafe stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (competitor : GaussianInt.Pair.Basic.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      GaussianInt.normNat competitor.denominator < GaussianInt.normNat stage.current.denominator) :
    Best.Error.AtLeastAsGoodAs source.value stage.current competitor := by
  let s := GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor
  let t := GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor
  have denominatorDecomposition :
      s * stage.current.denominator + t * stage.previous.denominator =
        competitor.denominator := by
    dsimp only [s, t]
    exact GaussianInt.Pair.Basis.competitor_denominator_decomposition stage.unitDeterminant
  have coefficientDenominatorSmaller :
      GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) <
        GaussianInt.normNat stage.current.denominator := by
    rw [denominatorDecomposition]
    exact denominatorSmaller
  have completeGrowth :=
    completeDenominatorGrowth_of_generated generated nonterminal
  by_cases large :
      (4 : Fraction.Rational) *
            (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
          (GaussianInt.normNat t : Fraction.Rational) *
            Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal)
  · exact stage.atLeastAsGoodAs_of_large_previousCoefficient nonterminal
      competitor competitorDenominatorNonzero denominatorSmaller (by
        change (4 : Fraction.Rational) *
              (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
            (GaussianInt.normNat t : Fraction.Rational) *
              Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal)
        exact large)
  · have tSmall : GaussianInt.normNat t < 4 :=
      previousCoefficient_normNat_lt_four_of_not_large stage nonterminal
        competitor completeGrowth (by
          change ¬ ((4 : Fraction.Rational) *
                (GaussianInt.normNat stage.current.denominator : Fraction.Rational) <
              (GaussianInt.normNat t : Fraction.Rational) *
                Data.Gaussian.Norm.Basic.normSq (stage.completeDenominator nonterminal))
          exact large)
    have tCases := GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_of_lt_four t tSmall
    have factorExterior :
        1 ≤ Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian s -
            GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
              nonterminal).value) := by
      rcases tCases with tZero | tUnit | tDiagonal
      · have tIsZero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero tZero
        have denominatorAsMultiple :
            competitor.denominator = s * stage.current.denominator := by
          rw [← denominatorDecomposition, tIsZero,
            GaussianInt.zero_mul,
            GaussianInt.add_zero]
        have multipleNormSmaller :
            GaussianInt.normNat s * GaussianInt.normNat stage.current.denominator <
              GaussianInt.normNat stage.current.denominator := by
          rw [← GaussianInt.Embedding.normNat_mul, ← denominatorAsMultiple]
          exact denominatorSmaller
        have sZero : GaussianInt.normNat s = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro sPositive
          have oneLeS : 1 ≤ GaussianInt.normNat s := sPositive
          have currentLeMultiple :
              GaussianInt.normNat stage.current.denominator ≤
                GaussianInt.normNat s * GaussianInt.normNat stage.current.denominator := by
            have scaled := Nat.mul_le_mul_right
              (GaussianInt.normNat stage.current.denominator) oneLeS
            rw [Nat.one_mul] at scaled
            exact scaled
          exact (not_lt_of_ge currentLeMultiple multipleNormSmaller)
        have sIsZero := GaussianInt.Norm.Basic.eq_zero_of_normNat_eq_zero sZero
        have denominatorZero : competitor.denominator = 0 := by
          rw [denominatorAsMultiple, sIsZero,
            GaussianInt.zero_mul]
        exact (competitorDenominatorNonzero denominatorZero).elim
      · exact one_le_factor_normSq_of_unit_previousCoefficient generated
          nonterminal s t tUnit coefficientDenominatorSmaller
      · have sSmall :=
          currentCoefficient_normNat_lt_six_of_diagonal_previous s t
            stage.current.denominator stage.previous.denominator
            (stage_denominatorGrowth generated) tDiagonal
            coefficientDenominatorSmaller
        by_cases sFive : GaussianInt.normNat s = 5
        · have notShorter := exceptionalSafe s t sFive tDiagonal
          exact (not_lt_of_ge notShorter coefficientDenominatorSmaller).elim
        · exact
            one_le_factor_normSq_of_diagonal_previousCoefficient_of_not_five
              generated nonterminal s t tDiagonal sSmall sFive
              coefficientDenominatorSmaller
    exact stage.atLeastAsGoodAs_of_one_le_factor_normSq nonterminal competitor
      (by
        change 1 ≤ Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian s -
            GaussianInt.toGaussian t * (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
              nonterminal).value)
        exact factorExterior)

end Purelib.NumberTheory.Approximation.Hurwitz.Geometry

end
