module

import Purelib.Logic.Decidable
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
import Purelib.Data.Int.Order
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Trace
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Nearest
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Hermitian.Binary
import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.Search
public import Purelib.NumberTheory.Approximation.Hurwitz.Geometry

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

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

open Purelib.NumberTheory.Approximation.Hurwitz

section
@[expose] public section

/-!
# The finite Lakein inequality for Hurwitz convergents

This module closes the last exceptional coefficient case left by the elementary
Hurwitz-square geometry.  The normalized adjacent-denominator ratio is an
explicit Gaussian rational.  Its finite laws of succession keep it in
`[-3/4, 3/4]²`; that coordinate certificate excludes every quadrance-five
current coefficient paired with a diagonal previous coefficient.
-/

section

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.Stage

/-- The preceding continuant denominator divided by the current one.  This is
formed only from displayed Gaussian integers. -/
def denominatorRatio {source : GaussianInt.Fraction}
  (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) :
    Gaussian.Basic.Canonical :=
  GaussianInt.toGaussian stage.previous.denominator *
    (GaussianInt.toGaussian stage.current.denominator)⁻¹

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.Stage

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- The initial Hurwitz stage has denominator ratio zero. -/
@[simp] theorem firstStage_denominatorRatio (source :
  GaussianInt.Fraction) :
    Stage.denominatorRatio (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) = 0 := by
  unfold Stage.denominatorRatio Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage
  simp only [GaussianInt.toGaussian_zero, GaussianInt.toGaussian_one,
    Gaussian.Field.inv_eq,
    Gaussian.Field.inv_one_direct,
    Gaussian.Basic.zero_mul, -eq_self, -iff_self]
  rfl

/-- The finite coordinate region needed for Lakein's exceptional coefficient
case. -/
def DenominatorRatioInLakeinSquare {source :
  GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) : Prop :=
  -(3 / 4 : Fraction.Rational) ≤ (Stage.denominatorRatio stage).re ∧
    (Stage.denominatorRatio stage).re ≤ (3 / 4 : Fraction.Rational) ∧
    -(3 / 4 : Fraction.Rational) ≤ (Stage.denominatorRatio stage).im ∧
    (Stage.denominatorRatio stage).im ≤ (3 / 4 : Fraction.Rational)

/-- The current denominator of a generated Hurwitz stage is nonzero. -/
theorem current_denominator_ne_zero_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage) :
    stage.current.denominator ≠ 0 := by
  intro currentZero
  have growth := Hurwitz.Geometry.stage_denominatorGrowth generated
  rw [currentZero] at growth
  change GaussianInt.normNat stage.previous.denominator < 0 at growth
  omega

/-- Multiplying the denominator ratio by its nonzero current denominator recovers the previous denominator. -/
theorem denominatorRatio_mul_current {source :
  GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) (currentNonzero : stage.current.denominator ≠ 0)
      :
    (Stage.denominatorRatio stage) * GaussianInt.toGaussian stage.current.denominator =
      GaussianInt.toGaussian stage.previous.denominator := by
  have currentGaussianNonzero :
      GaussianInt.toGaussian stage.current.denominator ≠ 0 := by
    intro currentZero
    exact currentNonzero (GaussianInt.toGaussian_eq_zero.mp currentZero)
  dsimp only [Stage.denominatorRatio]
  calc
    (GaussianInt.toGaussian stage.previous.denominator *
          (GaussianInt.toGaussian stage.current.denominator)⁻¹) *
        GaussianInt.toGaussian stage.current.denominator =
      GaussianInt.toGaussian stage.previous.denominator *
        ((GaussianInt.toGaussian stage.current.denominator)⁻¹ *
          GaussianInt.toGaussian stage.current.denominator) := by
        rw [Gaussian.Basic.mul_assoc]
    _ = GaussianInt.toGaussian stage.previous.denominator * 1 := by
      rw [Gaussian.Field.inv_eq,
        Gaussian.Field.inv_mul _
          currentGaussianNonzero]
    _ = GaussianInt.toGaussian stage.previous.denominator :=
      Gaussian.Basic.mul_one _

/-- The denominator ratio of a generated Hurwitz stage lies strictly inside the unit disk. -/
theorem denominatorRatio_normSq_lt_one_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage) :
    Data.Gaussian.Norm.Basic.normSq (Stage.denominatorRatio stage) < 1 := by
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  have currentGaussianNonzero :
      GaussianInt.toGaussian stage.current.denominator ≠ 0 := by
    intro currentZero
    exact currentNonzero (GaussianInt.toGaussian_eq_zero.mp currentZero)
  have currentPositive :
      0 < Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.current.denominator) :=
    Gaussian.Norm.Basic.normSq_pos currentGaussianNonzero
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.current.denominator)) _ currentPositive
  calc
    Data.Gaussian.Norm.Basic.normSq (Stage.denominatorRatio stage) *
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.current.denominator) =
        Data.Gaussian.Norm.Basic.normSq
          ((Stage.denominatorRatio stage) *
            GaussianInt.toGaussian stage.current.denominator) := by
      rw [Gaussian.Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.previous.denominator) := by
      rw [denominatorRatio_mul_current stage currentNonzero]
    _ = (GaussianInt.normNat stage.previous.denominator : Fraction.Rational) :=
      GaussianInt.normSq_toGaussian _
    _ < (GaussianInt.normNat stage.current.denominator : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_lt_direct
        (Hurwitz.Geometry.stage_denominatorGrowth generated)
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.current.denominator) :=
      (GaussianInt.normSq_toGaussian _).symm
    _ = 1 * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian stage.current.denominator) := by ring1

/-- Advancing the trace applies the usual finite backward-continued-fraction
map to the displayed denominator ratio. -/
theorem advanceStage_denominatorRatio {source :
  GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) (generated : Hurwitz.Geometry.Generated source
      stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) :
    Stage.denominatorRatio
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal) =
      (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        stage.quotient nonterminal)) +
        (Stage.denominatorRatio stage))⁻¹ := by
  let advanced := Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal
  let nextDigit := GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
    nonterminal)
  let currentValue := GaussianInt.toGaussian stage.current.denominator
  let advancedValue := GaussianInt.toGaussian advanced.current.denominator
  let divisor := GaussianInt.toGaussian nextDigit + (Stage.denominatorRatio stage)
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  have advancedGenerated : Hurwitz.Geometry.Generated source advanced :=
    Hurwitz.Geometry.Generated.advance generated nonterminal
  have advancedNonzero :=
    current_denominator_ne_zero_of_generated advancedGenerated
  have advancedGaussianNonzero : advancedValue ≠ 0 := by
    intro advancedZero
    exact advancedNonzero (GaussianInt.toGaussian_eq_zero.mp advancedZero)
  have divisorMulCurrent : divisor * currentValue = advancedValue := by
    dsimp only [divisor, currentValue, advancedValue, advanced, nextDigit]
    change
      (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        stage.quotient nonterminal)) +
          (Stage.denominatorRatio stage)) *
          GaussianInt.toGaussian stage.current.denominator =
        GaussianInt.toGaussian
          (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
            nonterminal) *
            stage.current.denominator + stage.previous.denominator)
    rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  have divisorNonzero : divisor ≠ 0 := by
    intro divisorZero
    have zeroAdvanced : advancedValue = 0 := by
      rw [← divisorMulCurrent, divisorZero,
        Gaussian.Basic.zero_mul]
    exact advancedGaussianNonzero zeroAdvanced
  apply Gaussian.Field.mul_right_cancel_of_ne
    advancedGaussianNonzero
  calc
    Stage.denominatorRatio advanced * advancedValue =
        GaussianInt.toGaussian advanced.previous.denominator :=
      denominatorRatio_mul_current advanced advancedNonzero
    _ = currentValue := rfl
    _ = 1 * currentValue := by
      rw [_root_.one_mul]
    _ = (divisor⁻¹ * divisor) * currentValue := by
      rw [Gaussian.Field.inv_eq,
        Gaussian.Field.inv_mul _ divisorNonzero]
    _ = divisor⁻¹ * (divisor * currentValue) := by
      rw [Gaussian.Basic.mul_assoc]
    _ = divisor⁻¹ * advancedValue := by rw [divisorMulCurrent]
    _ = (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
      stage.quotient nonterminal)) +
          (Stage.denominatorRatio stage))⁻¹ * advancedValue := rfl

/-- Twice a rational value strictly below one half is strictly below one. -/
private theorem twice_lt_one_of_lt_half {value :
  Fraction.Rational}
    (upper : value < 1 / 2) : 2 * value < 1 := by
  have scaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (show (0 : Fraction.Rational) < 2 by decide) upper
  calc
    2 * value < 2 * (1 / 2 : Fraction.Rational) := scaled
    _ = 1 := by decide

/-- Multiplication by one half cancels a doubled rational value. -/
private theorem half_two_mul (value : Fraction.Rational) :
    (1 / 2 : Fraction.Rational) * (2 * value) = value := by
  calc
    (1 / 2 : Fraction.Rational) * (2 * value) =
        ((1 / 2 : Fraction.Rational) + 1 / 2) * value := by ring1
    _ = 1 * value := by rw [show
      (1 / 2 : Fraction.Rational) + 1 / 2 = 1 by decide]
    _ = value := _root_.one_mul value

/-- The half-open tie convention makes the exterior test at `1` strict.
This is the one strict edge needed by the finite succession table. -/
theorem one_lt_next_sub_one_normSq (fraction :
  GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    1 < Data.Gaussian.Norm.Basic.normSq ((Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value - 1) := by
  let rho := GaussianInt.Division.Nearest.residual fraction
  let nextValue := (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nonterminal
  have rhoPositive : 0 < Data.Gaussian.Norm.Basic.normSq rho := Gaussian.Norm.Basic.normSq_pos rhoNonzero
  have reciprocal : nextValue * rho = 1 := by
    dsimp only [nextValue, rho]
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ rhoNonzero]
  have factorIdentity : (nextValue - 1) * rho = 1 - rho := by
    calc
      (nextValue - 1) * rho = nextValue * rho - 1 * rho := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = 1 - rho := by
        rw [reciprocal, _root_.one_mul]
  have rhoSquare := GaussianInt.Nearest.remainder_mem fraction.value
  have gapPositive : 0 < 1 - 2 * rho.re := by
    exact Fraction.Order.Arithmetic.sub_pos_direct
      (twice_lt_one_of_lt_half rhoSquare.2.1)
  have residualStrict : Data.Gaussian.Norm.Basic.normSq rho < Data.Gaussian.Norm.Basic.normSq (1 - rho) := by
    have shifted :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct
        gapPositive (Data.Gaussian.Norm.Basic.normSq rho)
    calc
      Data.Gaussian.Norm.Basic.normSq rho = Data.Gaussian.Norm.Basic.normSq rho + 0 := by ring1
      _ < Data.Gaussian.Norm.Basic.normSq rho + (1 - 2 * rho.re) := shifted
      _ = Data.Gaussian.Norm.Basic.normSq (1 - rho) := by
        simp only [Data.Gaussian.Norm.Basic.normSq,
          Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.one_re,
          Gaussian.Basic.one_im]
        ring1
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Data.Gaussian.Norm.Basic.normSq rho) _ rhoPositive
  calc
    1 * Data.Gaussian.Norm.Basic.normSq rho = Data.Gaussian.Norm.Basic.normSq rho := by ring1
    _ < Data.Gaussian.Norm.Basic.normSq (1 - rho) := residualStrict
    _ = Data.Gaussian.Norm.Basic.normSq ((nextValue - 1) * rho) := by rw [factorIdentity]
    _ = Data.Gaussian.Norm.Basic.normSq (nextValue - 1) * Data.Gaussian.Norm.Basic.normSq rho :=
      Gaussian.Norm.Basic.normSq_mul _ _

/-- After the digit 1+i, the following nonterminal complete quotient has real coordinate at least -1/2.

The exterior inequality at i becomes a lower bound on the real coordinate after division by the positive residual
quadrance. -/
private theorem next_value_real_lower_of_one_add_i_digit
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Fraction.Rational) ≤
      (Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
        nonterminal) nextNonterminal).value.re := by
  let current := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next current nextNonterminal
  let rho := GaussianInt.Division.Nearest.residual current
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nextNonterminal
  have rhoPositive : 0 < Data.Gaussian.Norm.Basic.normSq rho := Gaussian.Norm.Basic.normSq_pos rhoNonzero
  have currentDecomposition :
      current.value = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
    calc
      current.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) +
        GaussianInt.Division.Nearest.residual current :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual current
      _ = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
        rw [digitValue]
  have exterior := Hurwitz.Geometry.one_le_next_sub_unit_normSq fraction nonterminal
    (unit := GaussianInt.Norm.Small.imaginaryUnit) (Or.inr (Or.inr (Or.inl rfl)))
  have scaledLower : -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq rho ≤ rho.re := by
    rw [currentDecomposition] at exterior
    simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.Norm.Small.imaginaryUnit, GaussianInt.toGaussian,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Ring.IntCast.cast_zero, Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at exterior
    have doubled : -Data.Gaussian.Norm.Basic.normSq rho ≤ 2 * rho.re := by
      have shifted :=
        Fraction.Order.Arithmetic.add_le_add_right_direct exterior (-1)
      have nonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.re := by
        calc
          0 = (1 : Fraction.Rational) + -1 := by ring1
          _ ≤ ((1 + rho.re - 0) ^ 2 +
                (1 + rho.im - 1) ^ 2) + -1 := shifted
          _ = Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.re := by
            dsimp only [Data.Gaussian.Norm.Basic.normSq]
            ring1
      have translated :=
        Fraction.Order.Arithmetic.add_le_add_right_direct
          nonnegative (-Data.Gaussian.Norm.Basic.normSq rho)
      calc
        -Data.Gaussian.Norm.Basic.normSq rho = 0 + -Data.Gaussian.Norm.Basic.normSq rho := by ring1
        _ ≤ (Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.re) + -Data.Gaussian.Norm.Basic.normSq rho :=
          translated
        _ = 2 * rho.re := by ring1
    have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq rho =
          (1 / 2 : Fraction.Rational) * (-Data.Gaussian.Norm.Basic.normSq rho) := by ring1
      _ ≤ (1 / 2 : Fraction.Rational) * (2 * rho.re) := scaled
      _ = rho.re := half_two_mul rho.re
  have divided :=
    (Fraction.Order.Field.le_div_iff_pos rhoPositive).2 scaledLower
  rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq]
  change -(1 / 2 : Fraction.Rational) ≤ rho.re / Data.Gaussian.Norm.Basic.normSq rho
  exact divided

/-- After the digit 1+i, the following nonterminal complete quotient has imaginary coordinate strictly below 1/2.

The strict exterior inequality at 1 preserves the half-open rounding convention through inversion. -/
private theorem next_value_imaginary_upper_of_one_add_i_digit
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, 1⟩) :
    (Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) nextNonterminal).value.im <
      (1 / 2 : Fraction.Rational) := by
  let current := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next current nextNonterminal
  let rho := GaussianInt.Division.Nearest.residual current
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nextNonterminal
  have rhoPositive : 0 < Data.Gaussian.Norm.Basic.normSq rho := Gaussian.Norm.Basic.normSq_pos rhoNonzero
  have currentDecomposition :
      current.value = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
    calc
      current.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) +
        GaussianInt.Division.Nearest.residual current :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual current
      _ = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + rho := by
        rw [digitValue]
  have exterior := one_lt_next_sub_one_normSq fraction nonterminal
  have scaledUpper : -rho.im < (1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq rho := by
    rw [currentDecomposition] at exterior
    simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.one_re,
      Gaussian.Basic.one_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at exterior
    have shifted :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct exterior (-1)
    have positive : 0 < Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.im := by
      calc
        0 = (1 : Fraction.Rational) + -1 := by ring1
        _ < ((1 + rho.re - 1) ^ 2 +
              (1 + rho.im - 0) ^ 2) + -1 := shifted
        _ = Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.im := by
          dsimp only [Data.Gaussian.Norm.Basic.normSq]
          ring1
    have translated :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        positive (-(2 * rho.im))
    have doubled : -(2 * rho.im) < Data.Gaussian.Norm.Basic.normSq rho := by
      calc
        -(2 * rho.im) = 0 + -(2 * rho.im) := by ring1
        _ < (Data.Gaussian.Norm.Basic.normSq rho + 2 * rho.im) + -(2 * rho.im) := translated
        _ = Data.Gaussian.Norm.Basic.normSq rho := by ring1
    have scaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Fraction.Rational) < 1 / 2 by decide) doubled
    calc
      -rho.im = (1 / 2 : Fraction.Rational) * (2 * (-rho.im)) := by
        rw [half_two_mul]
      _ = (1 / 2 : Fraction.Rational) * (-(2 * rho.im)) := by
        congr 1
        ring1
      _ < (1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq rho := scaled
  have divided :=
    (Fraction.Order.Field.div_lt_iff_pos rhoPositive).2 scaledUpper
  rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq]
  change (-rho.im) / Data.Gaussian.Norm.Basic.normSq rho < (1 / 2 : Fraction.Rational)
  exact divided

/-- A digit `1+i` can only be followed by a digit in the southeast
quadrant.  The statement includes the deterministic boundary convention. -/
theorem successor_signs_of_one_add_i
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, 1⟩) :
    0 ≤ (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal)).re ∧
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal)).im ≤ 0 := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next
    fraction nonterminal) nextNonterminal
  let followingDigit := GaussianInt.Division.Nearest.digit following
  let followingResidual := GaussianInt.Division.Nearest.residual following
  have decomposition :
      following.value = GaussianInt.toGaussian followingDigit + followingResidual :=
    GaussianInt.Division.Nearest.value_eq_digit_add_residual following
  have residualSquare := GaussianInt.Nearest.remainder_mem following.value
  constructor
  · apply Int.Order.le_of_not_lt
    intro negative
    change followingDigit.re < 0 at negative
    have digitAtMostMinusOne : followingDigit.re ≤ -1 := by omega
    have castDigitAtMostMinusOne :
        (followingDigit.re : Fraction.Rational) ≤ -1 :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        digitAtMostMinusOne
    have valueStrict : following.value.re < -(1 / 2 : Fraction.Rational) := by
      have first := Fraction.Order.Arithmetic.add_le_add_right_direct
        castDigitAtMostMinusOne followingResidual.re
      have second := Fraction.Order.Arithmetic.add_lt_add_left_direct
        residualSquare.2.1 (-1)
      have shifted := first.trans_lt second
      calc
        following.value.re =
            (followingDigit.re : Fraction.Rational) + followingResidual.re := by
          simpa only [Gaussian.Basic.add_re, GaussianInt.toGaussian,
            ← Rat.Fraction.Cast.intCast_eq_fromInt] using congrArg Gaussian.Basic.re decomposition
        _ < (-1 : Fraction.Rational) + 1 / 2 := shifted
        _ = -(1 / 2 : Fraction.Rational) := by decide
    exact (not_lt_of_ge
      (next_value_real_lower_of_one_add_i_digit fraction nonterminal
        nextNonterminal digitValue) valueStrict)
  · apply Int.Order.le_of_not_lt
    intro positive
    change 0 < followingDigit.im at positive
    have oneLeDigit : 1 ≤ followingDigit.im := by omega
    have oneLeCast : (1 : Fraction.Rational) ≤
        (followingDigit.im : Fraction.Rational) :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        oneLeDigit
    have valueLower : (1 / 2 : Fraction.Rational) ≤ following.value.im := by
      have first := Fraction.Order.Arithmetic.add_le_add_right_direct
        oneLeCast followingResidual.im
      have second := Fraction.Order.Arithmetic.add_le_add_right_direct
        residualSquare.2.2.1 1
      have shifted :
          (1 : Fraction.Rational) + -(1 / 2 : Fraction.Rational) ≤
            (followingDigit.im : Fraction.Rational) + followingResidual.im := by
        calc
          (1 : Fraction.Rational) + -(1 / 2 : Fraction.Rational) =
              -(1 / 2 : Fraction.Rational) + 1 := by ring1
          _ ≤ followingResidual.im + 1 := second
          _ = 1 + followingResidual.im := by ring1
          _ ≤ (followingDigit.im : Fraction.Rational) + followingResidual.im := first
      calc
        (1 / 2 : Fraction.Rational) = 1 + -(1 / 2 : Fraction.Rational) := by decide
        _ ≤ (followingDigit.im : Fraction.Rational) + followingResidual.im := shifted
        _ = following.value.im :=
          by simpa only [Gaussian.Basic.add_im, GaussianInt.toGaussian,
            ← Rat.Fraction.Cast.intCast_eq_fromInt] using (congrArg Gaussian.Basic.im decomposition).symm
    exact (not_le_of_gt
      (next_value_imaginary_upper_of_one_add_i_digit fraction nonterminal
        nextNonterminal digitValue) valueLower)

/-- Clearing the following complete quotient turns a unit-disc exterior
condition into a polynomial inequality in the following residual.  This is
the common finite calculation behind the exceptional successor exclusions. -/
theorem successor_exterior_cleared
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (unit : GaussianInt) (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit) :
    Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal).value ≤
      Data.Gaussian.Norm.Basic.normSq
        ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
          fraction nonterminal)) - GaussianInt.toGaussian unit) *
            (Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
              nonterminal) nextNonterminal).value + 1) := by
  let current := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next current nextNonterminal
  let rho := GaussianInt.Division.Nearest.residual current
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nextNonterminal
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have productZero := congrArg (fun value => value * rho) followingZero
    rw [Gaussian.Basic.zero_mul] at productZero
    have reciprocal : following.value * rho = 1 := by
      dsimp only [following, current, rho]
      rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
        Gaussian.Field.inv_mul _ rhoNonzero]
    rw [reciprocal] at productZero
    exact (show (1 : Gaussian.Basic.Canonical) ≠ 0 by decide) productZero
  have followingPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value :=
    Gaussian.Norm.Basic.normSq_pos followingNonzero
  have exterior :
      1 ≤ Data.Gaussian.Norm.Basic.normSq (current.value - GaussianInt.toGaussian unit) := by
    dsimp only [current]
    exact Hurwitz.Geometry.one_le_next_sub_unit_normSq fraction nonterminal unitProperty
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      exterior followingPositive.le
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, current, rho]
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ rhoNonzero]
  have reciprocalReordered : rho * following.value = 1 := by
    calc
      rho * following.value = following.value * rho :=
        Gaussian.Basic.mul_comm _ _
      _ = 1 := reciprocal
  have factorIdentity :
      (current.value - GaussianInt.toGaussian unit) * following.value =
        (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
          following.value + 1 := by
    rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual current]
    calc
      (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) + GaussianInt.Division.Nearest.residual
        current - GaussianInt.toGaussian unit) *
            following.value =
          (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
            following.value +
            GaussianInt.Division.Nearest.residual current * following.value := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
          ring1
      _ = (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
        following.value +
          1 := by
        change (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
            following.value + rho * following.value = _
        rw [reciprocalReordered]
  change Data.Gaussian.Norm.Basic.normSq following.value ≤
    Data.Gaussian.Norm.Basic.normSq
      ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
        following.value + 1)
  calc
    Data.Gaussian.Norm.Basic.normSq following.value = 1 * Data.Gaussian.Norm.Basic.normSq following.value := by
      ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq (current.value - GaussianInt.toGaussian unit) *
          Data.Gaussian.Norm.Basic.normSq following.value := scaled
    _ = Data.Gaussian.Norm.Basic.normSq ((current.value - GaussianInt.toGaussian unit) * following.value) := by
      rw [Gaussian.Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq
        ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - GaussianInt.toGaussian unit) *
          following.value + 1) :=
      by rw [factorIdentity]

/-- The same clearing calculation retains the strict exterior inequality at
the positive real unit. -/
theorem successor_strict_exterior_cleared
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq (Data.ComplexContinuedFraction.Hurwitz.Step.next
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal).value <
      Data.Gaussian.Norm.Basic.normSq
        ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
          fraction nonterminal)) - 1) *
            (Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
              nonterminal) nextNonterminal).value + 1) := by
  let current := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next current nextNonterminal
  let rho := GaussianInt.Division.Nearest.residual current
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nextNonterminal
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have productZero := congrArg (fun value => value * rho) followingZero
    rw [Gaussian.Basic.zero_mul] at productZero
    have reciprocal : following.value * rho = 1 := by
      dsimp only [following, current, rho]
      rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
        Gaussian.Field.inv_mul _ rhoNonzero]
    rw [reciprocal] at productZero
    exact (show (1 : Gaussian.Basic.Canonical) ≠ 0 by decide) productZero
  have followingPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value :=
    Gaussian.Norm.Basic.normSq_pos followingNonzero
  have exterior : 1 < Data.Gaussian.Norm.Basic.normSq (current.value - 1) := by
    dsimp only [current]
    exact one_lt_next_sub_one_normSq fraction nonterminal
  have scaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      exterior followingPositive
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, current, rho]
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ rhoNonzero]
  have reciprocalReordered : rho * following.value = 1 := by
    calc
      rho * following.value = following.value * rho :=
        Gaussian.Basic.mul_comm _ _
      _ = 1 := reciprocal
  have factorIdentity :
      (current.value - 1) * following.value =
        (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) * following.value + 1 := by
    rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual current]
    calc
      (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) + GaussianInt.Division.Nearest.residual
        current - 1) *
            following.value =
          (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) * following.value +
            GaussianInt.Division.Nearest.residual current * following.value := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im] <;>
          ring1
      _ = (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) * following.value + 1 := by
        change (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) * following.value +
            rho * following.value = _
        rw [reciprocalReordered]
  change Data.Gaussian.Norm.Basic.normSq following.value <
    Data.Gaussian.Norm.Basic.normSq ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) *
      following.value + 1)
  calc
    Data.Gaussian.Norm.Basic.normSq following.value = 1 * Data.Gaussian.Norm.Basic.normSq following.value := by
      ring1
    _ < Data.Gaussian.Norm.Basic.normSq (current.value - 1) * Data.Gaussian.Norm.Basic.normSq following.value :=
      scaled
    _ = Data.Gaussian.Norm.Basic.normSq ((current.value - 1) * following.value) := by
      rw [Gaussian.Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq
        ((GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit current) - 1) * following.value + 1) := by
      rw [factorIdentity]

/-- On the rational interval [1/2,3/2], one quarter plus the square is strictly less than twice the value.

Centering at one bounds the displacement square by one quarter and gives a uniform negative difference. -/
private theorem quarter_add_square_lt_twice_of_half_interval
    (value : Fraction.Rational) (lower : (1 / 2 : Fraction.Rational) ≤ value)
    (upper : value ≤ (3 / 2 : Fraction.Rational)) :
    (1 / 2 : Fraction.Rational) ^ 2 + value ^ 2 < 2 * value := by
  let displacement := value - 1
  have displacementLower : -(1 / 2 : Fraction.Rational) ≤ displacement := by
    calc
      -(1 / 2 : Fraction.Rational) = (1 / 2 : Fraction.Rational) - 1 := by decide
      _ ≤ value - 1 := Fraction.Order.Arithmetic.sub_le_sub_right_direct lower 1
      _ = displacement := rfl
  have displacementUpper : displacement ≤ (1 / 2 : Fraction.Rational) := by
    calc
      displacement = value - 1 := rfl
      _ ≤ (3 / 2 : Fraction.Rational) - 1 := Fraction.Order.Arithmetic.sub_le_sub_right_direct upper 1
      _ = 1 / 2 := by decide
  have leftFactorNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) - displacement :=
    Fraction.Order.Arithmetic.sub_nonneg_direct displacementUpper
  have rightFactorNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) + displacement := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      displacementLower (1 / 2 : Fraction.Rational)
    calc
      0 = -(1 / 2 : Fraction.Rational) + 1 / 2 := by ring1
      _ ≤ displacement + 1 / 2 := shifted
      _ = 1 / 2 + displacement := by ring1
  have productNonnegative :
      0 ≤ ((1 / 2 : Fraction.Rational) - displacement) *
        ((1 / 2 : Fraction.Rational) + displacement) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      leftFactorNonnegative rightFactorNonnegative
  have displacementSquareUpper :
      displacement ^ 2 ≤ (1 / 4 : Fraction.Rational) := by
    have gap : 0 ≤ (1 / 4 : Fraction.Rational) - displacement ^ 2 := by
      calc
        0 ≤ ((1 / 2 : Fraction.Rational) - displacement) *
            ((1 / 2 : Fraction.Rational) + displacement) := productNonnegative
        _ = (1 / 2 : Fraction.Rational) * (1 / 2) - displacement ^ 2 := by
          ring1
        _ = (1 / 4 : Fraction.Rational) - displacement ^ 2 := by
          rw [show (1 / 2 : Fraction.Rational) * (1 / 2) = 1 / 4 by decide]
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct gap
  have differenceUpper :
      (1 / 2 : Fraction.Rational) ^ 2 + value ^ 2 - 2 * value ≤
        -(1 / 2 : Fraction.Rational) := by
    calc
      (1 / 2 : Fraction.Rational) ^ 2 + value ^ 2 - 2 * value =
          displacement ^ 2 - (1 - (1 / 2 : Fraction.Rational) ^ 2) := by
        dsimp only [displacement]
        ring1
      _ = displacement ^ 2 - 3 / 4 := by
        rw [show (1 : Fraction.Rational) - (1 / 2) ^ 2 = 3 / 4 by decide]
      _ ≤ (1 / 4 : Fraction.Rational) - 3 / 4 :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct
          displacementSquareUpper (3 / 4 : Fraction.Rational)
      _ = -(1 / 2 : Fraction.Rational) := by decide
  have differenceNegative :
      (1 / 2 : Fraction.Rational) ^ 2 + value ^ 2 - 2 * value < 0 :=
    differenceUpper.trans_lt (show -(1 / 2 : Fraction.Rational) < 0 by decide)
  exact Fraction.Order.Arithmetic.lt_of_sub_neg_direct differenceNegative

/-- A residual can be recovered from the following displayed quotient by
one finite inversion; no infinite tail is involved. -/
theorem residual_eq_next_value_inv (fraction :
  GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    GaussianInt.Division.Nearest.residual fraction = (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal).value⁻¹ := by
  let rho := GaussianInt.Division.Nearest.residual fraction
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  have rhoNonzero : rho ≠ 0 := GaussianInt.Division.Nearest.residual_ne_zero nonterminal
  have reciprocal : following.value * rho = 1 := by
    dsimp only [following, rho]
    rw [Data.ComplexContinuedFraction.Hurwitz.Step.next_value, Gaussian.Field.inv_eq,
      Gaussian.Field.inv_mul _ rhoNonzero]
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    rw [followingZero, Gaussian.Basic.zero_mul] at reciprocal
    exact (show (1 : Gaussian.Basic.Canonical) ≠ 0 by decide) reciprocal.symm
  apply Gaussian.Field.mul_right_cancel_of_ne
    followingNonzero
  calc
    GaussianInt.Division.Nearest.residual fraction * following.value = following.value * rho := by
      dsimp only [rho]
      exact Gaussian.Basic.mul_comm _ _
    _ = 1 := reciprocal
    _ = following.value⁻¹ * following.value := by
      rw [Gaussian.Field.inv_eq,
        Gaussian.Field.inv_mul _ followingNonzero]
    _ = (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal).value⁻¹ * following.value := rfl

/-- A noninitial digit 1+i has residual real coordinate strictly above -1/2.

Equality at the lower edge would force the preceding residual outside its selected fundamental square. -/
private theorem next_residual_real_lower_strict_of_one_add_i
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Fraction.Rational) < (GaussianInt.Division.Nearest.residual
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)).re := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let sigma := GaussianInt.Division.Nearest.residual following
  have sigmaSquare := GaussianInt.Nearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.re = -(1 / 2 : Fraction.Rational) :=
    le_antisymm upper sigmaSquare.1
  have decomposition :
      following.value = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have realValue : following.value.re = (1 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.re = 1 + -(1 / 2 : Fraction.Rational) := component
      _ = 1 / 2 := by decide
  have imaginaryLower : (1 / 2 : Fraction.Rational) ≤ following.value.im := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.2.1 1
    calc
      (1 / 2 : Fraction.Rational) = -(1 / 2 : Fraction.Rational) + 1 := by decide
      _ ≤ sigma.im + 1 := shifted
      _ = 1 + sigma.im := by ring1
      _ = following.value.im := component.symm
  have imaginaryUpper : following.value.im ≤ (3 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.2.2.le 1
    calc
      following.value.im = 1 + sigma.im := component
      _ = sigma.im + 1 := by ring1
      _ ≤ (1 / 2 : Fraction.Rational) + 1 := shifted
      _ = 3 / 2 := by decide
  have normLess : Data.Gaussian.Norm.Basic.normSq following.value < 2 * following.value.im := by
    rw [Data.Gaussian.Norm.Basic.normSq, realValue]
    exact quarter_add_square_lt_twice_of_half_interval following.value.im
      imaginaryLower imaginaryUpper
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := Hurwitz.Geometry.next_normSq_ge_two fraction nonterminal
    rw [followingZero, Gaussian.Norm.Basic.normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Fraction.Rational) < 2 by decide)) lower
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value := Gaussian.Norm.Basic.normSq_pos
    followingNonzero
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (show (0 : Fraction.Rational) < 1 / 2 by decide) normLess
  have numeratorStrict :
      -following.value.im <
        -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct scaled
    calc
      -following.value.im = -((1 / 2 : Fraction.Rational) *
          (2 * following.value.im)) := by
        rw [half_two_mul]
      _ < -((1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value) := negated
      _ = -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value := by ring1
  have quotientStrict :=
    (Fraction.Order.Field.div_lt_iff_pos normPositive).2 numeratorStrict
  have rhoSquare := GaussianInt.Nearest.remainder_mem fraction.value
  change GaussianInt.Nearest.InFundamentalSquare (GaussianInt.Division.Nearest.residual fraction)
    at rhoSquare
  have rhoLower := rhoSquare.2.2.1
  change -(1 / 2 : Fraction.Rational) ≤ (GaussianInt.Division.Nearest.residual fraction).im at rhoLower
  rw [residual_eq_next_value_inv fraction nonterminal,
    Gaussian.Field.inv_eq] at rhoLower
  change -(1 / 2 : Fraction.Rational) ≤
    -following.value.im / Data.Gaussian.Norm.Basic.normSq following.value at rhoLower
  exact (not_lt_of_ge rhoLower quotientStrict)

/-- A noninitial digit 1-i has residual real coordinate strictly above -1/2.

The excluded boundary would invert to an imaginary coordinate beyond the preceding residual square. -/
private theorem next_residual_real_lower_strict_of_one_sub_i
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, -1⟩) :
    -(1 / 2 : Fraction.Rational) < (GaussianInt.Division.Nearest.residual
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)).re := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let sigma := GaussianInt.Division.Nearest.residual following
  have sigmaSquare := GaussianInt.Nearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.re = -(1 / 2 : Fraction.Rational) :=
    le_antisymm upper sigmaSquare.1
  have decomposition :
      following.value = GaussianInt.toGaussian (⟨1, -1⟩ : GaussianInt) + sigma := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian (⟨1, -1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have realValue : following.value.re = (1 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.re = 1 + -(1 / 2 : Fraction.Rational) := component
      _ = 1 / 2 := by decide
  let magnitude := -following.value.im
  have magnitudeLower : (1 / 2 : Fraction.Rational) ≤ magnitude := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.2.2.le (-1)
    have followingUpper : following.value.im ≤ -(1 / 2 : Fraction.Rational) := by
      calc
        following.value.im = (-1 : Fraction.Rational) + sigma.im := component
        _ = sigma.im + (-1 : Fraction.Rational) := by ring1
        _ ≤ (1 / 2 : Fraction.Rational) + (-1 : Fraction.Rational) := shifted
        _ = -(1 / 2 : Fraction.Rational) := by decide
    have negated := Fraction.Order.Arithmetic.neg_le_neg_direct followingUpper
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have magnitudeUpper : magnitude ≤ (3 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.2.1 (-1)
    have followingLower : -(3 / 2 : Fraction.Rational) ≤ following.value.im := by
      calc
        -(3 / 2 : Fraction.Rational) = -(1 / 2 : Fraction.Rational) + (-1) := by decide
        _ ≤ sigma.im + (-1 : Fraction.Rational) := shifted
        _ = (-1 : Fraction.Rational) + sigma.im := by ring1
        _ = following.value.im := component.symm
    have negated := Fraction.Order.Arithmetic.neg_le_neg_direct followingLower
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have normLess : Data.Gaussian.Norm.Basic.normSq following.value < 2 * magnitude := by
    rw [Data.Gaussian.Norm.Basic.normSq, realValue]
    have bound := quarter_add_square_lt_twice_of_half_interval magnitude
      magnitudeLower magnitudeUpper
    convert bound using 1
    all_goals dsimp only [magnitude]
    all_goals ring1
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := Hurwitz.Geometry.next_normSq_ge_two fraction nonterminal
    rw [followingZero, Gaussian.Norm.Basic.normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Fraction.Rational) < 2 by decide)) lower
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value := Gaussian.Norm.Basic.normSq_pos
    followingNonzero
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (show (0 : Fraction.Rational) < 1 / 2 by decide) normLess
  have lowerQuotient :
      (1 / 2 : Fraction.Rational) < magnitude / Data.Gaussian.Norm.Basic.normSq following.value :=
    (Fraction.Order.Field.lt_div_iff_pos normPositive).2 (by
      calc
        (1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value <
            (1 / 2 : Fraction.Rational) * (2 * magnitude) := scaled
        _ = magnitude := half_two_mul magnitude)
  have rhoSquare := GaussianInt.Nearest.remainder_mem fraction.value
  change GaussianInt.Nearest.InFundamentalSquare (GaussianInt.Division.Nearest.residual fraction)
    at rhoSquare
  have rhoUpper := rhoSquare.2.2.2
  change (GaussianInt.Division.Nearest.residual fraction).im < (1 / 2 : Fraction.Rational) at rhoUpper
  rw [residual_eq_next_value_inv fraction nonterminal,
    Gaussian.Field.inv_eq] at rhoUpper
  change
    -following.value.im / Data.Gaussian.Norm.Basic.normSq following.value < (1 / 2 : Fraction.Rational)
      at rhoUpper
  have quotientIdentity :
      -following.value.im / Data.Gaussian.Norm.Basic.normSq following.value =
        magnitude / Data.Gaussian.Norm.Basic.normSq following.value := by rfl
  rw [quotientIdentity] at rhoUpper
  exact (not_lt_of_ge lowerQuotient.le rhoUpper)

/-- A noninitial digit 1+i has residual imaginary coordinate strictly above -1/2.

The boundary case would invert to a real coordinate larger than the preceding residual square permits. -/
private theorem
  next_residual_imaginary_lower_strict_of_one_add_i
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨1, 1⟩) :
    -(1 / 2 : Fraction.Rational) < (GaussianInt.Division.Nearest.residual
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)).im := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let sigma := GaussianInt.Division.Nearest.residual following
  have sigmaSquare := GaussianInt.Nearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.im = -(1 / 2 : Fraction.Rational) :=
    le_antisymm upper sigmaSquare.2.2.1
  have decomposition :
      following.value = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian (⟨1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have imaginaryValue : following.value.im = (1 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.im = 1 + -(1 / 2 : Fraction.Rational) := component
      _ = 1 / 2 := by decide
  have realLower : (1 / 2 : Fraction.Rational) ≤ following.value.re := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.1 1
    calc
      (1 / 2 : Fraction.Rational) = -(1 / 2 : Fraction.Rational) + 1 := by decide
      _ ≤ sigma.re + 1 := shifted
      _ = 1 + sigma.re := by ring1
      _ = following.value.re := component.symm
  have realUpper : following.value.re ≤ (3 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.1.le 1
    calc
      following.value.re = 1 + sigma.re := component
      _ = sigma.re + 1 := by ring1
      _ ≤ (1 / 2 : Fraction.Rational) + 1 := shifted
      _ = 3 / 2 := by decide
  have normLess : Data.Gaussian.Norm.Basic.normSq following.value < 2 * following.value.re := by
    rw [Data.Gaussian.Norm.Basic.normSq, imaginaryValue]
    calc
      following.value.re ^ 2 + (1 / 2 : Fraction.Rational) ^ 2 =
          (1 / 2 : Fraction.Rational) ^ 2 + following.value.re ^ 2 := by ring1
      _ < 2 * following.value.re :=
        quarter_add_square_lt_twice_of_half_interval following.value.re
          realLower realUpper
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := Hurwitz.Geometry.next_normSq_ge_two fraction nonterminal
    rw [followingZero, Gaussian.Norm.Basic.normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Fraction.Rational) < 2 by decide)) lower
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value := Gaussian.Norm.Basic.normSq_pos
    followingNonzero
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (show (0 : Fraction.Rational) < 1 / 2 by decide) normLess
  have quotientStrict :
      (1 / 2 : Fraction.Rational) <
        following.value.re / Data.Gaussian.Norm.Basic.normSq following.value :=
    (Fraction.Order.Field.lt_div_iff_pos normPositive).2 (by
      calc
        (1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value <
            (1 / 2 : Fraction.Rational) * (2 * following.value.re) := scaled
        _ = following.value.re := half_two_mul following.value.re)
  have rhoSquare := GaussianInt.Nearest.remainder_mem fraction.value
  change GaussianInt.Nearest.InFundamentalSquare (GaussianInt.Division.Nearest.residual fraction)
    at rhoSquare
  have rhoUpper := rhoSquare.2.1
  change (GaussianInt.Division.Nearest.residual fraction).re < (1 / 2 : Fraction.Rational) at rhoUpper
  rw [residual_eq_next_value_inv fraction nonterminal,
    Gaussian.Field.inv_eq] at rhoUpper
  change following.value.re / Data.Gaussian.Norm.Basic.normSq following.value <
    (1 / 2 : Fraction.Rational) at rhoUpper
  exact (not_lt_of_ge quotientStrict.le rhoUpper)

/-- A noninitial digit -1+i has residual imaginary coordinate strictly above -1/2.

The boundary case would invert to a real coordinate below the preceding residual square. -/
private theorem
  next_residual_imaginary_lower_strict_of_neg_one_add_i
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (digitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = ⟨-1, 1⟩) :
    -(1 / 2 : Fraction.Rational) < (GaussianInt.Division.Nearest.residual
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal)).im := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal
  let sigma := GaussianInt.Division.Nearest.residual following
  have sigmaSquare := GaussianInt.Nearest.remainder_mem following.value
  apply lt_of_not_ge
  intro upper
  have boundary : sigma.im = -(1 / 2 : Fraction.Rational) :=
    le_antisymm upper sigmaSquare.2.2.1
  have decomposition :
      following.value = GaussianInt.toGaussian (⟨-1, 1⟩ : GaussianInt) + sigma := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian (⟨-1, 1⟩ : GaussianInt) + sigma := by rw [digitValue]
  have imaginaryValue : following.value.im = (1 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.im decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_im,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    dsimp only [sigma] at boundary
    rw [boundary] at component
    calc
      following.value.im = 1 + -(1 / 2 : Fraction.Rational) := component
      _ = 1 / 2 := by decide
  let magnitude := -following.value.re
  have magnitudeLower : (1 / 2 : Fraction.Rational) ≤ magnitude := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.2.1.le (-1)
    have followingUpper : following.value.re ≤ -(1 / 2 : Fraction.Rational) := by
      calc
        following.value.re = (-1 : Fraction.Rational) + sigma.re := component
        _ = sigma.re + (-1 : Fraction.Rational) := by ring1
        _ ≤ (1 / 2 : Fraction.Rational) + (-1 : Fraction.Rational) := shifted
        _ = -(1 / 2 : Fraction.Rational) := by decide
    have negated := Fraction.Order.Arithmetic.neg_le_neg_direct followingUpper
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have magnitudeUpper : magnitude ≤ (3 / 2 : Fraction.Rational) := by
    have component := congrArg Gaussian.Basic.re decomposition
    simp only [GaussianInt.toGaussian, Gaussian.Basic.add_re,
      Int.cast_one, ← Rat.Fraction.Cast.intCast_eq_fromInt] at component
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      sigmaSquare.1 (-1)
    have followingLower : -(3 / 2 : Fraction.Rational) ≤ following.value.re := by
      calc
        -(3 / 2 : Fraction.Rational) = -(1 / 2 : Fraction.Rational) + (-1) := by decide
        _ ≤ sigma.re + (-1 : Fraction.Rational) := shifted
        _ = (-1 : Fraction.Rational) + sigma.re := by ring1
        _ = following.value.re := component.symm
    have negated := Fraction.Order.Arithmetic.neg_le_neg_direct followingLower
    dsimp only [magnitude]
    simpa only [neg_neg] using negated
  have normLess : Data.Gaussian.Norm.Basic.normSq following.value < 2 * magnitude := by
    rw [Data.Gaussian.Norm.Basic.normSq, imaginaryValue]
    have bound := quarter_add_square_lt_twice_of_half_interval magnitude
      magnitudeLower magnitudeUpper
    convert bound using 1
    all_goals dsimp only [magnitude]
    all_goals ring1
  have followingNonzero : following.value ≠ 0 := by
    intro followingZero
    have lower := Hurwitz.Geometry.next_normSq_ge_two fraction nonterminal
    rw [followingZero, Gaussian.Norm.Basic.normSq_zero] at lower
    exact (not_le_of_gt (show (0 : Fraction.Rational) < 2 by decide)) lower
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq following.value := Gaussian.Norm.Basic.normSq_pos
    followingNonzero
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (show (0 : Fraction.Rational) < 1 / 2 by decide) normLess
  have numeratorStrict :
      following.value.re <
        -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value := by
    have negated := Fraction.Order.Arithmetic.neg_lt_neg_direct scaled
    calc
      following.value.re = -magnitude := by dsimp only [magnitude]; ring1
      _ = -((1 / 2 : Fraction.Rational) * (2 * magnitude)) := by
        rw [half_two_mul]
      _ < -((1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value) := negated
      _ = -(1 / 2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq following.value := by ring1
  have quotientStrict :=
    (Fraction.Order.Field.div_lt_iff_pos normPositive).2 numeratorStrict
  have rhoSquare := GaussianInt.Nearest.remainder_mem fraction.value
  change GaussianInt.Nearest.InFundamentalSquare (GaussianInt.Division.Nearest.residual fraction)
    at rhoSquare
  have rhoLower := rhoSquare.1
  change -(1 / 2 : Fraction.Rational) ≤ (GaussianInt.Division.Nearest.residual fraction).re at rhoLower
  rw [residual_eq_next_value_inv fraction nonterminal,
    Gaussian.Field.inv_eq] at rhoLower
  change -(1 / 2 : Fraction.Rational) ≤
    following.value.re / Data.Gaussian.Norm.Basic.normSq following.value at rhoLower
  exact (not_lt_of_ge rhoLower quotientStrict)

/-- The signed quadrance difference obtained after clearing one proposed
adjacent digit pair against a Gaussian-unit exterior disc. -/
def successorGap (previousDigit followingDigit unit :
  GaussianInt)
    (followingResidual : Gaussian.Basic.Canonical) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq
      ((GaussianInt.toGaussian previousDigit - GaussianInt.toGaussian unit) *
          (GaussianInt.toGaussian followingDigit + followingResidual) + 1) -
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian followingDigit + followingResidual)

/-- A proposed pair of successive Hurwitz digits is impossible when its cleared unit-exterior gap is negative.

The digit identities tie the supplied polynomial gap to the actual following residual and contradict its exterior
certificate. -/
private theorem successor_pair_false_of_negative_gap
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (previousDigit followingDigit unit : GaussianInt)
    (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit)
    (previousDigitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = previousDigit)
    (followingDigitValue :
      GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal) = followingDigit)
    (negativeGap :
      successorGap previousDigit followingDigit unit
        (GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next
          (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal)) < 0) :
    False := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next
    fraction nonterminal) nextNonterminal
  have decomposition :
      following.value =
        GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following := by
        rw [followingDigitValue]
  have exterior := successor_exterior_cleared fraction nonterminal
    nextNonterminal unit unitProperty
  rw [previousDigitValue, decomposition] at exterior
  have strictGap :
      Data.Gaussian.Norm.Basic.normSq
          ((GaussianInt.toGaussian previousDigit - GaussianInt.toGaussian unit) *
              (GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following) + 1) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian followingDigit +
          GaussianInt.Division.Nearest.residual following) :=
    Fraction.Order.Arithmetic.lt_of_sub_neg_direct (by
      change successorGap previousDigit followingDigit unit
        (GaussianInt.Division.Nearest.residual following) < 0
      exact negativeGap)
  exact (not_lt_of_ge exterior strictGap)

/-- A proposed successive digit pair is impossible when its cleared gap at unit 1 is nonpositive.

The half-open rounding convention supplies the strict exterior inequality needed to exclude equality as well. -/
private theorem successor_pair_false_of_nonpositive_gap_at_one
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0)
    (previousDigit followingDigit : GaussianInt)
    (previousDigitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) = previousDigit)
    (followingDigitValue :
      GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal) = followingDigit)
    (nonpositiveGap :
      successorGap previousDigit followingDigit 1
        (GaussianInt.Division.Nearest.residual (Data.ComplexContinuedFraction.Hurwitz.Step.next
          (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal)) ≤ 0) :
    False := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next
    fraction nonterminal) nextNonterminal
  have decomposition :
      following.value =
        GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following := by
    calc
      following.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit following) +
        GaussianInt.Division.Nearest.residual following :=
        GaussianInt.Division.Nearest.value_eq_digit_add_residual following
      _ = GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following := by
        rw [followingDigitValue]
  have exterior := successor_strict_exterior_cleared fraction nonterminal
    nextNonterminal
  rw [previousDigitValue, decomposition] at exterior
  have weakGap :
      Data.Gaussian.Norm.Basic.normSq
          ((GaussianInt.toGaussian previousDigit - 1) *
              (GaussianInt.toGaussian followingDigit + GaussianInt.Division.Nearest.residual following) + 1) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian followingDigit +
          GaussianInt.Division.Nearest.residual following) :=
    Fraction.Order.Boundary.sub_nonpositive_iff.mp (by
      change successorGap previousDigit followingDigit 1
        (GaussianInt.Division.Nearest.residual following) ≤ 0
      exact nonpositiveGap)
  exact (not_lt_of_ge weakGap exterior)

/-- The twenty-eight small adjacent digit pairs left by the two-step
Hermitian calculation.  Constructors are finite displayed data, so
elimination of the relation is kernel-checked case analysis. -/
inductive ForbiddenSmallSuccessor : GaussianInt → GaussianInt →
  Prop
  /-- The forbidden consecutive digit pair (-2, -1) followed by (1, -1). -/ | c01 :
    ForbiddenSmallSuccessor ⟨-2, -1⟩ ⟨1, -1⟩
  /-- The forbidden consecutive digit pair (-2, 0) followed by (1, -1). -/ | c02 :
    ForbiddenSmallSuccessor ⟨-2, 0⟩ ⟨1, -1⟩
  /-- The forbidden consecutive digit pair (-2, 0) followed by (1, 1). -/ | c03 :
    ForbiddenSmallSuccessor ⟨-2, 0⟩ ⟨1, 1⟩
  /-- The forbidden consecutive digit pair (-2, 1) followed by (1, 1). -/ | c04 :
    ForbiddenSmallSuccessor ⟨-2, 1⟩ ⟨1, 1⟩
  /-- The forbidden consecutive digit pair (-1, -2) followed by (1, -1). -/ | c05 :
    ForbiddenSmallSuccessor ⟨-1, -2⟩ ⟨1, -1⟩
  /-- The forbidden consecutive digit pair (-1, -1) followed by (0, -2). -/ | c06 :
    ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨0, -2⟩
  /-- The forbidden consecutive digit pair (-1, -1) followed by (1, -1). -/ | c07 :
    ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨1, -1⟩
  /-- The forbidden consecutive digit pair (-1, -1) followed by (2, 0). -/ | c08 :
    ForbiddenSmallSuccessor ⟨-1, -1⟩ ⟨2, 0⟩
  /-- The forbidden consecutive digit pair (-1, 1) followed by (0, 2). -/ | c09 :
    ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨0, 2⟩
  /-- The forbidden consecutive digit pair (-1, 1) followed by (1, 1). -/ | c10 :
    ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨1, 1⟩
  /-- The forbidden consecutive digit pair (-1, 1) followed by (2, 0). -/ | c11 :
    ForbiddenSmallSuccessor ⟨-1, 1⟩ ⟨2, 0⟩
  /-- The forbidden consecutive digit pair (-1, 2) followed by (1, 1). -/ | c12 :
    ForbiddenSmallSuccessor ⟨-1, 2⟩ ⟨1, 1⟩
  /-- The forbidden consecutive digit pair (0, -2) followed by (-1, -1). -/ | c13 :
    ForbiddenSmallSuccessor ⟨0, -2⟩ ⟨-1, -1⟩
  /-- The forbidden consecutive digit pair (0, -2) followed by (1, -1). -/ | c14 :
    ForbiddenSmallSuccessor ⟨0, -2⟩ ⟨1, -1⟩
  /-- The forbidden consecutive digit pair (0, 2) followed by (-1, 1). -/ | c15 :
    ForbiddenSmallSuccessor ⟨0, 2⟩ ⟨-1, 1⟩
  /-- The forbidden consecutive digit pair (0, 2) followed by (1, 1). -/ | c16 :
    ForbiddenSmallSuccessor ⟨0, 2⟩ ⟨1, 1⟩
  /-- The forbidden consecutive digit pair (1, -2) followed by (-1, -1). -/ | c17 :
    ForbiddenSmallSuccessor ⟨1, -2⟩ ⟨-1, -1⟩
  /-- The forbidden consecutive digit pair (1, -1) followed by (-2, 0). -/ | c18 :
    ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨-2, 0⟩
  /-- The forbidden consecutive digit pair (1, -1) followed by (-1, -1). -/ | c19 :
    ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨-1, -1⟩
  /-- The forbidden consecutive digit pair (1, -1) followed by (0, -2). -/ | c20 :
    ForbiddenSmallSuccessor ⟨1, -1⟩ ⟨0, -2⟩
  /-- The forbidden consecutive digit pair (1, 1) followed by (-2, 0). -/ | c21 :
    ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨-2, 0⟩
  /-- The forbidden consecutive digit pair (1, 1) followed by (-1, 1). -/ | c22 :
    ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨-1, 1⟩
  /-- The forbidden consecutive digit pair (1, 1) followed by (0, 2). -/ | c23 :
    ForbiddenSmallSuccessor ⟨1, 1⟩ ⟨0, 2⟩
  /-- The forbidden consecutive digit pair (1, 2) followed by (-1, 1). -/ | c24 :
    ForbiddenSmallSuccessor ⟨1, 2⟩ ⟨-1, 1⟩
  /-- The forbidden consecutive digit pair (2, -1) followed by (-1, -1). -/ | c25 :
    ForbiddenSmallSuccessor ⟨2, -1⟩ ⟨-1, -1⟩
  /-- The forbidden consecutive digit pair (2, 0) followed by (-1, -1). -/ | c26 :
    ForbiddenSmallSuccessor ⟨2, 0⟩ ⟨-1, -1⟩
  /-- The forbidden consecutive digit pair (2, 0) followed by (-1, 1). -/ | c27 :
    ForbiddenSmallSuccessor ⟨2, 0⟩ ⟨-1, 1⟩
  /-- The forbidden consecutive digit pair (2, 1) followed by (-1, 1). -/ | c28 :
    ForbiddenSmallSuccessor ⟨2, 1⟩ ⟨-1, 1⟩

/-- An exact local abbreviation for the finite relation of forbidden successive digit pairs. -/
private abbrev IsForbiddenSmallSuccessorPair :=
  ForbiddenSmallSuccessor

/-- The cleared gap for digits (-2,-1), (1,-1) at unit -1 is the residual quadrance minus one. -/
private theorem successorGap_test_identity (sigma :
  Gaussian.Basic.Canonical) :
    successorGap ⟨-2, -1⟩ ⟨1, -1⟩ (-1) sigma = Data.Gaussian.Norm.Basic.normSq sigma - 1 := by
  simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two, -Int.cast_add,
    -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero, successorGap,
    Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
  ring1

/-- Minus one plus twice a rational value below one half is negative. -/
private theorem neg_one_add_twice_lt_zero_of_lt_half
    {value : Fraction.Rational} (upper : value < 1 / 2) :
    -1 + 2 * value < 0 := by
  have doubled := twice_lt_one_of_lt_half upper
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    doubled (-1)
  calc
    -1 + 2 * value = 2 * value + -1 := by ring1
    _ < 1 + -1 := shifted
    _ = 0 := by ring1

/-- Minus one minus twice a rational value above minus one half is negative. -/
private theorem neg_one_sub_twice_lt_zero_of_neg_half_lt
    {value : Fraction.Rational} (lower : -(1 / 2 : Fraction.Rational) < value) :
    -1 - 2 * value < 0 := by
  have doubled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (show (0 : Fraction.Rational) < 2 by decide) lower
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    doubled (-(2 * value))
  calc
    -1 - 2 * value = -1 + -(2 * value) := by ring1
    _ = 2 * (-(1 / 2 : Fraction.Rational)) + -(2 * value) := by
      rw [show (2 : Fraction.Rational) * (-(1 / 2)) = -1 by decide]
    _ < 2 * value + -(2 * value) := shifted
    _ = 0 := by ring1

/-- Minus three plus twice a rational value below one half is negative. -/
private theorem neg_three_add_twice_lt_zero_of_lt_half
    {value : Fraction.Rational} (upper : value < 1 / 2) :
    -3 + 2 * value < 0 := by
  have oneGap := neg_one_add_twice_lt_zero_of_lt_half upper
  have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
    oneGap (-2)
  calc
    -3 + 2 * value = (-1 + 2 * value) + -2 := by ring1
    _ < 0 + -2 := shifted
    _ < 0 := by decide

/-- Minus three minus twice a rational value at least minus one half is negative. -/
private theorem neg_three_sub_twice_lt_zero_of_neg_half_le
    {value : Fraction.Rational} (lower : -(1 / 2 : Fraction.Rational) ≤ value) :
    -3 - 2 * value < 0 := by
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    lower (show (0 : Fraction.Rational) ≤ 2 by decide)
  have negated := Fraction.Order.Arithmetic.neg_le_neg_direct doubled
  have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
    negated (-3)
  calc
    -3 - 2 * value = -(2 * value) + -3 := by ring1
    _ ≤ -(2 * (-(1 / 2 : Fraction.Rational))) + -3 := shifted
    _ = -2 := by decide
    _ < 0 := by decide

/-- No actual pair of adjacent noninitial Hurwitz digits belongs to the
finite exceptional relation.  Each constructor is discharged by one exact
cleared exterior-disc calculation. -/
theorem not_forbiddenSmallSuccessor
    (fraction : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0)
    (nextNonterminal : GaussianInt.Division.Nearest.remainder (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction
      nonterminal) ≠ 0) :
    ¬ ForbiddenSmallSuccessor
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal))
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal)) := by
  let following := Data.ComplexContinuedFraction.Hurwitz.Step.next (Data.ComplexContinuedFraction.Hurwitz.Step.next
    fraction nonterminal) nextNonterminal
  let sigma := GaussianInt.Division.Nearest.residual following
  have sigmaSquare := GaussianInt.Nearest.remainder_mem following.value
  have sigmaNormLtOne : Data.Gaussian.Norm.Basic.normSq sigma < 1 := by
    exact
      (GaussianInt.Nearest.remainder_normSq_le_half following.value).trans_lt
        (show (1 / 2 : Fraction.Rational) < 1 by decide)
  have normGap : Data.Gaussian.Norm.Basic.normSq sigma - 1 < 0 :=
    Fraction.Order.Arithmetic.sub_neg_direct sigmaNormLtOne
  have realUpperGap : -1 + 2 * sigma.re < 0 :=
    neg_one_add_twice_lt_zero_of_lt_half sigmaSquare.2.1
  have imaginaryUpperGap : -1 + 2 * sigma.im < 0 :=
    neg_one_add_twice_lt_zero_of_lt_half sigmaSquare.2.2.2
  have realUpperThreeGap : -3 + 2 * sigma.re < 0 :=
    neg_three_add_twice_lt_zero_of_lt_half sigmaSquare.2.1
  have imaginaryUpperThreeGap : -3 + 2 * sigma.im < 0 :=
    neg_three_add_twice_lt_zero_of_lt_half sigmaSquare.2.2.2
  have realLowerThreeGap : -3 - 2 * sigma.re < 0 :=
    neg_three_sub_twice_lt_zero_of_neg_half_le sigmaSquare.1
  have imaginaryLowerThreeGap : -3 - 2 * sigma.im < 0 :=
    neg_three_sub_twice_lt_zero_of_neg_half_le sigmaSquare.2.2.1
  intro forbidden
  generalize previousDigitValue : GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
    fraction nonterminal) =
    previousDigit at forbidden
  generalize followingDigitValue :
    GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
      (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal) =
      followingDigit at forbidden
  cases forbidden with
  | c01 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, -1⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-2, -1⟩ ⟨1, -1⟩ (-1) sigma < 0
      rw [successorGap_test_identity]
      exact normGap
  | c02 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 0⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_real_lower_strict_of_one_sub_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-2, 0⟩ ⟨1, -1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c03 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 0⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_real_lower_strict_of_one_add_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-2, 0⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c04 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-2, 1⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-2, 1⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c05 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c06 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨0, -2⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨0, -2⟩ (-1) sigma < 0
      convert imaginaryUpperThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c07 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨1, -1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨1, -1⟩ (-1) sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c08 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, -1⟩ ⟨2, 0⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, -1⟩ ⟨2, 0⟩ ⟨0, -1⟩ sigma < 0
      convert realLowerThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c09 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨0, 2⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 1⟩ ⟨0, 2⟩ (-1) sigma < 0
      convert imaginaryLowerThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c10 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨1, 1⟩ (-1)
        (Or.inr (Or.inl rfl)) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_one_add_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨-1, 1⟩ ⟨1, 1⟩ (-1) sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c11 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 1⟩ ⟨2, 0⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 1⟩ ⟨2, 0⟩ ⟨0, 1⟩ sigma < 0
      convert realLowerThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c12 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨-1, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨-1, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c13 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨0, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c14 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨0, -2⟩ ⟨1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c15 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_neg_one_add_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨0, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c16 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨0, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_one_add_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨0, 2⟩ ⟨1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c17 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, -2⟩ ⟨-1, -1⟩ ⟨0, -1⟩ sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c18 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨-2, 0⟩ ⟨0, -1⟩
        (Or.inr (Or.inr (Or.inr rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨-2, 0⟩ ⟨0, -1⟩ sigma < 0
      convert realUpperThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c19 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert imaginaryUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c20 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, -1⟩ ⟨0, -2⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, -1⟩ ⟨0, -2⟩ 1 sigma < 0
      convert imaginaryUpperThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c21 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨-2, 0⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, 1⟩ ⟨-2, 0⟩ ⟨0, 1⟩ sigma < 0
      convert realUpperThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c22 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      have strictLower := next_residual_imaginary_lower_strict_of_neg_one_add_i
        (Data.ComplexContinuedFraction.Hurwitz.Step.next fraction nonterminal) nextNonterminal followingDigitValue
      have negative := neg_one_sub_twice_lt_zero_of_neg_half_lt strictLower
      change successorGap ⟨1, 1⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert negative using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, sigma, following, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c23 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 1⟩ ⟨0, 2⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨1, 1⟩ ⟨0, 2⟩ 1 sigma < 0
      convert imaginaryLowerThreeGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c24 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨1, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩
        (Or.inr (Or.inr (Or.inl rfl))) previousDigitValue followingDigitValue
      change successorGap ⟨1, 2⟩ ⟨-1, 1⟩ ⟨0, 1⟩ sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c25 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, -1⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, -1⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c26 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 0⟩ ⟨-1, -1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 0⟩ ⟨-1, -1⟩ 1 sigma < 0
      convert realUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c27 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 0⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 0⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert realUpperGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1
  | c28 =>
      apply successor_pair_false_of_negative_gap fraction nonterminal
        nextNonterminal ⟨2, 1⟩ ⟨-1, 1⟩ 1
        (Or.inl rfl) previousDigitValue followingDigitValue
      change successorGap ⟨2, 1⟩ ⟨-1, 1⟩ 1 sigma < 0
      convert normGap using 1 ;
        simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
          -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.cast_zero,
          successorGap, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt] ; ring1

/-- The eight cross terms of the quadrance-five/diagonal denominator
comparison. -/
inductive IsLakeinRootCross : Int → Int → Prop
  /-- The root cross-coefficient pair `(-3) (-1)`. -/ | negativeThreeNegativeOne :
    IsLakeinRootCross (-3) (-1)
  /-- The root cross-coefficient pair `(-3) 1`. -/ | negativeThreePositiveOne :
    IsLakeinRootCross (-3) 1
  /-- The root cross-coefficient pair `(-1) (-3)`. -/ | negativeOneNegativeThree :
    IsLakeinRootCross (-1) (-3)
  /-- The root cross-coefficient pair `(-1) 3`. -/ | negativeOnePositiveThree :
    IsLakeinRootCross (-1) 3
  /-- The root cross-coefficient pair `1 (-3)`. -/ | positiveOneNegativeThree :
    IsLakeinRootCross 1 (-3)
  /-- The root cross-coefficient pair `1 3`. -/ | positiveOnePositiveThree :
    IsLakeinRootCross 1 3
  /-- The root cross-coefficient pair `3 (-1)`. -/ | positiveThreeNegativeOne :
    IsLakeinRootCross 3 (-1)
  /-- The root cross-coefficient pair `3 1`. -/ | positiveThreePositiveOne :
    IsLakeinRootCross 3 1

/-- The integral Hermitian form with constant coefficient four, radial coefficient two, and the supplied cross
coefficients.

The eight Lakein root choices express the norm-five/diagonal comparison after subtracting one. -/
def lakeinRootForm (realCross imaginaryCross : Int) :
    Geometry.Hermitian.Binary.IntegralHermitianForm :=
  ⟨4, 2, realCross, imaginaryCross⟩

/-- All eight Lakein root forms evaluate nonnegatively at the supplied Gaussian rational.

The quantified cross coefficients are restricted by the finite root-cross relation. -/
def LakeinRootFormsNonnegative (value :
  Gaussian.Basic.Canonical) : Prop :=
  ∀ realCross imaginaryCross,
    IsLakeinRootCross realCross imaginaryCross →
      0 ≤ (lakeinRootForm realCross imaginaryCross).evaluate value

/-- Every Lakein root form has determinant minus two. -/
private theorem lakeinRootForm_determinant
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross) :
    (lakeinRootForm realCross imaginaryCross).determinant = -2 := by
  cases root <;> decide

/-- Adding four times a unit-translated squared norm preserves nonnegativity of a Lakein root form.

The resulting integral form has constant eight, radial coefficient six, and the corresponding translated cross
coefficients. -/
private theorem evaluate_root_plus_four_unit_square_nonnegative
    (value : Gaussian.Basic.Canonical) {realCross imaginaryCross : Int}
    (rootNonnegative :
      0 ≤ (lakeinRootForm realCross imaginaryCross).evaluate value)
    (unit : GaussianInt) (unitProperty : GaussianInt.Norm.Small.IsGaussianUnit unit) :
    0 ≤
      (⟨8, 6, realCross + 4 * unit.re,
          imaginaryCross + 4 * unit.im⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate
        value := by
  have squareNonnegative :
      0 ≤ 4 * Data.Gaussian.Norm.Basic.normSq (value + GaussianInt.toGaussian unit) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 4 by decide) (Gaussian.Norm.Basic.normSq_nonneg _)
  have sumNonnegative := add_nonneg rootNonnegative squareNonnegative
  calc
    0 ≤
        (lakeinRootForm realCross imaginaryCross).evaluate value +
          4 * Data.Gaussian.Norm.Basic.normSq (value + GaussianInt.toGaussian unit) := sumNonnegative
    _ = (⟨8, 6, realCross + 4 * unit.re,
          imaginaryCross + 4 * unit.im⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate
        value := by
      rcases unitProperty with rfl | rfl | rfl | rfl
      all_goals simp [-tsub_zero, -sub_zero, -add_sub_add_right_eq_sub, -eq_self, -iff_self, -Even.neg_pow, -even_two,
        -Int.cast_add, -Int.cast_neg, -Int.cast_zero, -Int.cast_sub, Ring.IntCast.add, Ring.IntCast.cast_zero,
        Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate, lakeinRootForm,
        Geometry.Hermitian.Binary.hermitianForm, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, ←
          Rat.Fraction.Cast.intCast_eq_fromInt]
      all_goals ring1

/-- The twenty-four first-step forms not settled by the slack-one
certificate.  The following digit is retained because it is needed by the
second-step succession check. -/
inductive FirstExceptionalHermitian :
    Geometry.Hermitian.Binary.IntegralHermitianForm → GaussianInt → Prop
  /-- The exceptional form with coefficients (6, 4, 1, 5) and retained following digit (1, 1). -/ | c01 :
    FirstExceptionalHermitian ⟨6, 4, 1, 5⟩ ⟨1, 1⟩
  /-- The exceptional form with coefficients (2, 4, 1, -3) and retained following digit (1, -1). -/ | c02 :
    FirstExceptionalHermitian ⟨2, 4, 1, -3⟩ ⟨1, -1⟩
  /-- The exceptional form with coefficients (6, 4, 5, 1) and retained following digit (2, 0). -/ | c03 :
    FirstExceptionalHermitian ⟨6, 4, 5, 1⟩ ⟨2, 0⟩
  /-- The exceptional form with coefficients (2, 4, 1, 3) and retained following digit (1, 1). -/ | c04 :
    FirstExceptionalHermitian ⟨2, 4, 1, 3⟩ ⟨1, 1⟩
  /-- The exceptional form with coefficients (6, 4, 1, -5) and retained following digit (1, -1). -/ | c05 :
    FirstExceptionalHermitian ⟨6, 4, 1, -5⟩ ⟨1, -1⟩
  /-- The exceptional form with coefficients (6, 4, 5, -1) and retained following digit (2, 0). -/ | c06 :
    FirstExceptionalHermitian ⟨6, 4, 5, -1⟩ ⟨2, 0⟩
  /-- The exceptional form with coefficients (2, 4, 3, -1) and retained following digit (1, -1). -/ | c07 :
    FirstExceptionalHermitian ⟨2, 4, 3, -1⟩ ⟨1, -1⟩
  /-- The exceptional form with coefficients (6, 4, -5, -1) and retained following digit (-1, -1). -/ | c08 :
    FirstExceptionalHermitian ⟨6, 4, -5, -1⟩ ⟨-1, -1⟩
  /-- The exceptional form with coefficients (6, 4, -1, -5) and retained following digit (0, -2). -/ | c09 :
    FirstExceptionalHermitian ⟨6, 4, -1, -5⟩ ⟨0, -2⟩
  /-- The exceptional form with coefficients (2, 4, 3, 1) and retained following digit (1, 1). -/ | c10 :
    FirstExceptionalHermitian ⟨2, 4, 3, 1⟩ ⟨1, 1⟩
  /-- The exceptional form with coefficients (6, 4, -5, 1) and retained following digit (-1, 1). -/ | c11 :
    FirstExceptionalHermitian ⟨6, 4, -5, 1⟩ ⟨-1, 1⟩
  /-- The exceptional form with coefficients (6, 4, -1, 5) and retained following digit (0, 2). -/ | c12 :
    FirstExceptionalHermitian ⟨6, 4, -1, 5⟩ ⟨0, 2⟩
  /-- The exceptional form with coefficients (6, 4, 5, -1) and retained following digit (1, -1). -/ | c13 :
    FirstExceptionalHermitian ⟨6, 4, 5, -1⟩ ⟨1, -1⟩
  /-- The exceptional form with coefficients (2, 4, -3, -1) and retained following digit (-1, -1). -/ | c14 :
    FirstExceptionalHermitian ⟨2, 4, -3, -1⟩ ⟨-1, -1⟩
  /-- The exceptional form with coefficients (6, 4, 1, -5) and retained following digit (0, -2). -/ | c15 :
    FirstExceptionalHermitian ⟨6, 4, 1, -5⟩ ⟨0, -2⟩
  /-- The exceptional form with coefficients (6, 4, 5, 1) and retained following digit (1, 1). -/ | c16 :
    FirstExceptionalHermitian ⟨6, 4, 5, 1⟩ ⟨1, 1⟩
  /-- The exceptional form with coefficients (2, 4, -3, 1) and retained following digit (-1, 1). -/ | c17 :
    FirstExceptionalHermitian ⟨2, 4, -3, 1⟩ ⟨-1, 1⟩
  /-- The exceptional form with coefficients (6, 4, 1, 5) and retained following digit (0, 2). -/ | c18 :
    FirstExceptionalHermitian ⟨6, 4, 1, 5⟩ ⟨0, 2⟩
  /-- The exceptional form with coefficients (6, 4, -1, 5) and retained following digit (-1, 1). -/ | c19 :
    FirstExceptionalHermitian ⟨6, 4, -1, 5⟩ ⟨-1, 1⟩
  /-- The exceptional form with coefficients (2, 4, -1, -3) and retained following digit (-1, -1). -/ | c20 :
    FirstExceptionalHermitian ⟨2, 4, -1, -3⟩ ⟨-1, -1⟩
  /-- The exceptional form with coefficients (6, 4, -5, 1) and retained following digit (-2, 0). -/ | c21 :
    FirstExceptionalHermitian ⟨6, 4, -5, 1⟩ ⟨-2, 0⟩
  /-- The exceptional form with coefficients (2, 4, -1, 3) and retained following digit (-1, 1). -/ | c22 :
    FirstExceptionalHermitian ⟨2, 4, -1, 3⟩ ⟨-1, 1⟩
  /-- The exceptional form with coefficients (6, 4, -1, -5) and retained following digit (-1, -1). -/ | c23 :
    FirstExceptionalHermitian ⟨6, 4, -1, -5⟩ ⟨-1, -1⟩
  /-- The exceptional form with coefficients (6, 4, -5, -1) and retained following digit (-2, 0). -/ | c24 :
    FirstExceptionalHermitian ⟨6, 4, -5, -1⟩ ⟨-2, 0⟩

/-- A root-form pullback by a digit of norm at least two either has constant at least seven or is one of 24 retained
exceptions.

Digits of norm at least five satisfy the uniform constant bound; the remaining diagonal and doubled-axis digits are
checked by finite cases. -/
private theorem root_pullback_constant_gap_or_exceptional
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross)
    (coefficient : GaussianInt) (coefficientNorm : 2 ≤ GaussianInt.normNat coefficient) :
    7 ≤
        ((lakeinRootForm realCross imaginaryCross).pullback coefficient).constant ∨
      FirstExceptionalHermitian
        ((lakeinRootForm realCross imaginaryCross).pullback coefficient)
        coefficient := by
  by_cases large : 5 ≤ GaussianInt.normNat coefficient
  · left
    have normIntLarge : (5 : Int) ≤ GaussianInt.normInt coefficient := by
      rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat]
      exact Int.Order.natCast_le_iff.mpr large
    have scaledLarge : (3 : Int) * 5 ≤ 3 * GaussianInt.normInt coefficient :=
      Int.Order.mul_le_mul_of_nonneg_left normIntLarge (by decide)
    have constantGap : (7 : Int) ≤ 3 * GaussianInt.normInt coefficient - 8 := by
      calc
        (7 : Int) = 3 * 5 - 8 := by decide
        _ ≤ 3 * GaussianInt.normInt coefficient - 8 := by
          rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
          exact Int.Order.add_le_add scaledLarge (Int.Order.le_refl (-8))
    have rootSquare :
        realCross * realCross + imaginaryCross * imaginaryCross = 10 := by
      cases root <;> decide
    have lower := Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_constant_lower
      (lakeinRootForm realCross imaginaryCross) coefficient
    have constantEquation : 3 * GaussianInt.normInt coefficient - 8 =
          ((lakeinRootForm realCross imaginaryCross).constant - 1) *
              GaussianInt.normInt coefficient +
            (lakeinRootForm realCross imaginaryCross).radial -
              ((lakeinRootForm realCross imaginaryCross).realCross *
                  (lakeinRootForm realCross imaginaryCross).realCross +
                (lakeinRootForm realCross imaginaryCross).imaginaryCross *
                  (lakeinRootForm realCross imaginaryCross).imaginaryCross) := by
            dsimp only [lakeinRootForm]
            rw [rootSquare]
            ring1
    rewrite [constantEquation] at constantGap
    exact Int.Order.le_trans constantGap lower
  · have small : GaussianInt.normNat coefficient < 5 := Nat.lt_of_not_ge large
    have cases := GaussianInt.Norm.Small.normNat_eq_zero_or_one_or_two_or_four_or_five_of_lt_six
      coefficient (small.trans (by decide))
    rcases cases with zero | one | two | four | five
    · rw [zero] at coefficientNorm
      exact False.elim ((by decide : ¬2 ≤ 0) coefficientNorm)
    · rw [one] at coefficientNorm
      exact False.elim ((by decide : ¬2 ≤ 1) coefficientNorm)
    · have concrete := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two two
      rcases concrete with rfl | rfl | rfl | rfl
      all_goals cases root
      all_goals first
        | exact Or.inl (by decide)
        | exact Or.inr FirstExceptionalHermitian.c01
        | exact Or.inr FirstExceptionalHermitian.c02
        | exact Or.inr FirstExceptionalHermitian.c04
        | exact Or.inr FirstExceptionalHermitian.c05
        | exact Or.inr FirstExceptionalHermitian.c07
        | exact Or.inr FirstExceptionalHermitian.c08
        | exact Or.inr FirstExceptionalHermitian.c10
        | exact Or.inr FirstExceptionalHermitian.c11
        | exact Or.inr FirstExceptionalHermitian.c13
        | exact Or.inr FirstExceptionalHermitian.c14
        | exact Or.inr FirstExceptionalHermitian.c16
        | exact Or.inr FirstExceptionalHermitian.c17
        | exact Or.inr FirstExceptionalHermitian.c19
        | exact Or.inr FirstExceptionalHermitian.c20
        | exact Or.inr FirstExceptionalHermitian.c22
        | exact Or.inr FirstExceptionalHermitian.c23
    · have concrete := GaussianInt.Norm.Small.axisDouble_cases_of_normNat_eq_four four
      rcases concrete with rfl | rfl | rfl | rfl
      all_goals cases root
      all_goals first
        | exact Or.inl (by decide)
        | exact Or.inr FirstExceptionalHermitian.c03
        | exact Or.inr FirstExceptionalHermitian.c06
        | exact Or.inr FirstExceptionalHermitian.c09
        | exact Or.inr FirstExceptionalHermitian.c12
        | exact Or.inr FirstExceptionalHermitian.c15
        | exact Or.inr FirstExceptionalHermitian.c18
        | exact Or.inr FirstExceptionalHermitian.c21
        | exact Or.inr FirstExceptionalHermitian.c24
    · rw [five] at small
      exact False.elim ((Nat.lt_irrefl 5) small)

/-- An integer whose square is below sixteen is one of the seven values from -3 through 3. -/
private theorem coordinate_cases_of_square_lt_sixteen {value :
  Int}
    (small : value * value < 16) :
    value = -3 ∨ value = -2 ∨ value = -1 ∨ value = 0 ∨
      value = 1 ∨ value = 2 ∨ value = 3 := by
  have lower : -(4 : Int) < value := by
    apply Int.Order.lt_of_not_le
    intro valueAtMost
    have fourLeNegative : (4 : Int) ≤ -value := by
      have negated := Int.Order.neg_le_neg valueAtMost
      change (4 : Int) ≤ -value at negated
      exact negated
    have squareAtLeastSixteen : (16 : Int) ≤ value * value := by
      calc
        (16 : Int) = 4 * 4 := rfl
        _ ≤ (-value) * (-value) :=
          Int.Order.le_trans
            (Int.Order.mul_le_mul_of_nonneg_right fourLeNegative (by decide))
            (Int.Order.mul_le_mul_of_nonneg_left fourLeNegative (by omega))
        _ = value * value := by ring1
    exact (Int.Order.lt_iff_le_and_not_ge.mp small).2 squareAtLeastSixteen
  have upper : value < 4 := by
    apply Int.Order.lt_of_not_le
    intro fourLeValue
    have squareAtLeastSixteen : (16 : Int) ≤ value * value := by
      calc
        (16 : Int) = 4 * 4 := rfl
        _ ≤ value * value :=
          Int.Order.le_trans
            (Int.Order.mul_le_mul_of_nonneg_right fourLeValue (by decide))
            (Int.Order.mul_le_mul_of_nonneg_left fourLeValue (by omega))
    exact (Int.Order.lt_iff_le_and_not_ge.mp small).2 squareAtLeastSixteen
  have lowerLe : (-3 : Int) ≤ value := by
    change (-(4 : Int) + 1) ≤ value
    exact Int.add_one_le_iff.mpr lower
  have upperLe : value ≤ (3 : Int) := by
    change value ≤ (4 : Int) - 1
    omega
  by_cases negThree : value = -3
  · exact Or.inl negThree
  have negTwoLe : (-2 : Int) ≤ value := by
    change (-3 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne lowerLe (Ne.symm negThree))
  by_cases negTwo : value = -2
  · exact Or.inr (Or.inl negTwo)
  have negOneLe : (-1 : Int) ≤ value := by
    change (-2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne negTwoLe (Ne.symm negTwo))
  by_cases negOne : value = -1
  · exact Or.inr (Or.inr (Or.inl negOne))
  have zeroLe : (0 : Int) ≤ value := by
    change (-1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne negOneLe (Ne.symm negOne))
  by_cases zero : value = 0
  · exact Or.inr (Or.inr (Or.inr (Or.inl zero)))
  have oneLe : (1 : Int) ≤ value := by
    change (0 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne zeroLe (Ne.symm zero))
  by_cases one : value = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl one))))
  have twoLe : (2 : Int) ≤ value := by
    change (1 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne oneLe (Ne.symm one))
  by_cases two : value = 2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl two)))))
  have threeLe : (3 : Int) ≤ value := by
    change (2 : Int) + 1 ≤ value
    exact Int.add_one_le_iff.mpr
      (Int.Order.lt_of_le_of_ne twoLe (Ne.symm two))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Int.Order.le_antisymm upperLe threeLe))))))

/-- The 32 Gaussian integers of quadrance at least two and below eleven.

Each constructor retains one concrete preceding digit for the finite second-pullback classification. -/
private inductive IsSmallPreviousDigit : GaussianInt → Prop
  /-- The allowed small preceding digit (-3, -1). -/ | c01 :
    IsSmallPreviousDigit ⟨-3, -1⟩
  /-- The allowed small preceding digit (-3, 0). -/ | c02 :
    IsSmallPreviousDigit ⟨-3, 0⟩
  /-- The allowed small preceding digit (-3, 1). -/ | c03 :
    IsSmallPreviousDigit ⟨-3, 1⟩
  /-- The allowed small preceding digit (-2, -2). -/ | c04 :
    IsSmallPreviousDigit ⟨-2, -2⟩
  /-- The allowed small preceding digit (-2, -1). -/ | c05 :
    IsSmallPreviousDigit ⟨-2, -1⟩
  /-- The allowed small preceding digit (-2, 0). -/ | c06 :
    IsSmallPreviousDigit ⟨-2, 0⟩
  /-- The allowed small preceding digit (-2, 1). -/ | c07 :
    IsSmallPreviousDigit ⟨-2, 1⟩
  /-- The allowed small preceding digit (-2, 2). -/ | c08 :
    IsSmallPreviousDigit ⟨-2, 2⟩
  /-- The allowed small preceding digit (-1, -3). -/ | c09 :
    IsSmallPreviousDigit ⟨-1, -3⟩
  /-- The allowed small preceding digit (-1, -2). -/ | c10 :
    IsSmallPreviousDigit ⟨-1, -2⟩
  /-- The allowed small preceding digit (-1, -1). -/ | c11 :
    IsSmallPreviousDigit ⟨-1, -1⟩
  /-- The allowed small preceding digit (-1, 1). -/ | c12 :
    IsSmallPreviousDigit ⟨-1, 1⟩
  /-- The allowed small preceding digit (-1, 2). -/ | c13 :
    IsSmallPreviousDigit ⟨-1, 2⟩
  /-- The allowed small preceding digit (-1, 3). -/ | c14 :
    IsSmallPreviousDigit ⟨-1, 3⟩
  /-- The allowed small preceding digit (0, -3). -/ | c15 :
    IsSmallPreviousDigit ⟨0, -3⟩
  /-- The allowed small preceding digit (0, -2). -/ | c16 :
    IsSmallPreviousDigit ⟨0, -2⟩
  /-- The allowed small preceding digit (0, 2). -/ | c17 :
    IsSmallPreviousDigit ⟨0, 2⟩
  /-- The allowed small preceding digit (0, 3). -/ | c18 :
    IsSmallPreviousDigit ⟨0, 3⟩
  /-- The allowed small preceding digit (1, -3). -/ | c19 :
    IsSmallPreviousDigit ⟨1, -3⟩
  /-- The allowed small preceding digit (1, -2). -/ | c20 :
    IsSmallPreviousDigit ⟨1, -2⟩
  /-- The allowed small preceding digit (1, -1). -/ | c21 :
    IsSmallPreviousDigit ⟨1, -1⟩
  /-- The allowed small preceding digit (1, 1). -/ | c22 :
    IsSmallPreviousDigit ⟨1, 1⟩
  /-- The allowed small preceding digit (1, 2). -/ | c23 :
    IsSmallPreviousDigit ⟨1, 2⟩
  /-- The allowed small preceding digit (1, 3). -/ | c24 :
    IsSmallPreviousDigit ⟨1, 3⟩
  /-- The allowed small preceding digit (2, -2). -/ | c25 :
    IsSmallPreviousDigit ⟨2, -2⟩
  /-- The allowed small preceding digit (2, -1). -/ | c26 :
    IsSmallPreviousDigit ⟨2, -1⟩
  /-- The allowed small preceding digit (2, 0). -/ | c27 :
    IsSmallPreviousDigit ⟨2, 0⟩
  /-- The allowed small preceding digit (2, 1). -/ | c28 :
    IsSmallPreviousDigit ⟨2, 1⟩
  /-- The allowed small preceding digit (2, 2). -/ | c29 :
    IsSmallPreviousDigit ⟨2, 2⟩
  /-- The allowed small preceding digit (3, -1). -/ | c30 :
    IsSmallPreviousDigit ⟨3, -1⟩
  /-- The allowed small preceding digit (3, 0). -/ | c31 :
    IsSmallPreviousDigit ⟨3, 0⟩
  /-- The allowed small preceding digit (3, 1). -/ | c32 :
    IsSmallPreviousDigit ⟨3, 1⟩

/-- A Gaussian integer of quadrance between two and ten belongs to the explicit small-digit relation.

Each coordinate lies between -3 and 3; the norm bounds discard precisely the other coordinate pairs. -/
private theorem isSmallPreviousDigit_of_norm_bounds
    (digit : GaussianInt) (twoLe : 2 ≤ GaussianInt.normNat digit)
    (lessThanEleven : GaussianInt.normNat digit < 11) :
    IsSmallPreviousDigit digit := by
  have normIntTwoLe : (2 : Int) ≤ GaussianInt.normInt digit := by
    rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_le_iff.mpr twoLe
  have normIntSmall : GaussianInt.normInt digit < 11 := by
    rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_lt_iff.mpr lessThanEleven
  have realSmall : digit.re * digit.re < 16 := by
    have imaginaryNonnegative := Purelib.Data.Int.Order.mul_self_nonneg digit.im
    have realLeNorm : digit.re * digit.re ≤ GaussianInt.normInt digit := by
      have shifted := Int.Order.add_le_add (Int.Order.le_refl (digit.re * digit.re)) imaginaryNonnegative
      simpa only [GaussianInt.normInt, Int.add_zero] using shifted
    omega
  have imaginarySmall : digit.im * digit.im < 16 := by
    have realNonnegative := Purelib.Data.Int.Order.mul_self_nonneg digit.re
    have imaginaryLeNorm : digit.im * digit.im ≤ GaussianInt.normInt digit := by
      have shifted := Int.Order.add_le_add realNonnegative (Int.Order.le_refl (digit.im * digit.im))
      simpa only [GaussianInt.normInt, Int.Arithmetic.zero_add] using shifted
    omega
  rcases digit with ⟨real, imaginary⟩
  change real * real < 16 at realSmall
  change imaginary * imaginary < 16 at imaginarySmall
  rcases coordinate_cases_of_square_lt_sixteen realSmall with
      realNegativeThree | realNegativeTwo | realNegativeOne | realZero |
        realPositiveOne | realPositiveTwo | realPositiveThree <;>
    rcases coordinate_cases_of_square_lt_sixteen imaginarySmall with
      imaginaryNegativeThree | imaginaryNegativeTwo | imaginaryNegativeOne |
        imaginaryZero | imaginaryPositiveOne | imaginaryPositiveTwo |
        imaginaryPositiveThree
  all_goals subst real; subst imaginary
  all_goals dsimp only [GaussianInt.normInt] at normIntTwoLe normIntSmall
  all_goals first
    | exact False.elim
        (Purelib.Logic.Decidable.false_of_decide_false normIntTwoLe (by decide))
    | exact False.elim
        (Purelib.Logic.Decidable.false_of_decide_false normIntSmall (by decide))
    | constructor

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

/-- Pulling an exceptional form back by a digit of quadrance at least eleven makes it nonnegative on the closed unit
disk.

Its determinant is minus two and the norm bound supplies the required positive constant gap. -/
private theorem
  pullback_nonnegative_of_large
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt) (large : 11 ≤ GaussianInt.normNat previousDigit)
    (value : Gaussian.Basic.Canonical) (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  have normIntLarge : (11 : Int) ≤ GaussianInt.normInt previousDigit := by
    rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_le_iff.mpr large
  have lower := Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_constant_lower
    form previousDigit
  have scaledLarge : (5 : Int) * 11 ≤ 5 * GaussianInt.normInt previousDigit :=
    Int.Order.mul_le_mul_of_nonneg_left normIntLarge (by decide)
  have shiftedScaledLarge := Int.Order.add_le_add scaledLarge (Int.Order.le_refl (-22))
  have gapForSix : (9 : Int) ≤ 5 * GaussianInt.normInt previousDigit - 22 := by
    have nineLower : (9 : Int) ≤ 5 * 11 - 22 := by decide
    have scaledLower : (5 : Int) * 11 - 22 ≤ 5 * GaussianInt.normInt previousDigit - 22 := by
      rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
      exact shiftedScaledLarge
    exact Int.Order.le_trans nineLower scaledLower
  have shiftedLarge := Int.Order.add_le_add normIntLarge (Int.Order.le_refl (-6))
  have gapForTwo : (5 : Int) ≤ GaussianInt.normInt previousDigit - 6 := by
    calc
      (5 : Int) = 11 - 6 := by decide
      _ ≤ GaussianInt.normInt previousDigit - 6 := by
        rw [_root_.sub_eq_add_neg, _root_.sub_eq_add_neg]
        exact shiftedLarge
  have gapToLower :
      form.constant + 3 ≤
        (form.constant - 1) * GaussianInt.normInt previousDigit + form.radial -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) := by
    cases exceptional <;> dsimp only
    all_goals first
      | convert gapForSix using 1 <;> ring1
      | convert gapForTwo using 1 <;> ring1
  have constantGap :
      form.constant + 3 ≤ (form.pullback previousDigit).constant := by
    exact Int.Order.le_trans gapToLower lower
  have scalePositive : 0 < (form.constant : Fraction.Rational) + 1 := by
    cases exceptional <;> decide
  have determinantValue : form.determinant = -2 := by
    cases exceptional <;> decide
  exact Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
    form previousDigit value valueInside scalePositive determinantValue
      constantGap

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- Membership in the eight exact integral Lakein root forms. -/
private inductive IsLakeinRootForm :
  Geometry.Hermitian.Binary.IntegralHermitianForm → Prop
  /-- The root form with cross coefficients `(-3) (-1)`. -/ | c01 :
    IsLakeinRootForm (lakeinRootForm (-3) (-1))
  /-- The root form with cross coefficients `(-3) 1`. -/ | c02 :
    IsLakeinRootForm (lakeinRootForm (-3) 1)
  /-- The root form with cross coefficients `(-1) (-3)`. -/ | c03 :
    IsLakeinRootForm (lakeinRootForm (-1) (-3))
  /-- The root form with cross coefficients `(-1) 3`. -/ | c04 :
    IsLakeinRootForm (lakeinRootForm (-1) 3)
  /-- The root form with cross coefficients `1 (-3)`. -/ | c05 :
    IsLakeinRootForm (lakeinRootForm 1 (-3))
  /-- The root form with cross coefficients `1 3`. -/ | c06 :
    IsLakeinRootForm (lakeinRootForm 1 3)
  /-- The root form with cross coefficients `3 (-1)`. -/ | c07 :
    IsLakeinRootForm (lakeinRootForm 3 (-1))
  /-- The root form with cross coefficients `3 1`. -/ | c08 :
    IsLakeinRootForm (lakeinRootForm 3 1)

/-- Membership in the eight augmented root forms with constant eight and radial coefficient six.

Their cross coefficients have magnitudes seven and one, in either coordinate order. -/
private inductive IsLakeinAugmentedRootForm :
    Geometry.Hermitian.Binary.IntegralHermitianForm → Prop
  /-- The augmented root form with coefficients (8, 6, 7, 1). -/ | c01 :
    IsLakeinAugmentedRootForm ⟨8, 6, 7, 1⟩
  /-- The augmented root form with coefficients (8, 6, 7, -1). -/ | c02 :
    IsLakeinAugmentedRootForm ⟨8, 6, 7, -1⟩
  /-- The augmented root form with coefficients (8, 6, -7, 1). -/ | c03 :
    IsLakeinAugmentedRootForm ⟨8, 6, -7, 1⟩
  /-- The augmented root form with coefficients (8, 6, -7, -1). -/ | c04 :
    IsLakeinAugmentedRootForm ⟨8, 6, -7, -1⟩
  /-- The augmented root form with coefficients (8, 6, 1, 7). -/ | c05 :
    IsLakeinAugmentedRootForm ⟨8, 6, 1, 7⟩
  /-- The augmented root form with coefficients (8, 6, -1, 7). -/ | c06 :
    IsLakeinAugmentedRootForm ⟨8, 6, -1, 7⟩
  /-- The augmented root form with coefficients (8, 6, 1, -7). -/ | c07 :
    IsLakeinAugmentedRootForm ⟨8, 6, 1, -7⟩
  /-- The augmented root form with coefficients (8, 6, -1, -7). -/ | c08 :
    IsLakeinAugmentedRootForm ⟨8, 6, -1, -7⟩

/-- An integral certificate that a Hermitian form is nonnegative on the closed unit disk.

The radial coefficient plus one is positive, and the corresponding constant-minus-one determinant gap is nonnegative. -/
private def HasLakeinSlackOneCertificate
    (form : Geometry.Hermitian.Binary.IntegralHermitianForm) : Prop :=
  0 < form.radial + 1 ∧
    0 ≤ (form.constant - 1) * (form.radial + 1) -
      (form.realCross * form.realCross +
        form.imaginaryCross * form.imaginaryCross)

/-- Decide the slack-one certificate by its two finite integer inequalities. -/
private instance hasLakeinSlackOneCertificateDecidable
    (form : Geometry.Hermitian.Binary.IntegralHermitianForm) :
    Decidable (HasLakeinSlackOneCertificate form) := by
  unfold HasLakeinSlackOneCertificate
  infer_instance

/-- A form is a Lakein root, an augmented root, or has the integral slack-one certificate.

These alternatives preserve the exact form whose evaluation is to be bounded. -/
private def IsLakeinSafeForm (form :
  Geometry.Hermitian.Binary.IntegralHermitianForm) : Prop :=
  IsLakeinRootForm form ∨ IsLakeinAugmentedRootForm form ∨
    HasLakeinSlackOneCertificate form

/-- Classify the second pullback of the exceptional form `⟨6, 4, 1, 5⟩` with following digit `⟨1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC01_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, 5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, 1, -3⟩` with following digit `⟨1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC02_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 1, -3⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 5, 1⟩` with following digit `⟨2, 0⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC03_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c08
    | exact Or.inl ForbiddenSmallSuccessor.c11
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, 1, 3⟩` with following digit `⟨1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC04_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 1, 3⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 1, -5⟩` with following digit `⟨1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC05_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, -5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 5, -1⟩` with following digit `⟨2, 0⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC06_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c08
    | exact Or.inl ForbiddenSmallSuccessor.c11
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, 3, -1⟩` with following digit `⟨1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC07_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 3, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -5, -1⟩` with following digit `⟨-1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC08_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -1, -5⟩` with following digit `⟨0, -2⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC09_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, -2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, -5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c06
    | exact Or.inl ForbiddenSmallSuccessor.c20
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, 3, 1⟩` with following digit `⟨1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC10_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, 3, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -5, 1⟩` with following digit `⟨-1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC11_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -1, 5⟩` with following digit `⟨0, 2⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC12_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, 2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, 5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c09
    | exact Or.inl ForbiddenSmallSuccessor.c23
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 5, -1⟩` with following digit `⟨1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC13_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c01
    | exact Or.inl ForbiddenSmallSuccessor.c02
    | exact Or.inl ForbiddenSmallSuccessor.c05
    | exact Or.inl ForbiddenSmallSuccessor.c07
    | exact Or.inl ForbiddenSmallSuccessor.c14
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, -3, -1⟩` with following digit `⟨-1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC14_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -3, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 1, -5⟩` with following digit `⟨0, -2⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC15_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, -2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, -5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c06
    | exact Or.inl ForbiddenSmallSuccessor.c20
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 5, 1⟩` with following digit `⟨1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC16_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 5, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c03
    | exact Or.inl ForbiddenSmallSuccessor.c04
    | exact Or.inl ForbiddenSmallSuccessor.c10
    | exact Or.inl ForbiddenSmallSuccessor.c12
    | exact Or.inl ForbiddenSmallSuccessor.c16
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, -3, 1⟩` with following digit `⟨-1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC17_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -3, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, 1, 5⟩` with following digit `⟨0, 2⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC18_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨0, 2⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, 1, 5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c09
    | exact Or.inl ForbiddenSmallSuccessor.c23
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -1, 5⟩` with following digit `⟨-1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC19_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, 5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, -1, -3⟩` with following digit `⟨-1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC20_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -1, -3⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -5, 1⟩` with following digit `⟨-2, 0⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC21_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c18
    | exact Or.inl ForbiddenSmallSuccessor.c21
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨2, 4, -1, 3⟩` with following digit `⟨-1, 1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC22_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, 1⟩ ∨
      IsLakeinSafeForm
        ((⟨2, 4, -1, 3⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c15
    | exact Or.inl ForbiddenSmallSuccessor.c22
    | exact Or.inl ForbiddenSmallSuccessor.c24
    | exact Or.inl ForbiddenSmallSuccessor.c27
    | exact Or.inl ForbiddenSmallSuccessor.c28
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -1, -5⟩` with following digit `⟨-1, -1⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC23_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-1, -1⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -1, -5⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c13
    | exact Or.inl ForbiddenSmallSuccessor.c17
    | exact Or.inl ForbiddenSmallSuccessor.c19
    | exact Or.inl ForbiddenSmallSuccessor.c25
    | exact Or.inl ForbiddenSmallSuccessor.c26
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- Classify the second pullback of the exceptional form `⟨6, 4, -5, -1⟩` with following digit `⟨-2, 0⟩`.

For each of the 32 small preceding digits, the result is either a forbidden succession or the exact safe-form
certificate. -/
private theorem exceptionalC24_second_classification
    (previousDigit : GaussianInt)
    (small : IsSmallPreviousDigit previousDigit) :
    IsForbiddenSmallSuccessorPair previousDigit ⟨-2, 0⟩ ∨
      IsLakeinSafeForm
        ((⟨6, 4, -5, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).pullback previousDigit) := by
  cases small <;> first
    | exact Or.inl ForbiddenSmallSuccessor.c18
    | exact Or.inl ForbiddenSmallSuccessor.c21
    | exact Or.inr (Or.inl (by constructor))
    | exact Or.inr (Or.inr (Or.inl (by constructor)))
    | exact Or.inr (Or.inr (Or.inr (by decide)))

/-- The augmented form `⟨8, 6, 7, 1⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem evaluate_augmented_seven_one_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 7, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 3 1 IsLakeinRootCross.positiveThreePositiveOne)
    (1 : GaussianInt) (Or.inl rfl)
  have identity :
      (⟨8, 6, 7, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, 3 + 4 * (1 : GaussianInt).re,
          1 + 4 * (1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, 7, -1⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_seven_negative_one_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 7, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 3 (-1) IsLakeinRootCross.positiveThreeNegativeOne)
    (1 : GaussianInt) (Or.inl rfl)
  have identity :
      (⟨8, 6, 7, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, 3 + 4 * (1 : GaussianInt).re,
          -1 + 4 * (1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, -7, 1⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_negative_seven_one_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -7, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-3) 1 IsLakeinRootCross.negativeThreePositiveOne)
    (-1 : GaussianInt) (Or.inr (Or.inl rfl))
  have identity :
      (⟨8, 6, -7, 1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, -3 + 4 * (-1 : GaussianInt).re,
          1 + 4 * (-1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, -7, -1⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_negative_seven_negative_one_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -7, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-3) (-1)
      IsLakeinRootCross.negativeThreeNegativeOne)
    (-1 : GaussianInt) (Or.inr (Or.inl rfl))
  have identity :
      (⟨8, 6, -7, -1⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, -3 + 4 * (-1 : GaussianInt).re,
          -1 + 4 * (-1 : GaussianInt).im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, 1, 7⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem evaluate_augmented_one_seven_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 1, 7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 1 3 IsLakeinRootCross.positiveOnePositiveThree)
    GaussianInt.Norm.Small.imaginaryUnit (Or.inr (Or.inr (Or.inl rfl)))
  have identity :
      (⟨8, 6, 1, 7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, 1 + 4 * GaussianInt.Norm.Small.imaginaryUnit.re,
          3 + 4 * GaussianInt.Norm.Small.imaginaryUnit.im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, -1, 7⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_negative_one_seven_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -1, 7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-1) 3 IsLakeinRootCross.negativeOnePositiveThree)
    GaussianInt.Norm.Small.imaginaryUnit (Or.inr (Or.inr (Or.inl rfl)))
  have identity :
      (⟨8, 6, -1, 7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, -1 + 4 * GaussianInt.Norm.Small.imaginaryUnit.re,
          3 + 4 * GaussianInt.Norm.Small.imaginaryUnit.im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, 1, -7⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_one_negative_seven_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, 1, -7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative 1 (-3) IsLakeinRootCross.positiveOneNegativeThree)
    (-GaussianInt.Norm.Small.imaginaryUnit) (Or.inr (Or.inr (Or.inr rfl)))
  have identity :
      (⟨8, 6, 1, -7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, 1 + 4 * (-GaussianInt.Norm.Small.imaginaryUnit).re,
          -3 + 4 * (-GaussianInt.Norm.Small.imaginaryUnit).im⟩ := by decide
  rw [identity]
  exact transformed

/-- The augmented form `⟨8, 6, -1, -7⟩` is nonnegative wherever all Lakein root forms are nonnegative.

Its value is a root-form value plus four times a unit-translated squared norm. -/
private theorem
  evaluate_augmented_negative_one_negative_seven_nonnegative
    (value : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (⟨8, 6, -1, -7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm).evaluate value := by
  have transformed := evaluate_root_plus_four_unit_square_nonnegative value
    (rootNonnegative (-1) (-3)
      IsLakeinRootCross.negativeOneNegativeThree)
    (-GaussianInt.Norm.Small.imaginaryUnit) (Or.inr (Or.inr (Or.inr rfl)))
  have identity :
      (⟨8, 6, -1, -7⟩ : Geometry.Hermitian.Binary.IntegralHermitianForm) =
        ⟨8, 6, -1 + 4 * (-GaussianInt.Norm.Small.imaginaryUnit).re,
          -3 + 4 * (-GaussianInt.Norm.Small.imaginaryUnit).im⟩ := by decide
  rw [identity]
  exact transformed

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.IsLakeinSafeForm

/-- A safe form evaluates nonnegatively inside the unit disk when all root forms are nonnegative there.

The three cases use the supplied root inequalities, unit-square augmentation, or the integral slack-one certificate. -/
private theorem evaluate_nonnegative
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {value : Gaussian.Basic.Canonical}
    (safe : IsLakeinSafeForm form) (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ form.evaluate value := open Purelib.Algebra in by
  rcases safe with root | augmented | slack
  · cases root
    · exact rootNonnegative (-3) (-1)
        Lakein.IsLakeinRootCross.negativeThreeNegativeOne
    · exact rootNonnegative (-3) 1
        Lakein.IsLakeinRootCross.negativeThreePositiveOne
    · exact rootNonnegative (-1) (-3)
        Lakein.IsLakeinRootCross.negativeOneNegativeThree
    · exact rootNonnegative (-1) 3
        Lakein.IsLakeinRootCross.negativeOnePositiveThree
    · exact rootNonnegative 1 (-3)
        Lakein.IsLakeinRootCross.positiveOneNegativeThree
    · exact rootNonnegative 1 3
        Lakein.IsLakeinRootCross.positiveOnePositiveThree
    · exact rootNonnegative 3 (-1)
        Lakein.IsLakeinRootCross.positiveThreeNegativeOne
    · exact rootNonnegative 3 1
        Lakein.IsLakeinRootCross.positiveThreePositiveOne
  · cases augmented
    · exact Lakein.evaluate_augmented_seven_one_nonnegative value rootNonnegative
    · exact Lakein.evaluate_augmented_seven_negative_one_nonnegative value
        rootNonnegative
    · exact Lakein.evaluate_augmented_negative_seven_one_nonnegative value
        rootNonnegative
    · exact Lakein.evaluate_augmented_negative_seven_negative_one_nonnegative value
        rootNonnegative
    · exact Lakein.evaluate_augmented_one_seven_nonnegative value rootNonnegative
    · exact Lakein.evaluate_augmented_negative_one_seven_nonnegative value
        rootNonnegative
    · exact Lakein.evaluate_augmented_one_negative_seven_nonnegative value
        rootNonnegative
    · exact Lakein.evaluate_augmented_negative_one_negative_seven_nonnegative value
        rootNonnegative
  · change
      0 < form.radial + 1 ∧
        0 ≤ (form.constant - 1) * (form.radial + 1) -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross) at slack
    have scaleCast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct
        1 (form.radial + 1)).2 (by omega)
    have scalePositive : 0 < (form.radial : Fraction.Rational) + 1 := by
      have onePositive : (0 : Fraction.Rational) < 1 := by decide
      apply onePositive.trans_le
      simpa only [Int.cast_one, Ring.IntCast.add] using scaleCast
    have gapCast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct 0
        ((form.constant - 1) * (form.radial + 1) -
          (form.realCross * form.realCross +
            form.imaginaryCross * form.imaginaryCross))).2 slack.2
    have determinantGap :
        0 ≤ ((form.constant : Fraction.Rational) - 1) *
            ((form.radial : Fraction.Rational) + 1) -
          ((form.realCross : Fraction.Rational) ^ 2 +
            (form.imaginaryCross : Fraction.Rational) ^ 2) := by
      simpa only [Ring.IntCast.cast_zero, Ring.IntCast.sub, Int.cast_one, Ring.IntCast.intCast_mul,
        Ring.IntCast.add, pow_two] using gapCast
    exact Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate_nonnegative_of_slack_one
      form value valueInside scalePositive determinantGap

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.IsLakeinSafeForm

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- A second pullback by a digit of norm two through ten either records a forbidden succession or produces a safe form.

The 24 first-step exceptions and 32 possible preceding digits are checked by the explicit case lemmas. -/
private theorem
  exceptional_second_pullback_classification_of_small
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ GaussianInt.normNat previousDigit)
    (small : GaussianInt.normNat previousDigit < 11) :
    IsForbiddenSmallSuccessorPair previousDigit followingDigit ∨
      IsLakeinSafeForm (form.pullback previousDigit) := by
  have digitSmall := isSmallPreviousDigit_of_norm_bounds previousDigit
    previousNorm small
  cases exceptional
  · exact exceptionalC01_second_classification previousDigit digitSmall
  · exact exceptionalC02_second_classification previousDigit digitSmall
  · exact exceptionalC03_second_classification previousDigit digitSmall
  · exact exceptionalC04_second_classification previousDigit digitSmall
  · exact exceptionalC05_second_classification previousDigit digitSmall
  · exact exceptionalC06_second_classification previousDigit digitSmall
  · exact exceptionalC07_second_classification previousDigit digitSmall
  · exact exceptionalC08_second_classification previousDigit digitSmall
  · exact exceptionalC09_second_classification previousDigit digitSmall
  · exact exceptionalC10_second_classification previousDigit digitSmall
  · exact exceptionalC11_second_classification previousDigit digitSmall
  · exact exceptionalC12_second_classification previousDigit digitSmall
  · exact exceptionalC13_second_classification previousDigit digitSmall
  · exact exceptionalC14_second_classification previousDigit digitSmall
  · exact exceptionalC15_second_classification previousDigit digitSmall
  · exact exceptionalC16_second_classification previousDigit digitSmall
  · exact exceptionalC17_second_classification previousDigit digitSmall
  · exact exceptionalC18_second_classification previousDigit digitSmall
  · exact exceptionalC19_second_classification previousDigit digitSmall
  · exact exceptionalC20_second_classification previousDigit digitSmall
  · exact exceptionalC21_second_classification previousDigit digitSmall
  · exact exceptionalC22_second_classification previousDigit digitSmall
  · exact exceptionalC23_second_classification previousDigit digitSmall
  · exact exceptionalC24_second_classification previousDigit digitSmall

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

/-- A second pullback of an exceptional form is nonnegative for an allowed preceding digit of norm below eleven.

The evaluation point lies in the closed unit disk and satisfies all root-form inequalities; the forbidden succession
branch is excluded explicitly. -/
private theorem
  pullback_nonnegative_of_small
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ GaussianInt.normNat previousDigit)
    (small : GaussianInt.normNat previousDigit < 11)
    (notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit)
    (value : Gaussian.Basic.Canonical) (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  rcases Lakein.exceptional_second_pullback_classification_of_small exceptional
      previousDigit previousNorm small with forbidden | safe
  · exact (notForbidden forbidden).elim
  · exact safe.evaluate_nonnegative valueInside rootNonnegative

/-- Every exceptional first pullback is nonnegative after the preceding
Hurwitz step.  Large preceding digits are settled by the determinant
certificate; the finitely many small digits are exactly the preceding table,
with the impossible entries removed by Hurwitz succession. -/
theorem pullback_nonnegative
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {followingDigit : GaussianInt}
    (exceptional : FirstExceptionalHermitian form followingDigit)
    (previousDigit : GaussianInt)
    (previousNorm : 2 ≤ GaussianInt.normNat previousDigit)
    (notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit)
    (value : Gaussian.Basic.Canonical) (valueInside : Data.Gaussian.Norm.Basic.normSq value ≤ 1)
    (rootNonnegative : LakeinRootFormsNonnegative value) :
    0 ≤ (form.pullback previousDigit).evaluate value := by
  by_cases large : 11 ≤ GaussianInt.normNat previousDigit
  · exact exceptional.pullback_nonnegative_of_large previousDigit large value
      valueInside
  · exact exceptional.pullback_nonnegative_of_small previousDigit previousNorm
      (Nat.lt_of_not_ge large) notForbidden value valueInside rootNonnegative

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- The affine denominator in one backward-ratio step cannot vanish.  The
proof uses only the strict growth of the two displayed continuant
denominators and the finite lower bound on the next Hurwitz digit. -/
theorem denominatorRatio_step_sum_ne_zero
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0) :
    GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
      stage.quotient nonterminal)) +
        (Stage.denominatorRatio stage) ≠ 0 := by
  let coefficient := GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
    nonterminal)
  intro sumZero
  have ratioIdentity :
      (Stage.denominatorRatio stage) = -(GaussianInt.toGaussian coefficient) := by
    apply Gaussian.Basic.ext
    · have realZero := congrArg
        Gaussian.Basic.re sumZero
      simp only [Gaussian.Basic.add_re, GaussianInt.toGaussian,
        ← Rat.Fraction.Cast.intCast_eq_fromInt] at realZero
      change (coefficient.re : Fraction.Rational) +
          (Stage.denominatorRatio stage).re = 0 at realZero
      calc
        (Stage.denominatorRatio stage).re =
            ((coefficient.re : Fraction.Rational) +
                (Stage.denominatorRatio stage).re) -
              (coefficient.re : Fraction.Rational) := by ring1
        _ = 0 - (coefficient.re : Fraction.Rational) := by rw [realZero]
        _ = (-(GaussianInt.toGaussian coefficient)).re := by
          simp only [Gaussian.Basic.neg_re, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
    · have imaginaryZero := congrArg
        Gaussian.Basic.im sumZero
      simp only [Gaussian.Basic.add_im, GaussianInt.toGaussian,
        ← Rat.Fraction.Cast.intCast_eq_fromInt] at imaginaryZero
      change (coefficient.im : Fraction.Rational) +
          (Stage.denominatorRatio stage).im = 0 at imaginaryZero
      calc
        (Stage.denominatorRatio stage).im =
            ((coefficient.im : Fraction.Rational) +
                (Stage.denominatorRatio stage).im) -
              (coefficient.im : Fraction.Rational) := by ring1
        _ = 0 - (coefficient.im : Fraction.Rational) := by rw [imaginaryZero]
        _ = (-(GaussianInt.toGaussian coefficient)).im := by
          simp only [Gaussian.Basic.neg_im, GaussianInt.toGaussian, ← Rat.Fraction.Cast.intCast_eq_fromInt]
          ring1
  have coefficientNorm : 2 ≤ GaussianInt.normNat coefficient :=
    Hurwitz.Geometry.two_le_next_digit_normNat stage.quotient nonterminal
  have coefficientNormCast :
      (2 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian coefficient) := by
    rw [GaussianInt.normSq_toGaussian]
    exact Fraction.Cast.Order.natCast_le_direct coefficientNorm
  have ratioAtLeastOne :
      (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq (Stage.denominatorRatio stage) := by
    rw [ratioIdentity, Gaussian.Norm.Basic.normSq_neg]
    exact (show (1 : Fraction.Rational) ≤ 2 by decide).trans coefficientNormCast
  exact (not_lt_of_ge ratioAtLeastOne)
    (denominatorRatio_normSq_lt_one_of_generated generated)

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.Geometry.Hermitian.Binary.IntegralHermitianForm

/-- Nonnegativity of a pulled-back Hermitian form transports through one
explicit Hurwitz advance. -/
theorem evaluate_advance_nonnegative_of_pullback
    (form : Geometry.Hermitian.Binary.IntegralHermitianForm)
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (pullbackNonnegative :
      0 ≤ (form.pullback
        (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
          nonterminal))).evaluate
          (Lakein.Stage.denominatorRatio stage)) :
    0 ≤ form.evaluate
      (Lakein.Stage.denominatorRatio
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal)) := by
  let coefficient := GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient
    nonterminal)
  let sum := GaussianInt.toGaussian coefficient + (Lakein.Stage.denominatorRatio stage)
  have sumNonzero : sum ≠ 0 := by
    exact Lakein.denominatorRatio_step_sum_ne_zero generated nonterminal
  have normPositive : 0 < Data.Gaussian.Norm.Basic.normSq sum := Gaussian.Norm.Basic.normSq_pos sumNonzero
  have transformed := form.evaluate_pullback_mul_normSq coefficient
    (Lakein.Stage.denominatorRatio stage) sumNonzero
  have productNonnegative :
      0 ≤ form.evaluate sum⁻¹ * Data.Gaussian.Norm.Basic.normSq sum := by
    rw [transformed]
    exact pullbackNonnegative
  have evaluatedNonnegative : 0 ≤ form.evaluate sum⁻¹ := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := Data.Gaussian.Norm.Basic.normSq sum) _ normPositive
    calc
      0 * Data.Gaussian.Norm.Basic.normSq sum = 0 := by ring1
      _ ≤ form.evaluate sum⁻¹ * Data.Gaussian.Norm.Basic.normSq sum := productNonnegative
  rw [Lakein.advanceStage_denominatorRatio stage generated nonterminal]
  exact evaluatedNonnegative

end Purelib.Geometry.Hermitian.Binary.IntegralHermitianForm

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- All eight Lakein root forms are nonnegative at zero. -/
private theorem lakeinRootFormsNonnegative_zero :
    LakeinRootFormsNonnegative 0 := by
  intro realCross imaginaryCross root
  cases root <;>
    decide

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

/-- Every first-step exceptional Hermitian form is nonnegative at zero. -/
private theorem
  evaluate_zero_nonnegative
    {form : Geometry.Hermitian.Binary.IntegralHermitianForm} {coefficient : GaussianInt}
    (exceptional : FirstExceptionalHermitian form coefficient) :
    0 ≤ form.evaluate 0 := by
  cases exceptional <;> decide

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.FirstExceptionalHermitian

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- A root form pulled back by a digit of quadrance at least two is nonnegative at zero. -/
private theorem root_pullback_nonnegative_at_zero
    {realCross imaginaryCross : Int}
    (root : IsLakeinRootCross realCross imaginaryCross)
    (coefficient : GaussianInt) (coefficientNorm : 2 ≤ GaussianInt.normNat coefficient) :
    0 ≤ ((lakeinRootForm realCross imaginaryCross).pullback coefficient).evaluate
      0 := by
  rcases root_pullback_constant_gap_or_exceptional root coefficient
      coefficientNorm with constantGap | exceptional
  · exact
      Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
        (lakeinRootForm realCross imaginaryCross) coefficient 0
        (by decide) (by
          change (0 : Fraction.Rational) < 4 + 1
          decide)
        (lakeinRootForm_determinant root) constantGap
  · exact exceptional.evaluate_zero_nonnegative

/-- All root forms are nonnegative at the denominator ratio after the first nonterminal Hurwitz advance. -/
private theorem firstAdvance_lakeinRootFormsNonnegative
    (source : GaussianInt.Fraction) (nonterminal : GaussianInt.Division.Nearest.remainder source ≠ 0) :
    LakeinRootFormsNonnegative
      (Stage.denominatorRatio
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
          (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal)) := by
  intro realCross imaginaryCross root
  apply Purelib.Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
    (lakeinRootForm realCross imaginaryCross) Hurwitz.Geometry.Generated.first nonterminal
  rw [firstStage_denominatorRatio]
  exact root_pullback_nonnegative_at_zero root _
    (Hurwitz.Geometry.two_le_next_digit_normNat source nonterminal)

/-- Assuming the root forms at one generated stage, the explicit
two-successor classification establishes them two stages later. -/
private theorem lakeinRootFormsNonnegative_two_advances
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (nextNonterminal :
      GaussianInt.Division.Nearest.remainder
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal).quotient ≠ 0)
    (rootNonnegative :
      LakeinRootFormsNonnegative (Stage.denominatorRatio stage)) :
    LakeinRootFormsNonnegative
      (Stage.denominatorRatio
        (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal)
          nextNonterminal)) := by
  let middle := Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal
  let previousDigit := GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
    stage.quotient nonterminal)
  let followingDigit := GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
    middle.quotient nextNonterminal)
  have middleGenerated : Hurwitz.Geometry.Generated source middle :=
    Hurwitz.Geometry.Generated.advance generated nonterminal
  have baseInside : Data.Gaussian.Norm.Basic.normSq (Stage.denominatorRatio stage) ≤ 1 :=
    (denominatorRatio_normSq_lt_one_of_generated generated).le
  have middleInside : Data.Gaussian.Norm.Basic.normSq (Stage.denominatorRatio middle) ≤ 1 :=
    (denominatorRatio_normSq_lt_one_of_generated middleGenerated).le
  have previousNorm : 2 ≤ GaussianInt.normNat previousDigit := by
    exact Hurwitz.Geometry.two_le_next_digit_normNat stage.quotient nonterminal
  have followingNorm : 2 ≤ GaussianInt.normNat followingDigit := by
    exact Hurwitz.Geometry.two_le_next_digit_normNat middle.quotient nextNonterminal
  have notForbidden :
      ¬ ForbiddenSmallSuccessor previousDigit followingDigit := by
    change ¬ ForbiddenSmallSuccessor
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal))
      (GaussianInt.Division.Nearest.digit (Data.ComplexContinuedFraction.Hurwitz.Step.next
        (Data.ComplexContinuedFraction.Hurwitz.Step.next stage.quotient nonterminal) nextNonterminal))
    exact not_forbiddenSmallSuccessor stage.quotient nonterminal
      nextNonterminal
  intro realCross imaginaryCross root
  have firstPullbackNonnegative :
      0 ≤ ((lakeinRootForm realCross imaginaryCross).pullback
        followingDigit).evaluate (Stage.denominatorRatio middle) := by
    rcases root_pullback_constant_gap_or_exceptional root followingDigit
        followingNorm with constantGap | exceptional
    · exact
        Geometry.Hermitian.Binary.IntegralHermitianForm.pullback_evaluate_nonnegative_of_constant_gap
          (lakeinRootForm realCross imaginaryCross) followingDigit
          (Stage.denominatorRatio middle) middleInside (by
            change (0 : Fraction.Rational) < 4 + 1
            decide)
          (lakeinRootForm_determinant root) constantGap
    · have secondPullbackNonnegative :
          0 ≤ (((lakeinRootForm realCross imaginaryCross).pullback
            followingDigit).pullback previousDigit).evaluate
              (Stage.denominatorRatio stage) := by
        exact exceptional.pullback_nonnegative previousDigit previousNorm
          notForbidden (Stage.denominatorRatio stage) baseInside rootNonnegative
      have transported :=
        Purelib.Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
          ((lakeinRootForm realCross imaginaryCross).pullback followingDigit)
          generated nonterminal secondPullbackNonnegative
      exact transported
  exact Purelib.Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate_advance_nonnegative_of_pullback
    (lakeinRootForm realCross imaginaryCross) middleGenerated nextNonterminal
    firstPullbackNonnegative

/-- The induction invariant remembers the root inequalities both at the
current generated stage and after each possible next advance.  This makes
the two-step exceptional calculation line up exactly with the unary
`Generated` recursion. -/
private def LakeinRootStageInvariant {source :
  GaussianInt.Fraction}
    (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source) : Prop :=
  LakeinRootFormsNonnegative (Stage.denominatorRatio stage) ∧
    ∀ nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0,
      LakeinRootFormsNonnegative
        (Stage.denominatorRatio
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage stage nonterminal))

/-- Every finitely generated Hurwitz stage retains root-form nonnegativity both now and after its next nonterminal
advance.

The paired invariant propagates the two-step exceptional classification through the unary generation relation. -/
private theorem lakeinRootStageInvariant_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage) :
    LakeinRootStageInvariant stage := by
  induction generated with
  | first =>
      constructor
      · rw [firstStage_denominatorRatio]
        exact lakeinRootFormsNonnegative_zero
      · intro nonterminal
        exact firstAdvance_lakeinRootFormsNonnegative source nonterminal
  | @advance previousStage generated previousNonterminal inductionHypothesis =>
      constructor
      · exact inductionHypothesis.2 previousNonterminal
      · intro nextNonterminal
        exact lakeinRootFormsNonnegative_two_advances generated
          previousNonterminal nextNonterminal inductionHypothesis.1

/-- All eight quadrance-five/diagonal root forms are nonnegative at every
stage produced by the finite Hurwitz trace. -/
theorem lakeinRootFormsNonnegative_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage) :
    LakeinRootFormsNonnegative (Stage.denominatorRatio stage) :=
  (lakeinRootStageInvariant_of_generated generated).1

/-- A norm-five coefficient plus a diagonal multiple of a ratio has quadrance one plus its exact Lakein root form.

The cross coefficients are the displayed integral bilinear expressions in the two Gaussian coefficients. -/
private theorem normFive_diagonal_factor_identity
    (ratio : Gaussian.Basic.Canonical) (s t : GaussianInt)
    (sNorm : GaussianInt.normNat s = 5) (tNorm : GaussianInt.normNat t = 2) :
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s + GaussianInt.toGaussian t * ratio) =
      1 +
        (lakeinRootForm
          (s.re * t.re + s.im * t.im)
          (-s.re * t.im + s.im * t.re)).evaluate ratio := open Purelib.Algebra in by
  have castNeg (value : Int) : ((-value : Int) : Fraction.Rational) = -(value : Fraction.Rational) :=
    Ring.IntCast.neg value
  have sNormIdentity : Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s) = 5 := by
    rw [GaussianInt.normSq_toGaussian, sNorm]
    rfl
  have tNormIdentity : Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian t) = 2 := by
    rw [GaussianInt.normSq_toGaussian, tNorm]
    rfl
  calc
    Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s + GaussianInt.toGaussian t * ratio) =
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s) + Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian t) * Data.Gaussian.Norm.Basic.normSq ratio +
          2 *
            (((s.re * t.re + s.im * t.im : Int) : Fraction.Rational) * ratio.re +
              ((-s.re * t.im + s.im * t.re : Int) : Fraction.Rational) *
                ratio.im) := by
      simp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
        Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
        Ring.IntCast.add, Ring.IntCast.intCast_mul, castNeg, ← Rat.Fraction.Cast.intCast_eq_fromInt]
      ring1
    _ = 5 + 2 * Data.Gaussian.Norm.Basic.normSq ratio +
          2 *
            (((s.re * t.re + s.im * t.im : Int) : Fraction.Rational) * ratio.re +
              ((-s.re * t.im + s.im * t.re : Int) : Fraction.Rational) *
                ratio.im) := by
      rw [sNormIdentity, tNormIdentity]
    _ = 1 +
        (lakeinRootForm
          (s.re * t.re + s.im * t.im)
          (-s.re * t.im + s.im * t.re)).evaluate ratio := by
      simp only [Geometry.Hermitian.Binary.IntegralHermitianForm.evaluate, lakeinRootForm,
        Geometry.Hermitian.Binary.hermitianForm, Int.cast_ofNat, Ring.IntCast.add, Ring.IntCast.intCast_mul]
      ring1

/-- The cross coefficients of a norm-five/diagonal pair belong to the eight-element Lakein root relation. -/
private theorem normFive_diagonal_cross_isLakeinRoot
    {s t : GaussianInt} (sNorm : GaussianInt.normNat s = 5)
    (tNorm : GaussianInt.normNat t = 2) :
    IsLakeinRootCross
      (s.re * t.re + s.im * t.im)
      (-s.re * t.im + s.im * t.re) := by
  have sCases := GaussianInt.Norm.Small.normFive_cases_of_normNat_eq_five sNorm
  have tCases := GaussianInt.Norm.Small.isDiagonal_of_normNat_eq_two tNorm
  rcases sCases with sCase | sCase | sCase | sCase | sCase | sCase |
      sCase | sCase <;>
    rcases tCases with tCase | tCase | tCase | tCase <;>
    subst s <;> subst t
  all_goals first
    | exact IsLakeinRootCross.negativeThreeNegativeOne
    | exact IsLakeinRootCross.negativeThreePositiveOne
    | exact IsLakeinRootCross.negativeOneNegativeThree
    | exact IsLakeinRootCross.negativeOnePositiveThree
    | exact IsLakeinRootCross.positiveOneNegativeThree
    | exact IsLakeinRootCross.positiveOnePositiveThree
    | exact IsLakeinRootCross.positiveThreeNegativeOne
    | exact IsLakeinRootCross.positiveThreePositiveOne

/-- The eight root-form inequalities are precisely the exterior certificate
for every quadrance-five coefficient paired with a diagonal coefficient. -/
theorem one_le_normSq_normFive_add_diagonal_mul_of_rootForms
    (ratio : Gaussian.Basic.Canonical) (rootNonnegative : LakeinRootFormsNonnegative ratio)
    (s t : GaussianInt) (sNorm : GaussianInt.normNat s = 5)
    (tNorm : GaussianInt.normNat t = 2) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s + GaussianInt.toGaussian t * ratio) := by
  let realCross := s.re * t.re + s.im * t.im
  let imaginaryCross := -s.re * t.im + s.im * t.re
  have root : IsLakeinRootCross realCross imaginaryCross :=
    normFive_diagonal_cross_isLakeinRoot sNorm tNorm
  have rootBound := rootNonnegative realCross imaginaryCross root
  calc
    (1 : Fraction.Rational) = 1 + 0 := by ring1
    _ ≤ 1 + (lakeinRootForm realCross imaginaryCross).evaluate ratio :=
      by
        have shifted :=
          Fraction.Order.Arithmetic.add_le_add_right_direct rootBound 1
        calc
          (1 : Fraction.Rational) + 0 = 0 + 1 := by ring1
          _ ≤ (lakeinRootForm realCross imaginaryCross).evaluate ratio + 1 :=
            shifted
          _ = 1 + (lakeinRootForm realCross imaginaryCross).evaluate ratio := by
            ring1
    _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian s + GaussianInt.toGaussian t * ratio) := by
      exact (normFive_diagonal_factor_identity ratio s t sNorm tNorm).symm

/-- Root-form nonnegativity supplies the outstanding quadrance-five
denominator comparison at a generated stage. -/
theorem normFiveDenominatorSafe_of_rootForms
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage)
    (rootNonnegative :
      LakeinRootFormsNonnegative (Stage.denominatorRatio stage)) :
    Hurwitz.Geometry.NormFiveDenominatorSafe stage := by
  intro s t sNorm tNorm
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  let currentValue := GaussianInt.toGaussian stage.current.denominator
  let factor := GaussianInt.toGaussian s + GaussianInt.toGaussian t * (Stage.denominatorRatio stage)
  have factorExterior : 1 ≤ Data.Gaussian.Norm.Basic.normSq factor := by
    dsimp only [factor]
    exact one_le_normSq_normFive_add_diagonal_mul_of_rootForms
      (Stage.denominatorRatio stage) rootNonnegative s t sNorm tNorm
  have currentNormNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq currentValue :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have scaledExterior :
      1 * Data.Gaussian.Norm.Basic.normSq currentValue ≤ Data.Gaussian.Norm.Basic.normSq factor *
        Data.Gaussian.Norm.Basic.normSq currentValue :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      factorExterior currentNormNonnegative
  have factorIdentity :
      factor * currentValue =
        GaussianInt.toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator) := by
    dsimp only [factor, currentValue]
    rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  apply (Fraction.Cast.Order.natCast_le_iff_direct).1
  calc
    (GaussianInt.normNat stage.current.denominator : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq currentValue := (GaussianInt.normSq_toGaussian _).symm
    _ = 1 * Data.Gaussian.Norm.Basic.normSq currentValue := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq currentValue := scaledExterior
    _ = Data.Gaussian.Norm.Basic.normSq (factor * currentValue) := by rw [Gaussian.Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator)) := by rw [factorIdentity]
    _ = (GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) : Fraction.Rational) :=
      GaussianInt.normSq_toGaussian _

/-- Every generated Hurwitz stage satisfies the exceptional denominator
certificate required by Lakein's comparison. -/
theorem normFiveDenominatorSafe_of_generated
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage) :
    Hurwitz.Geometry.NormFiveDenominatorSafe stage :=
  normFiveDenominatorSafe_of_rootForms generated
    (lakeinRootFormsNonnegative_of_generated generated)

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein.Stage

/-- A terminal generated stage reconstructs the displayed rational source
exactly. -/
theorem current_error_eq_zero_of_terminal
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (terminal : GaussianInt.Division.Nearest.remainder stage.quotient = 0) :
    Best.Error.error source.value stage.current = 0 := by
  have residualZero : GaussianInt.Division.Nearest.residual stage.quotient = 0 := by
    apply Gaussian.Field.mul_right_cancel_of_ne
      stage.quotient.denominatorGaussianNonzero
    calc
      GaussianInt.Division.Nearest.residual stage.quotient *
            GaussianInt.toGaussian stage.quotient.denominator =
          GaussianInt.toGaussian (GaussianInt.Division.Nearest.remainder stage.quotient) :=
        (GaussianInt.Division.Nearest.remainder_toGaussian stage.quotient).symm
      _ = 0 := by rw [terminal, GaussianInt.toGaussian_zero]
      _ = 0 * GaussianInt.toGaussian stage.quotient.denominator := by
        rw [Gaussian.Basic.zero_mul]
  have relation := stage.error_add_residual_mul_previous_eq_zero
  rw [residualZero, Gaussian.Basic.zero_mul,
    Gaussian.Basic.add_zero] at relation
  exact relation

/-- Lakein's comparison at a nonterminal generated stage. -/
theorem atLeastAsGoodAs_of_generated_nonterminal
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (generated : Hurwitz.Geometry.Generated source stage)
    (nonterminal : GaussianInt.Division.Nearest.remainder stage.quotient ≠ 0)
    (competitor : GaussianInt.Pair.Basic.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      GaussianInt.normNat competitor.denominator < GaussianInt.normNat stage.current.denominator) :
    Best.Error.AtLeastAsGoodAs source.value stage.current competitor := by
  exact (Hurwitz.Geometry.Stage.atLeastAsGoodAs_of_generated_of_normFiveDenominatorSafe stage)
    generated (Lakein.normFiveDenominatorSafe_of_generated generated) nonterminal
    competitor competitorDenominatorNonzero denominatorSmaller

/-- **Finite Lakein inequality.**  Every displayed Hurwitz convergent is at
least as good as any Gaussian-rational competitor with strictly smaller
denominator quadrance.  At the terminal stage the displayed convergent is
exact; every earlier stage is covered by the finite root-form invariant. -/
theorem atLeastAsGoodAs_of_generated
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (generated : Hurwitz.Geometry.Generated source stage)
    (competitor : GaussianInt.Pair.Basic.ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      GaussianInt.normNat competitor.denominator < GaussianInt.normNat stage.current.denominator) :
    Best.Error.AtLeastAsGoodAs source.value stage.current competitor := by
  by_cases terminal : GaussianInt.Division.Nearest.remainder stage.quotient = 0
  · have currentErrorZero := (current_error_eq_zero_of_terminal stage) terminal
    rw [Best.Error.AtLeastAsGoodAs, currentErrorZero, Gaussian.Norm.Basic.normSq_zero]
    exact Gaussian.Norm.Basic.normSq_nonneg _
  · exact (atLeastAsGoodAs_of_generated_nonterminal stage) generated terminal
      competitor competitorDenominatorNonzero denominatorSmaller

/-- Every generated stage satisfies the unconditional weak lower-height
best-approximation predicate. -/
theorem isWeakLowerBest_of_generated
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (generated : Hurwitz.Geometry.Generated source stage) :
    Best.Basic.IsWeakLowerBest source.value stage.current := by
  refine ⟨Lakein.current_denominator_ne_zero_of_generated generated, ?_⟩
  intro competitor competitorNonzero denominatorSmaller
  change Best.Error.AtLeastAsGoodAs source.value stage.current competitor
  exact (atLeastAsGoodAs_of_generated stage) generated competitor
    competitorNonzero denominatorSmaller

/-- The terminal Hurwitz pair is not merely weakly optimal: its zero error
and adjacent unit determinant make it a genuine best approximation.  Any
smaller exact competitor would force its denominator to be a nonzero
Gaussian-integer multiple of the terminal denominator. -/
theorem isBest_of_generated_of_terminal
    {source : GaussianInt.Fraction} (stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source)
    (generated : Hurwitz.Geometry.Generated source stage)
    (terminal : GaussianInt.Division.Nearest.remainder stage.quotient = 0) :
    Best.Basic.IsBest source.value stage.current := by
  have currentNonzero := Lakein.current_denominator_ne_zero_of_generated generated
  have currentErrorZero := (current_error_eq_zero_of_terminal stage) terminal
  refine ⟨currentNonzero, ?_, ?_⟩
  · intro competitor competitorNonzero denominatorSmaller
    rw [Best.Error.errorQuadrance, currentErrorZero, Gaussian.Norm.Basic.normSq_zero]
    apply Gaussian.Norm.Basic.normSq_pos
    intro competitorErrorZero
    have determinantGaussianZero :
        GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current competitor) = 0 := by
      rw [Data.ComplexContinuedFraction.Hurwitz.Trace.determinant_eq_denominator_mul_error_sub,
        competitorErrorZero, currentErrorZero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re,
          Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re,
          Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re,
          Gaussian.Basic.zero_im] <;>
        ring1
    have determinantZero : GaussianInt.Pair.Basis.determinant stage.current competitor = 0 :=
      GaussianInt.toGaussian_eq_zero.mp determinantGaussianZero
    have denominatorDecomposition := GaussianInt.Pair.Basis.competitor_denominator_decomposition
      (competitor := competitor) stage.unitDeterminant
    simp only [GaussianInt.Pair.Basis.previousCoefficient, determinantZero,
      GaussianInt.mul_zero,
      GaussianInt.zero_mul,
      GaussianInt.add_zero] at denominatorDecomposition
    have coefficientNonzero :
        GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor ≠ 0 := by
      intro coefficientZero
      rw [coefficientZero,
        GaussianInt.zero_mul] at denominatorDecomposition
      exact competitorNonzero denominatorDecomposition.symm
    have coefficientPositive := GaussianInt.normNat_pos coefficientNonzero
    have currentNoLarger :
        GaussianInt.normNat stage.current.denominator ≤ GaussianInt.normNat competitor.denominator := by
      calc
        GaussianInt.normNat stage.current.denominator =
            1 * GaussianInt.normNat stage.current.denominator :=
          (Nat.one_mul _).symm
        _ ≤ GaussianInt.normNat
              (GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor) *
              GaussianInt.normNat stage.current.denominator :=
          Nat.mul_le_mul_right _ coefficientPositive
        _ = GaussianInt.normNat competitor.denominator := by
          rw [← GaussianInt.Embedding.normNat_mul, denominatorDecomposition]
    exact (not_lt_of_ge currentNoLarger denominatorSmaller).elim
  · intro competitor _ _
    rw [Best.Error.errorQuadrance, currentErrorZero, Gaussian.Norm.Basic.normSq_zero]
    exact Gaussian.Norm.Basic.normSq_nonneg _

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein.Stage

namespace Purelib.NumberTheory.Approximation.Hurwitz.Lakein

/-- Every displayed rational source has a best approximation, witnessed
constructively by the terminal pair of its executable Hurwitz trace. -/
theorem exists_bestApproximation (source :
  GaussianInt.Fraction) :
    ∃ pair : GaussianInt.Pair.Basic.ConvergentPair,
      Best.Basic.IsBest source.value pair := by
  obtain ⟨terminalStage, member, terminal⟩ :=
    Data.ComplexContinuedFraction.Hurwitz.Trace.exists_terminal_mem_stages source
  have generated := Hurwitz.Geometry.generated_of_mem_stages member
  exact ⟨terminalStage.current,
    Stage.isBest_of_generated_of_terminal
      terminalStage generated terminal⟩

/-- The sound-and-complete finite all-best selector always returns at least
one displayed pair. -/
theorem allBest_nonempty (source : GaussianInt.Fraction) :
    Best.Search.allBest source ≠ [] := by
  obtain ⟨pair, best⟩ := exists_bestApproximation source
  have member :=
    (Best.Search.mem_allBest_iff_isBest source pair).mpr best
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

/-- Every integer square is nonnegative. -/
private theorem int_square_nonnegative (x : Int) : 0 ≤ x * x :=
  Int.Order.mul_self_nonneg x

/-- Twice the first integer coordinate is at most the coordinate square sum whenever that sum is at least two. -/
private theorem twice_int_le_sum_squares {x y : Int}
    (twoLe : 2 ≤ x * x + y * y) : 2 * x ≤ x * x + y * y := by
  by_cases xAtLeastTwo : 2 ≤ x
  · have xNonnegative : 0 ≤ x := by omega
    have differenceNonnegative : 0 ≤ x - 2 := by omega
    have productNonnegative := Int.Order.mul_nonneg xNonnegative differenceNonnegative
    have productIdentity : x * (x - 2) = x * x - 2 * x := by ring1
    rw [productIdentity] at productNonnegative
    have ySquareNonnegative := Int.Order.mul_self_nonneg y
    omega
  · by_cases xNonpositive : x ≤ 0
    · have sumNonnegative := Int.Order.add_nonneg
        (Int.Order.mul_self_nonneg x) (Int.Order.mul_self_nonneg y)
      omega
    · have xOne : x = 1 := by omega
      subst x
      exact twoLe

/-- The negative coordinate square sum bounds twice the first integer coordinate from below when the sum is at least
two. -/
private theorem neg_sum_squares_le_twice_int {x y : Int}
    (twoLe : 2 ≤ x * x + y * y) :
    -(x * x + y * y) ≤ 2 * x := by
  have reflectedNorm : (-x) * (-x) + y * y = x * x + y * y := by ring1
  have reflectedTwoLe : 2 ≤ (-x) * (-x) + y * y := by
    rw [reflectedNorm]
    exact twoLe
  have upper := twice_int_le_sum_squares reflectedTwoLe
  rw [reflectedNorm] at upper
  have negated := Int.Order.neg_le_neg upper
  calc
    -(x * x + y * y) ≤ -(2 * -x) := negated
    _ = 2 * x := by ring1

/-- Multiplication by one half cancels twice a rational value. -/
private theorem half_mul_two_mul (value : Fraction.Rational) :
    (1 / 2 : Fraction.Rational) * (2 * value) = value := by
  calc
    (1 / 2 : Fraction.Rational) * (2 * value) =
        ((1 / 2 : Fraction.Rational) * 2) * value :=
      (_root_.mul_assoc _ _ _).symm
    _ = 1 * value := by rw [show (1 / 2 : Fraction.Rational) * 2 = 1 by decide]
    _ = value := one_mul _

/-- Bounds on twice a rational value give the corresponding half-scaled bounds on that value. -/
private theorem half_scaled_bounds {value bound :
  Fraction.Rational}
    (lower : -bound ≤ 2 * value) (upper : 2 * value ≤ bound) :
    -(1 / 2 : Fraction.Rational) * bound ≤ value ∧
      value ≤ (1 / 2 : Fraction.Rational) * bound := by
  have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 := by decide
  have scaledLower :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      lower halfNonnegative
  have scaledUpper :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      upper halfNonnegative
  constructor
  · calc
      -(1 / 2 : Fraction.Rational) * bound =
          (1 / 2 : Fraction.Rational) * (-bound) := by ring1
      _ ≤ (1 / 2 : Fraction.Rational) * (2 * value) := scaledLower
      _ = value := half_mul_two_mul value
  · calc
      value = (1 / 2 : Fraction.Rational) * (2 * value) :=
        (half_mul_two_mul value).symm
      _ ≤ (1 / 2 : Fraction.Rational) * bound := scaledUpper

/-- Dividing half-scaled bounds by their positive scale places the quotient in the closed half interval. -/
private theorem div_half_bounds {value bound :
  Fraction.Rational}
    (boundPositive : 0 < bound)
    (scaledBounds :
      -(1 / 2 : Fraction.Rational) * bound ≤ value ∧
        value ≤ (1 / 2 : Fraction.Rational) * bound) :
    -(1 / 2 : Fraction.Rational) ≤ value / bound ∧
      value / bound ≤ (1 / 2 : Fraction.Rational) := by
  exact
    ⟨(Fraction.Order.Field.le_div_iff_pos boundPositive).2
        scaledBounds.1,
      (Fraction.Order.Field.div_le_iff_pos boundPositive).2
        scaledBounds.2⟩

/-- Every reciprocal of a Gaussian integer of quadrance at least two lies
coordinatewise in the half-square. -/
theorem inverse_integer_coordinate_bounds {value : GaussianInt}
    (twoLe : 2 ≤ GaussianInt.normNat value) :
    -(1 / 2 : Fraction.Rational) ≤ (GaussianInt.toGaussian value)⁻¹.re ∧
      (GaussianInt.toGaussian value)⁻¹.re ≤ (1 / 2 : Fraction.Rational) ∧
      -(1 / 2 : Fraction.Rational) ≤ (GaussianInt.toGaussian value)⁻¹.im ∧
      (GaussianInt.toGaussian value)⁻¹.im ≤ (1 / 2 : Fraction.Rational) := open Purelib.Algebra in by
  have castNeg (value : Int) : ((-value : Int) : Fraction.Rational) = -(value : Fraction.Rational) :=
    Ring.IntCast.neg value
  have normIntTwoLe : (2 : Int) ≤ GaussianInt.normInt value := by
    rw [GaussianInt.Norm.Basic.normInt_eq_natCast_normNat]
    exact Int.Order.natCast_le_iff.mpr twoLe
  have realUpperInt : 2 * value.re ≤ GaussianInt.normInt value := by
    exact twice_int_le_sum_squares normIntTwoLe
  have realLowerInt : -GaussianInt.normInt value ≤ 2 * value.re := by
    exact neg_sum_squares_le_twice_int normIntTwoLe
  have imaginaryUpperInt : 2 * value.im ≤ GaussianInt.normInt value := by
    change 2 * value.im ≤
      value.re * value.re + value.im * value.im
    calc
      2 * value.im ≤ value.im * value.im + value.re * value.re :=
        twice_int_le_sum_squares (x := value.im) (y := value.re) (by
          rw [_root_.add_comm]
          exact normIntTwoLe)
      _ = value.re * value.re + value.im * value.im := by ring1
  have imaginaryLowerInt : -GaussianInt.normInt value ≤ 2 * value.im := by
    change -(value.re * value.re + value.im * value.im) ≤ 2 * value.im
    calc
      -(value.re * value.re + value.im * value.im) =
          -(value.im * value.im + value.re * value.re) := by ring1
      _ ≤ 2 * value.im :=
        neg_sum_squares_le_twice_int (x := value.im) (y := value.re) (by
          rw [_root_.add_comm]
          exact normIntTwoLe)
  have normPositiveNat : 0 < GaussianInt.normNat value := lt_of_lt_of_le (by decide) twoLe
  have normPositive : (0 : Fraction.Rational) < (GaussianInt.normNat value : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct normPositiveNat
  have normIdentity :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) = (GaussianInt.normNat value :
        Fraction.Rational) :=
    GaussianInt.normSq_toGaussian value
  have castRealUpper :
      (2 : Fraction.Rational) * (value.re : Fraction.Rational) ≤
        (GaussianInt.normNat value : Fraction.Rational) := by
    have cast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        realUpperInt
    simpa only [Ring.IntCast.intCast_mul, Int.cast_ofNat,
      GaussianInt.Norm.Basic.normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castRealLower :
      -(GaussianInt.normNat value : Fraction.Rational) ≤
        (2 : Fraction.Rational) * (value.re : Fraction.Rational) := by
    have cast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        realLowerInt
    simpa only [castNeg, Ring.IntCast.intCast_mul, Int.cast_ofNat,
      GaussianInt.Norm.Basic.normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castImaginaryUpper :
      (2 : Fraction.Rational) * (value.im : Fraction.Rational) ≤
        (GaussianInt.normNat value : Fraction.Rational) := by
    have cast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        imaginaryUpperInt
    simpa only [Ring.IntCast.intCast_mul, Int.cast_ofNat,
      GaussianInt.Norm.Basic.normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have castImaginaryLower :
      -(GaussianInt.normNat value : Fraction.Rational) ≤
        (2 : Fraction.Rational) * (value.im : Fraction.Rational) := by
    have cast :=
      (Fraction.Cast.Order.intCast_le_intCast_iff_direct _ _).2
        imaginaryLowerInt
    simpa only [castNeg, Ring.IntCast.intCast_mul, Int.cast_ofNat,
      GaussianInt.Norm.Basic.normInt_eq_natCast_normNat, Int.cast_natCast] using cast
  have realScaledBounds := half_scaled_bounds castRealLower castRealUpper
  have imaginaryNegLower :
      -(GaussianInt.normNat value : Fraction.Rational) ≤
        2 * (-(value.im : Fraction.Rational)) := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
      castImaginaryUpper
    calc
      -(GaussianInt.normNat value : Fraction.Rational) ≤
          -((2 : Fraction.Rational) * (value.im : Fraction.Rational)) := reversed
      _ = 2 * (-(value.im : Fraction.Rational)) := by ring1
  have imaginaryNegUpper :
      2 * (-(value.im : Fraction.Rational)) ≤
        (GaussianInt.normNat value : Fraction.Rational) := by
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
      castImaginaryLower
    calc
      2 * (-(value.im : Fraction.Rational)) =
          -((2 : Fraction.Rational) * (value.im : Fraction.Rational)) := by ring1
      _ ≤ -(-(GaussianInt.normNat value : Fraction.Rational)) := reversed
      _ = (GaussianInt.normNat value : Fraction.Rational) := neg_neg _
  have imaginaryScaledBounds :=
    half_scaled_bounds imaginaryNegLower imaginaryNegUpper
  have realBounds := div_half_bounds normPositive realScaledBounds
  have imaginaryBounds := div_half_bounds normPositive imaginaryScaledBounds
  rw [Gaussian.Field.inv_eq]
  change
    -(1 / 2 : Fraction.Rational) ≤
        Rat.Fraction.Cast.fromInt value.re / Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) ∧
      Rat.Fraction.Cast.fromInt value.re / Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) ≤ 1 / 2 ∧
      -(1 / 2 : Fraction.Rational) ≤
        -Rat.Fraction.Cast.fromInt value.im / Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) ∧
      -Rat.Fraction.Cast.fromInt value.im / Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian value) ≤ 1 / 2
  rw [normIdentity]
  simpa only [← Rat.Fraction.Cast.intCast_eq_fromInt] using
    And.intro realBounds.1 (And.intro realBounds.2 (And.intro
      imaginaryBounds.1 imaginaryBounds.2))

/-- The first noninitial denominator ratio is already in the smaller
half-square. -/
theorem firstAdvance_denominatorRatioInLakeinSquare (source :
  GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder source ≠ 0) :
    DenominatorRatioInLakeinSquare
      (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
      (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal) := by
  unfold DenominatorRatioInLakeinSquare
  have recurrence := advanceStage_denominatorRatio
    (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) Hurwitz.Geometry.Generated.first nonterminal
  have digitTwoLe := Hurwitz.Geometry.two_le_next_digit_normNat source nonterminal
  have inverseBounds := inverse_integer_coordinate_bounds digitTwoLe
  change
    -(3 / 4 : Fraction.Rational) ≤
        (Stage.denominatorRatio
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
            (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal)).re ∧
      (Stage.denominatorRatio
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
            (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal)).re ≤ 3 / 4 ∧
      -(3 / 4 : Fraction.Rational) ≤
        (Stage.denominatorRatio
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
            (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal)).im ∧
      (Stage.denominatorRatio
          (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
            (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal)).im ≤ 3 / 4
  rw [recurrence]
  rw [firstStage_denominatorRatio,
    Gaussian.Basic.add_zero]
  exact
    ⟨(show -(3 / 4 : Fraction.Rational) ≤ -(1 / 2) by decide).trans
        inverseBounds.1,
      inverseBounds.2.1.trans (show (1 / 2 : Fraction.Rational) ≤ 3 / 4 by decide),
      (show -(3 / 4 : Fraction.Rational) ≤ -(1 / 2) by decide).trans
        inverseBounds.2.2.1,
      inverseBounds.2.2.2.trans
        (show (1 / 2 : Fraction.Rational) ≤ 3 / 4 by decide)⟩

/-- The Lakein square is exactly strong enough to provide the outstanding
quadrance-five denominator certificate. -/
theorem normFiveDenominatorSafe_of_lakeinSquare
    {source : GaussianInt.Fraction} {stage : Data.ComplexContinuedFraction.Hurwitz.Trace.Stage source}
    (generated : Hurwitz.Geometry.Generated source stage)
    (inside : DenominatorRatioInLakeinSquare stage) :
    Hurwitz.Geometry.NormFiveDenominatorSafe stage := by
  intro s t sNorm tNorm
  have currentNonzero := current_denominator_ne_zero_of_generated generated
  let currentValue := GaussianInt.toGaussian stage.current.denominator
  let factor := GaussianInt.toGaussian s + GaussianInt.toGaussian t * (Stage.denominatorRatio stage)
  have factorExterior : 1 ≤ Data.Gaussian.Norm.Basic.normSq factor := by
    dsimp only [factor]
    exact Hurwitz.Geometry.one_le_normSq_normFive_add_diagonal_mul_of_coordinate_bounds
      (Stage.denominatorRatio stage) s t sNorm tNorm inside.1 inside.2.1
      inside.2.2.1 inside.2.2.2
  have currentNormNonnegative : 0 ≤ Data.Gaussian.Norm.Basic.normSq currentValue :=
    Gaussian.Norm.Basic.normSq_nonneg _
  have scaledExterior :
      1 * Data.Gaussian.Norm.Basic.normSq currentValue ≤ Data.Gaussian.Norm.Basic.normSq factor *
        Data.Gaussian.Norm.Basic.normSq currentValue :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      factorExterior currentNormNonnegative
  have factorIdentity :
      factor * currentValue =
        GaussianInt.toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator) := by
    dsimp only [factor, currentValue]
    rw [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul, GaussianInt.toGaussian_mul,
      ← denominatorRatio_mul_current stage currentNonzero]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im,
        Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  apply (Fraction.Cast.Order.natCast_le_iff_direct).1
  calc
    (GaussianInt.normNat stage.current.denominator : Fraction.Rational) =
        Data.Gaussian.Norm.Basic.normSq currentValue := (GaussianInt.normSq_toGaussian _).symm
    _ = 1 * Data.Gaussian.Norm.Basic.normSq currentValue := by ring1
    _ ≤ Data.Gaussian.Norm.Basic.normSq factor * Data.Gaussian.Norm.Basic.normSq currentValue := scaledExterior
    _ = Data.Gaussian.Norm.Basic.normSq (factor * currentValue) := by rw [Gaussian.Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq
        (GaussianInt.toGaussian
          (s * stage.current.denominator +
            t * stage.previous.denominator)) := by rw [factorIdentity]
    _ = (GaussianInt.normNat
          (s * stage.current.denominator +
            t * stage.previous.denominator) : Fraction.Rational) :=
      GaussianInt.normSq_toGaussian _

/-- The exceptional denominator comparison is automatic at the first
noninitial convergent; no succession argument is needed until the following
stage. -/
theorem firstAdvance_normFiveDenominatorSafe (source :
  GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder source ≠ 0) :
    Hurwitz.Geometry.NormFiveDenominatorSafe
      (Data.ComplexContinuedFraction.Hurwitz.Trace.advanceStage
        (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) nonterminal) := by
  exact normFiveDenominatorSafe_of_lakeinSquare
    (Hurwitz.Geometry.Generated.advance Hurwitz.Geometry.Generated.first nonterminal)
    (firstAdvance_denominatorRatioInLakeinSquare source nonterminal)

/-- The initial denominator ratio zero lies in the Lakein square. -/
theorem firstStage_denominatorRatioInLakeinSquare (source :
  GaussianInt.Fraction) :
    DenominatorRatioInLakeinSquare
      (Data.ComplexContinuedFraction.Hurwitz.Trace.firstStage source) := by
  unfold DenominatorRatioInLakeinSquare
  rw [firstStage_denominatorRatio]
  change -(3 / 4 : Fraction.Rational) ≤ 0 ∧ 0 ≤ 3 / 4 ∧
    -(3 / 4 : Fraction.Rational) ≤ 0 ∧ 0 ≤ 3 / 4
  decide

end Purelib.NumberTheory.Approximation.Hurwitz.Lakein

end

end
