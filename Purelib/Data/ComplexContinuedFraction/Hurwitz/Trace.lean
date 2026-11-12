module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Best.Error

import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.Rat.Fraction.Compatibility

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

open Purelib.Data.GaussianInt.Division
open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Finite traces of Hurwitz complete quotients

The terminating rational encoder is useful for execution, while the Lakein
comparison also needs the complete quotient and the two adjacent convergents
at every prefix.  This module records exactly that finite state.  Each stage
carries a division-free reconstruction identity for the original displayed
Gaussian rational.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Trace

open Purelib.Data.Gaussian in
/-- The original canonical Gaussian carrier used by the retained Hurwitz stages. -/
abbrev Gaussian := Basic.Canonical
/-- The original nominal Gaussian-integer carrier used by the retained convergent pairs. -/
abbrev GaussianInt := Data.GaussianInt
/-- The original displayed Gaussian-integer fraction carrier, including its nonzero denominator witness. -/
abbrev Fraction := GaussianInt.Fraction
/-- The original integral numerator-denominator pair carrier for Hurwitz convergents. -/
abbrev ConvergentPair := GaussianInt.Pair.Basic.ConvergentPair

open Purelib.Data.GaussianInt (normNat)

open Purelib.Data.ComplexContinuedFraction in
/-- Compute the next pair as the supplied digit times the current pair plus the previous pair. -/
def advancePair (nextDigit : GaussianInt)
    (current previous : ConvergentPair) : ConvergentPair :=
  ⟨nextDigit * current.numerator + previous.numerator,
    nextDigit * current.denominator + previous.denominator⟩

section
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction
/-- Advancing the pair recurrence negates the determinant of the retained adjacent pair. -/
theorem determinant_advancePair (nextDigit : GaussianInt)
    (current previous : ConvergentPair) :
    GaussianInt.Pair.Basis.determinant (advancePair nextDigit current previous) current =
      -GaussianInt.Pair.Basis.determinant current previous := by
  apply GaussianInt.ext <;>
    simp only [GaussianInt.Pair.Basis.determinant, advancePair,
      GaussianInt.add_re,
      GaussianInt.add_im,
      GaussianInt.sub_re,
      GaussianInt.sub_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.mul_re,
      GaussianInt.mul_im] <;>
    ring1

/-- Advancing the pair recurrence preserves determinant equal to one or minus one. -/
theorem unitDeterminant_advancePair {current previous : ConvergentPair}
    (unitDeterminant : GaussianInt.Pair.Basis.HasUnitDeterminant current previous)
    (nextDigit : GaussianInt) :
    GaussianInt.Pair.Basis.HasUnitDeterminant (advancePair nextDigit current previous) current := by
  rw [GaussianInt.Pair.Basis.HasUnitDeterminant, determinant_advancePair]
  rcases unitDeterminant with positive | negative
  · right
    rw [positive]
  · left
    rw [negative]
    exact neg_neg 1

end

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
set_option genInjectivity false in
/-- Retain a quotient and two adjacent convergent pairs representing the original source fraction.

The exact current and previous pairs have determinant one or minus one. Their coordinate combination with the retained
quotient residual satisfies the original source reconstruction equation. -/
structure Stage (source : Fraction) where
  /-- The retained displayed quotient fraction at this stage. -/ quotient : Fraction
  /-- The preceding retained integral convergent pair. -/ previous : ConvergentPair
  /-- The current retained integral convergent pair. -/ current : ConvergentPair
  /-- Evidence that the exact adjacent pair determinant is one or minus one. -/ unitDeterminant :
    GaussianInt.Pair.Basis.HasUnitDeterminant current previous
  /-- The original source reconstruction equation using these pairs and the retained quotient residual. -/ represents :
    source.value *
        (GaussianInt.toGaussian current.denominator +
          Nearest.residual quotient * GaussianInt.toGaussian previous.denominator) =
      GaussianInt.toGaussian current.numerator +
        Nearest.residual quotient * GaussianInt.toGaussian previous.numerator

constructive_injectivity Stage

section
open Purelib.Data
open Purelib.Data.ComplexContinuedFraction
section
open Purelib.Data.Gaussian
open Purelib.NumberTheory.Approximation
/-- Current error plus the retained quotient residual times previous error is zero. -/
theorem Stage.error_add_residual_mul_previous_eq_zero
    {source : Fraction} (stage : Stage source) :
    Best.Error.error source.value stage.current +
        Nearest.residual stage.quotient * Best.Error.error source.value stage.previous = 0 := by
  calc
    Best.Error.error source.value stage.current +
          Nearest.residual stage.quotient * Best.Error.error source.value stage.previous =
        source.value *
            (GaussianInt.toGaussian stage.current.denominator +
              Nearest.residual stage.quotient *
                GaussianInt.toGaussian stage.previous.denominator) -
          (GaussianInt.toGaussian stage.current.numerator +
            Nearest.residual stage.quotient *
              GaussianInt.toGaussian stage.previous.numerator) := by
      apply Basic.ext <;>
        simp only [Best.Error.error,
          Basic.add_re,
          Basic.add_im,
          Basic.sub_re,
          Basic.sub_im,
          Basic.mul_re,
          Basic.mul_im] <;>
        ring1
    _ = 0 := by
      rw [stage.represents]
      exact Basic.sub_self _

/-- At a nonterminal stage, previous error is minus the next quotient value times current error. -/
theorem Stage.previous_error_eq_neg_next_mul_current
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    Best.Error.error source.value stage.previous =
      -(Step.next stage.quotient nonterminal).value *
        Best.Error.error source.value stage.current := by
  have residualNonzero : Nearest.residual stage.quotient ≠ 0 :=
    Nearest.residual_ne_zero nonterminal
  have reciprocal :
      (Step.next stage.quotient nonterminal).value *
          Nearest.residual stage.quotient = 1 := by
    rw [Step.next_value, Field.inv_eq,
      Field.inv_mul _ residualNonzero]
  have residualMulPrevious :
      Nearest.residual stage.quotient * Best.Error.error source.value stage.previous =
        -Best.Error.error source.value stage.current := by
    calc
      Nearest.residual stage.quotient * Best.Error.error source.value stage.previous =
          (Best.Error.error source.value stage.current +
            Nearest.residual stage.quotient * Best.Error.error source.value stage.previous) -
              Best.Error.error source.value stage.current := by
        apply Basic.ext <;>
          simp only [Basic.add_re,
            Basic.add_im,
            Basic.sub_re,
            Basic.sub_im] <;>
          ring1
      _ = 0 - Best.Error.error source.value stage.current := by
        rw [stage.error_add_residual_mul_previous_eq_zero]
      _ = -Best.Error.error source.value stage.current := by
        apply Basic.ext <;>
          simp only [Basic.sub_re,
            Basic.sub_im,
            Basic.neg_re,
            Basic.neg_im,
            Basic.zero_re,
            Basic.zero_im] <;>
          ring1
  calc
    Best.Error.error source.value stage.previous =
        ((Step.next stage.quotient nonterminal).value *
          Nearest.residual stage.quotient) * Best.Error.error source.value stage.previous := by
      rw [reciprocal, Basic.one_mul]
    _ = (Step.next stage.quotient nonterminal).value *
          (Nearest.residual stage.quotient *
            Best.Error.error source.value stage.previous) := by
      rw [Basic.mul_assoc]
    _ = (Step.next stage.quotient nonterminal).value *
          (-Best.Error.error source.value stage.current) := by
      rw [residualMulPrevious]
    _ = -(Step.next stage.quotient nonterminal).value *
          Best.Error.error source.value stage.current := by
      apply Basic.ext <;>
        simp only [Basic.neg_re,
          Basic.neg_im,
          Basic.mul_re,
          Basic.mul_im] <;>
        ring1

/-- A competitor error factors through its exact adjacent-pair coefficients and the retained next quotient.

The stage is nonterminal and its unit determinant gives the original integral basis coefficients. The factor multiplies
the same stage current error without replacing either convergent pair. -/
theorem Stage.competitor_error_eq_factor_mul_current
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair) :
    Best.Error.error source.value competitor =
      (GaussianInt.toGaussian
          (GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor) -
        GaussianInt.toGaussian
          (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) *
            (Step.next stage.quotient nonterminal).value) *
        Best.Error.error source.value stage.current := by
  rw [Best.Error.competitor_error_decomposition source.value stage.unitDeterminant,
    stage.previous_error_eq_neg_next_mul_current nonterminal]
  apply Basic.ext <;>
    simp only [Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im,
      Basic.neg_re,
      Basic.neg_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    ring1

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.NumberTheory.Approximation in
/-- A competitor factor with squared norm at least one proves the current retained convergent no worse than that
competitor. -/
theorem Stage.atLeastAsGoodAs_of_one_le_factor_normSq
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair)
    (factorExterior :
      1 ≤ Norm.Basic.normSq
        (GaussianInt.toGaussian
            (GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor) -
          GaussianInt.toGaussian
              (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) *
            (Step.next stage.quotient nonterminal).value)) :
    Best.Error.AtLeastAsGoodAs source.value stage.current competitor := by
  rw [Best.Error.AtLeastAsGoodAs,
    stage.competitor_error_eq_factor_mul_current nonterminal competitor,
    Norm.Basic.normSq_mul]
  have currentErrorNonnegative := Norm.Basic.normSq_nonneg (Best.Error.error source.value stage.current)
  have scaled :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      factorExterior currentErrorNonnegative
  calc
    Norm.Basic.normSq (Best.Error.error source.value stage.current) =
        1 * Norm.Basic.normSq (Best.Error.error source.value stage.current) := by ring1
    _ ≤ Norm.Basic.normSq
          (GaussianInt.toGaussian
              (GaussianInt.Pair.Basis.currentCoefficient stage.current stage.previous competitor) -
            GaussianInt.toGaussian
                (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) *
              (Step.next stage.quotient nonterminal).value) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) := scaled

/-- Combine the next quotient value with the current denominator and add the previous denominator. -/
def Stage.completeDenominator {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) : Gaussian :=
  (Step.next stage.quotient nonterminal).value *
      GaussianInt.toGaussian stage.current.denominator +
    GaussianInt.toGaussian stage.previous.denominator

open Purelib.Data.Gaussian in
/-- The source value times the retained complete denominator equals the corresponding next-quotient numerator
combination. -/
theorem Stage.scaled_represents {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    source.value * stage.completeDenominator nonterminal =
      (Step.next stage.quotient nonterminal).value *
          GaussianInt.toGaussian stage.current.numerator +
        GaussianInt.toGaussian stage.previous.numerator := by
  have residualNonzero : Nearest.residual stage.quotient ≠ 0 :=
    Nearest.residual_ne_zero nonterminal
  have reciprocal :
      (Step.next stage.quotient nonterminal).value *
          Nearest.residual stage.quotient = 1 := by
    rw [Step.next_value, Field.inv_eq,
      Field.inv_mul _ residualNonzero]
  calc
    source.value * stage.completeDenominator nonterminal =
        (Step.next stage.quotient nonterminal).value *
          (source.value *
            (GaussianInt.toGaussian stage.current.denominator +
              Nearest.residual stage.quotient *
                GaussianInt.toGaussian stage.previous.denominator)) := by
      unfold completeDenominator
      calc
        source.value *
              ((Step.next stage.quotient nonterminal).value *
                  GaussianInt.toGaussian stage.current.denominator +
                GaussianInt.toGaussian stage.previous.denominator) =
            source.value *
              ((Step.next stage.quotient nonterminal).value *
                  GaussianInt.toGaussian stage.current.denominator +
                ((Step.next stage.quotient nonterminal).value *
                    Nearest.residual stage.quotient) *
                  GaussianInt.toGaussian stage.previous.denominator) := by
          rw [reciprocal, Basic.one_mul]
        _ = (Step.next stage.quotient nonterminal).value *
              (source.value *
                (GaussianInt.toGaussian stage.current.denominator +
                  Nearest.residual stage.quotient *
                    GaussianInt.toGaussian stage.previous.denominator)) := by
          apply Basic.ext <;>
            simp only [Basic.add_re,
              Basic.add_im,
              Basic.mul_re,
              Basic.mul_im] <;>
            ring1
    _ = (Step.next stage.quotient nonterminal).value *
          (GaussianInt.toGaussian stage.current.numerator +
            Nearest.residual stage.quotient *
              GaussianInt.toGaussian stage.previous.numerator) := by
      rw [stage.represents]
    _ = (Step.next stage.quotient nonterminal).value *
          GaussianInt.toGaussian stage.current.numerator +
        GaussianInt.toGaussian stage.previous.numerator := by
      calc
        (Step.next stage.quotient nonterminal).value *
              (GaussianInt.toGaussian stage.current.numerator +
                Nearest.residual stage.quotient *
                  GaussianInt.toGaussian stage.previous.numerator) =
            (Step.next stage.quotient nonterminal).value *
                GaussianInt.toGaussian stage.current.numerator +
              ((Step.next stage.quotient nonterminal).value *
                  Nearest.residual stage.quotient) *
                GaussianInt.toGaussian stage.previous.numerator := by
          apply Basic.ext <;>
            simp only [Basic.add_re,
              Basic.add_im,
              Basic.mul_re,
              Basic.mul_im] <;>
            ring1
        _ = (Step.next stage.quotient nonterminal).value *
              GaussianInt.toGaussian stage.current.numerator +
            GaussianInt.toGaussian stage.previous.numerator := by
          rw [reciprocal, Basic.one_mul]

section
open Purelib.Data.Gaussian
open Purelib.NumberTheory.Approximation
/-- Current error times the complete denominator is minus the embedded adjacent-pair determinant. -/
theorem Stage.current_error_mul_completeDenominator
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    Best.Error.error source.value stage.current *
        stage.completeDenominator nonterminal =
      -GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current stage.previous) := by
  have reconstruction := stage.scaled_represents nonterminal
  calc
    Best.Error.error source.value stage.current *
          stage.completeDenominator nonterminal =
        GaussianInt.toGaussian stage.current.denominator *
            (source.value * stage.completeDenominator nonterminal) -
          GaussianInt.toGaussian stage.current.numerator *
            stage.completeDenominator nonterminal := by
      apply Basic.ext <;>
        simp only [Best.Error.error,
          Basic.sub_re,
          Basic.sub_im,
          Basic.mul_re,
          Basic.mul_im] <;>
        ring1
    _ = GaussianInt.toGaussian stage.current.denominator *
          ((Step.next stage.quotient nonterminal).value *
              GaussianInt.toGaussian stage.current.numerator +
            GaussianInt.toGaussian stage.previous.numerator) -
        GaussianInt.toGaussian stage.current.numerator *
          stage.completeDenominator nonterminal := by
      rw [reconstruction]
    _ = -GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current stage.previous) := by
      unfold completeDenominator GaussianInt.Pair.Basis.determinant
      simp only [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul]
      apply Basic.ext <;>
        simp only [Basic.add_re,
          Basic.add_im,
          Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im,
          Basic.mul_re,
          Basic.mul_im] <;>
        ring1

/-- At a nonterminal stage, current-error norm times complete-denominator norm is one. -/
theorem Stage.current_error_norm_product_eq_one
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    Norm.Basic.normSq (Best.Error.error source.value stage.current) *
        Norm.Basic.normSq (stage.completeDenominator nonterminal) = 1 := by
  rw [← Norm.Basic.normSq_mul, stage.current_error_mul_completeDenominator nonterminal,
    Norm.Basic.normSq_neg, GaussianInt.normSq_toGaussian]
  rcases stage.unitDeterminant with positive | negative
  · rw [positive]
    rfl
  · rw [negative]
    rfl

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.NumberTheory.Approximation
/-- The current error has positive squared norm at every nonterminal retained stage. -/
theorem Stage.current_error_normSq_pos
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    0 < Norm.Basic.normSq (Best.Error.error source.value stage.current) := by
  have nonnegative := Norm.Basic.normSq_nonneg (Best.Error.error source.value stage.current)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have product := stage.current_error_norm_product_eq_one nonterminal
  rw [← zero] at product
  have impossible : (0 : Fraction.Rational) = 1 := by
    calc
      0 = 0 * Norm.Basic.normSq (stage.completeDenominator nonterminal) := by ring1
      _ = 1 := product
  exact (show (0 : Fraction.Rational) ≠ 1 by decide) impossible

/-- The complete denominator has positive squared norm at every nonterminal retained stage. -/
theorem Stage.completeDenominator_normSq_pos
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    0 < Norm.Basic.normSq (stage.completeDenominator nonterminal) := by
  have nonnegative := Norm.Basic.normSq_nonneg (stage.completeDenominator nonterminal)
  apply lt_of_le_of_ne nonnegative
  intro zero
  have product := stage.current_error_norm_product_eq_one nonterminal
  rw [← zero] at product
  have impossible : (0 : Fraction.Rational) = 1 := by
    calc
      0 = Norm.Basic.normSq (Best.Error.error source.value stage.current) * 0 := by ring1
      _ = 1 := product
  exact (show (0 : Fraction.Rational) ≠ 1 by decide) impossible

end

open Purelib.Data.Gaussian in
open Purelib.NumberTheory.Approximation in
/-- The embedded pair determinant is the difference of denominator-weighted approximation errors. -/
theorem determinant_eq_denominator_mul_error_sub
    (source : Gaussian) (current competitor : ConvergentPair) :
    GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant current competitor) =
      GaussianInt.toGaussian current.denominator * Best.Error.error source competitor -
        GaussianInt.toGaussian competitor.denominator * Best.Error.error source current := by
  unfold GaussianInt.Pair.Basis.determinant Best.Error.error
  simp only [GaussianInt.toGaussian_sub, GaussianInt.toGaussian_mul]
  apply Basic.ext <;>
    simp only [Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.NumberTheory.Approximation in
/-- Pair determinant norm is at most twice the sum of the two denominator-norm-weighted error norms. -/
theorem determinant_normSq_le
    (source : Gaussian) (current competitor : ConvergentPair) :
    Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant current competitor)) ≤
      2 *
        ((normNat current.denominator :
            Fraction.Rational) *
            Norm.Basic.normSq (Best.Error.error source competitor) +
          (normNat competitor.denominator :
            Fraction.Rational) *
            Norm.Basic.normSq (Best.Error.error source current)) := by
  rw [determinant_eq_denominator_mul_error_sub]
  calc
    Norm.Basic.normSq
          (GaussianInt.toGaussian current.denominator * Best.Error.error source competitor -
            GaussianInt.toGaussian competitor.denominator * Best.Error.error source current) ≤
        2 *
          (Norm.Basic.normSq (GaussianInt.toGaussian current.denominator * Best.Error.error source competitor)
            +
            Norm.Basic.normSq
              (GaussianInt.toGaussian competitor.denominator * Best.Error.error source current)) :=
      Norm.Bounds.normSq_sub_le_two _ _
    _ = 2 *
        ((normNat current.denominator :
            Fraction.Rational) *
            Norm.Basic.normSq (Best.Error.error source competitor) +
          (normNat competitor.denominator :
            Fraction.Rational) *
            Norm.Basic.normSq (Best.Error.error source current)) := by
      rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The previous basis coefficient norm equals the embedded determinant norm against the retained current pair. -/
theorem Stage.previousCoefficient_normSq
    {source : Fraction} (stage : Stage source)
    (competitor : ConvergentPair) :
    (normNat
        (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) :
          Fraction.Rational) =
      Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current competitor))
        := by
  rw [← GaussianInt.normSq_toGaussian]
  unfold GaussianInt.Pair.Basis.previousCoefficient
  rw [GaussianInt.toGaussian_mul, Norm.Basic.normSq_mul]
  have determinantNorm :
      Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current
        stage.previous)) = 1 := by
    rcases stage.unitDeterminant with positive | negative
    · rw [positive, GaussianInt.toGaussian_one, Norm.Basic.normSq_one]
    · rw [negative, GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one, Norm.Basic.normSq_neg,
        Norm.Basic.normSq_one]
  rw [determinantNorm]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.NumberTheory.Approximation in
/-- A sufficiently large previous basis coefficient excludes a better competitor with smaller nonzero denominator.

The coefficient norm times the retained complete-denominator norm must exceed four times the current denominator norm.
The original stage and competitor remain the inputs to the resulting error comparison. -/
theorem Stage.atLeastAsGoodAs_of_large_previousCoefficient
    {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0)
    (competitor : ConvergentPair)
    (competitorDenominatorNonzero : competitor.denominator ≠ 0)
    (denominatorSmaller :
      normNat competitor.denominator < normNat stage.current.denominator)
    (largeCoefficient :
      (4 : Fraction.Rational) *
          (normNat stage.current.denominator :
            Fraction.Rational) <
        (normNat
            (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) :
              Fraction.Rational) *
          Norm.Basic.normSq (stage.completeDenominator nonterminal)) :
    Best.Error.AtLeastAsGoodAs source.value stage.current competitor := by
  rw [Best.Error.AtLeastAsGoodAs]
  apply le_of_not_gt
  intro competitorBetter
  have competitorHeightPositive :
      (0 : Fraction.Rational) <
        (normNat competitor.denominator :
          Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct
      (GaussianInt.normNat_pos competitorDenominatorNonzero)
  have denominatorCastSmaller :
      (normNat competitor.denominator :
          Fraction.Rational) <
        (normNat stage.current.denominator :
          Fraction.Rational) :=
    (Fraction.Cast.Order.natCast_lt_iff_direct).2 denominatorSmaller
  have currentHeightPositive :
      (0 : Fraction.Rational) <
        (normNat stage.current.denominator :
          Fraction.Rational) :=
    competitorHeightPositive.trans denominatorCastSmaller
  have currentErrorPositive := stage.current_error_normSq_pos nonterminal
  have completeDenominatorPositive :=
    stage.completeDenominator_normSq_pos nonterminal
  have firstLeg :
      (normNat stage.current.denominator :
          Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value competitor) <
        (normNat stage.current.denominator :
          Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) :=
    Arithmetic.mul_lt_mul_of_pos_left_direct
      currentHeightPositive competitorBetter
  have secondLeg :
      (normNat competitor.denominator :
          Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) <
        (normNat stage.current.denominator :
          Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) :=
    Arithmetic.mul_lt_mul_of_pos_right_direct
      denominatorCastSmaller currentErrorPositive
  have sumStrict := Arithmetic.add_lt_add_direct
    firstLeg secondLeg
  have doubledStrict :
      2 *
          ((normNat stage.current.denominator :
              Fraction.Rational) *
              Norm.Basic.normSq (Best.Error.error source.value competitor) +
            (normNat competitor.denominator :
              Fraction.Rational) *
              Norm.Basic.normSq (Best.Error.error source.value stage.current)) <
        4 *
          (normNat stage.current.denominator :
            Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) := by
    have scaled :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
        (show (0 : Fraction.Rational) < 2 by decide)
        sumStrict
    calc
      2 *
            ((normNat stage.current.denominator :
                Fraction.Rational) *
                Norm.Basic.normSq (Best.Error.error source.value competitor) +
              (normNat competitor.denominator :
                Fraction.Rational) *
                Norm.Basic.normSq (Best.Error.error source.value stage.current)) <
          2 *
            ((normNat stage.current.denominator :
                Fraction.Rational) *
                Norm.Basic.normSq (Best.Error.error source.value stage.current) +
              (normNat stage.current.denominator :
                Fraction.Rational) *
                Norm.Basic.normSq (Best.Error.error source.value stage.current)) := scaled
      _ = 4 *
          (normNat stage.current.denominator :
            Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) := by ring1
  have determinantStrict :
      Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current competitor))
        <
        4 *
          (normNat stage.current.denominator :
            Fraction.Rational) *
          Norm.Basic.normSq (Best.Error.error source.value stage.current) :=
    (determinant_normSq_le source.value stage.current competitor).trans_lt
      doubledStrict
  have scaledDeterminantStrict :=
    Arithmetic.mul_lt_mul_of_pos_right_direct
      determinantStrict completeDenominatorPositive
  have coefficientProductStrict :
      (normNat
          (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) :
            Fraction.Rational) *
          Norm.Basic.normSq (stage.completeDenominator nonterminal) <
        4 *
          (normNat stage.current.denominator :
            Fraction.Rational) := by
    calc
      (normNat
            (GaussianInt.Pair.Basis.previousCoefficient stage.current stage.previous competitor) :
              Fraction.Rational) *
            Norm.Basic.normSq (stage.completeDenominator nonterminal) =
          Norm.Basic.normSq (GaussianInt.toGaussian (GaussianInt.Pair.Basis.determinant stage.current
            competitor)) *
            Norm.Basic.normSq (stage.completeDenominator nonterminal) := by
        rw [stage.previousCoefficient_normSq competitor]
      _ < (4 *
            (normNat stage.current.denominator :
              Fraction.Rational) *
            Norm.Basic.normSq (Best.Error.error source.value stage.current)) *
          Norm.Basic.normSq (stage.completeDenominator nonterminal) :=
        scaledDeterminantStrict
      _ = 4 *
          (normNat stage.current.denominator :
            Fraction.Rational) *
          (Norm.Basic.normSq (Best.Error.error source.value stage.current) *
            Norm.Basic.normSq (stage.completeDenominator nonterminal)) := by ring1
      _ = 4 *
          (normNat stage.current.denominator :
            Fraction.Rational) := by
        rw [stage.current_error_norm_product_eq_one nonterminal]
        ring1
  exact (not_lt_of_ge coefficientProductStrict.le largeCoefficient).elim

section
open Purelib.Data.Gaussian
/-- Construct the first Hurwitz stage from the original fraction and its selected nearest-integer digit.

Retain the source as quotient, the pair one over zero as previous, and digit over one as current. Their exact
determinant and residual decomposition certify the stage. -/
def firstStage (source : Fraction) : Stage source :=
  { quotient := source
    previous := ⟨1, 0⟩
    current := ⟨Nearest.digit source, 1⟩
    unitDeterminant := by
      right
      apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.Basis.determinant,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.neg_re,
          GaussianInt.neg_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.zero_re,
          GaussianInt.zero_im,
          GaussianInt.one_re,
          GaussianInt.one_im] <;>
        ring1
    represents := by
      simpa only [GaussianInt.toGaussian_one, GaussianInt.toGaussian_zero,
        Basic.mul_one,
        Basic.mul_zero,
        Basic.add_zero,
        Basic.zero_add]
        using Nearest.value_eq_digit_add_residual source }

/-- Advance a nonterminal retained stage using the exact next quotient and selected next digit.

Move the current pair to previous, compute the next pair by the same digit recurrence, and transport the original source
representation and unit-determinant evidence. The result retains the original source index. -/
def advanceStage {source : Fraction} (stage : Stage source)
    (nonterminal : Nearest.remainder stage.quotient ≠ 0) : Stage source := by
  let nextQuotient := Step.next stage.quotient nonterminal
  let nextDigit := Nearest.digit nextQuotient
  let nextResidual := Nearest.residual nextQuotient
  let nextCurrent := advancePair nextDigit stage.current stage.previous
  have oldResidualNonzero : Nearest.residual stage.quotient ≠ 0 :=
    Nearest.residual_ne_zero nonterminal
  have nextValue : nextQuotient.value =
      (Nearest.residual stage.quotient)⁻¹ :=
    Step.next_value stage.quotient nonterminal
  have reciprocal :
      nextQuotient.value * Nearest.residual stage.quotient = 1 := by
    rw [nextValue, Field.inv_eq,
      Field.inv_mul _ oldResidualNonzero]
  have nextDecomposition :
      nextQuotient.value = GaussianInt.toGaussian nextDigit + nextResidual :=
    Nearest.value_eq_digit_add_residual nextQuotient
  have scaledRepresentation := congrArg
    (fun value => nextQuotient.value * value) stage.represents
  refine
    { quotient := nextQuotient
      previous := stage.current
      current := nextCurrent
      unitDeterminant :=
        unitDeterminant_advancePair stage.unitDeterminant nextDigit
      represents := ?_ }
  change source.value *
      (GaussianInt.toGaussian nextCurrent.denominator +
        nextResidual * GaussianInt.toGaussian stage.current.denominator) =
    GaussianInt.toGaussian nextCurrent.numerator +
      nextResidual * GaussianInt.toGaussian stage.current.numerator
  dsimp only [nextCurrent, advancePair]
  simp only [GaussianInt.toGaussian_add, GaussianInt.toGaussian_mul]
  have denominatorRegroup :
      GaussianInt.toGaussian nextDigit * GaussianInt.toGaussian stage.current.denominator +
          GaussianInt.toGaussian stage.previous.denominator +
            nextResidual * GaussianInt.toGaussian stage.current.denominator =
        (GaussianInt.toGaussian nextDigit + nextResidual) *
            GaussianInt.toGaussian stage.current.denominator +
          GaussianInt.toGaussian stage.previous.denominator := by
    apply Basic.ext <;>
      simp only [Basic.add_re,
        Basic.add_im,
        Basic.mul_re,
        Basic.mul_im] <;>
      ring1
  have numeratorRegroup :
      GaussianInt.toGaussian nextDigit * GaussianInt.toGaussian stage.current.numerator +
          GaussianInt.toGaussian stage.previous.numerator +
            nextResidual * GaussianInt.toGaussian stage.current.numerator =
        (GaussianInt.toGaussian nextDigit + nextResidual) *
            GaussianInt.toGaussian stage.current.numerator +
          GaussianInt.toGaussian stage.previous.numerator := by
    apply Basic.ext <;>
      simp only [Basic.add_re,
        Basic.add_im,
        Basic.mul_re,
        Basic.mul_im] <;>
      ring1
  rw [denominatorRegroup, numeratorRegroup, ← nextDecomposition]
  calc
    source.value *
          (nextQuotient.value * GaussianInt.toGaussian stage.current.denominator +
            GaussianInt.toGaussian stage.previous.denominator) =
        nextQuotient.value *
          (source.value *
            (GaussianInt.toGaussian stage.current.denominator +
              Nearest.residual stage.quotient *
                GaussianInt.toGaussian stage.previous.denominator)) := by
      calc
        source.value *
              (nextQuotient.value * GaussianInt.toGaussian stage.current.denominator +
                GaussianInt.toGaussian stage.previous.denominator) =
            source.value *
              (nextQuotient.value * GaussianInt.toGaussian stage.current.denominator +
                (nextQuotient.value * Nearest.residual stage.quotient) *
                  GaussianInt.toGaussian stage.previous.denominator) := by
          rw [reciprocal, Basic.one_mul]
        _ = nextQuotient.value *
              (source.value *
                (GaussianInt.toGaussian stage.current.denominator +
                  Nearest.residual stage.quotient *
                    GaussianInt.toGaussian stage.previous.denominator)) := by
          apply Basic.ext <;>
            simp only [Basic.add_re,
              Basic.add_im,
              Basic.mul_re,
              Basic.mul_im] <;>
            ring1
    _ = nextQuotient.value *
          (GaussianInt.toGaussian stage.current.numerator +
            Nearest.residual stage.quotient *
              GaussianInt.toGaussian stage.previous.numerator) := scaledRepresentation
    _ = nextQuotient.value * GaussianInt.toGaussian stage.current.numerator +
          GaussianInt.toGaussian stage.previous.numerator := by
      calc
        nextQuotient.value *
              (GaussianInt.toGaussian stage.current.numerator +
                Nearest.residual stage.quotient *
                  GaussianInt.toGaussian stage.previous.numerator) =
            nextQuotient.value * GaussianInt.toGaussian stage.current.numerator +
              (nextQuotient.value * Nearest.residual stage.quotient) *
                GaussianInt.toGaussian stage.previous.numerator := by
          apply Basic.ext <;>
            simp only [Basic.add_re,
              Basic.add_im,
              Basic.mul_re,
              Basic.mul_im] <;>
            ring1
        _ = nextQuotient.value * GaussianInt.toGaussian stage.current.numerator +
              GaussianInt.toGaussian stage.previous.numerator := by
          rw [reciprocal, Basic.one_mul]

end

/-- The advanced stage stores the exact next Hurwitz quotient. -/
@[simp] theorem advanceStage_quotient {source : Fraction}
    (stage : Stage source) (nonterminal : Nearest.remainder stage.quotient ≠ 0) :
    (advanceStage stage nonterminal).quotient =
      Step.next stage.quotient nonterminal := by
  rfl

/-- Enumerate retained Hurwitz stages until a zero remainder or the supplied fuel limit.

Always include the current stage, including at zero fuel. A nonterminal successor retains the current stage before
recursing on its exact advance, so exhaustion alone asserts no termination property. -/
def stagesFromFuel {source : Fraction} : Nat → Stage source → List (Stage
  source)
  | 0, stage => [stage]
  | fuel + 1, stage =>
      if terminal : Nearest.remainder stage.quotient = 0 then
        [stage]
      else
        stage :: Trace.stagesFromFuel fuel (advanceStage
          stage terminal)

end

section
open Purelib.Data.ComplexContinuedFraction
/-- Enumerate stages with fuel one greater than the retained quotient denominator norm. -/
def stagesFrom {source : Fraction} (stage : Stage source) :
    List (Stage source) :=
  stagesFromFuel (Nat.succ (normNat stage.quotient.denominator)) stage

/-- Enumerate the finite retained stage sequence starting at the source fraction's first stage. -/
def stages (source : Fraction) : List (Stage source) :=
  stagesFrom (firstStage source)

end

open Purelib.Data
open Purelib.Data.ComplexContinuedFraction
/-- Fuel greater than the current denominator norm guarantees a zero-remainder stage in the retained stage list. -/
private theorem exists_terminal_mem_stagesFromFuel {source : Fraction}
    (fuel : Nat) (stage : Stage source)
    (enough : normNat stage.quotient.denominator < fuel) :
    ∃ terminalStage,
      terminalStage ∈ stagesFromFuel fuel stage ∧
        Nearest.remainder terminalStage.quotient = 0 := by
  induction fuel generalizing stage with
  | zero => exact (Nat.not_lt_zero _ enough).elim
  | succ fuel inductionHypothesis =>
      by_cases terminal : Nearest.remainder stage.quotient = 0
      · refine ⟨stage, ?_, terminal⟩
        rw [stagesFromFuel, dif_pos terminal]
        exact List.Mem.head []
      · have descent :
            normNat (advanceStage stage terminal).quotient.denominator <
              normNat stage.quotient.denominator := by
          rw [advanceStage_quotient]
          exact Nearest.remainder_norm_lt_denominator stage.quotient
        have currentLeFuel :
            normNat stage.quotient.denominator ≤ fuel :=
          Nat.le_of_lt_succ enough
        have nextEnough :
            normNat (advanceStage stage terminal).quotient.denominator < fuel :=
          descent.trans_le currentLeFuel
        obtain ⟨terminalStage, member, terminalStageTerminal⟩ :=
          inductionHypothesis (advanceStage stage terminal) nextEnough
        refine ⟨terminalStage, ?_, terminalStageTerminal⟩
        rw [stagesFromFuel, dif_neg terminal]
        exact List.Mem.tail stage member

/-- The denominator-norm-budgeted stage list contains a retained terminal stage. -/
theorem exists_terminal_mem_stagesFrom {source : Fraction}
    (stage : Stage source) :
    ∃ terminalStage,
      terminalStage ∈ stagesFrom stage ∧
        Nearest.remainder terminalStage.quotient = 0 := by
  exact exists_terminal_mem_stagesFromFuel
    (Nat.succ (normNat stage.quotient.denominator)) stage
      (Nat.lt_succ_self _)

/-- The source fraction's complete retained stage sequence contains a zero-remainder stage. -/
theorem exists_terminal_mem_stages (source : Fraction) :
    ∃ terminalStage,
      terminalStage ∈ stages source ∧
        Nearest.remainder terminalStage.quotient = 0 :=
  exists_terminal_mem_stagesFrom (firstStage source)

end Purelib.Data.ComplexContinuedFraction.Hurwitz.Trace

end
