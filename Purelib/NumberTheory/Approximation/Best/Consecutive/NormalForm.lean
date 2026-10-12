module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.GaussianInt.Norm.Bounds
import Purelib.Algebra.NatCast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Divisibility.Basic
import Purelib.Data.GaussianInt.Divisibility.NormTwo
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
public import Purelib.Data.GaussianInt.Norm.Small
import Purelib.Data.GaussianInt.Pair.Basis
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Best.Search
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Embedding
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section

/-!
# Finite coefficient patterns for consecutive Gaussian approximations

Unit and diagonal Gaussian coefficients retain the original source pairs and
mixed-cylinder comparisons. Their exact coordinate patterns give the displayed
error and denominator bounds without replacing either retained input pair.
-/

namespace Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm

/-- Algebraic part of the “no repeated index two” transition.  If two
successive determinant pairs both have quadrance two, the third pair cannot
lie in the centered coset of the first two.  It therefore has an ordinary
coefficient expansion, and its coefficient on the first pair is a Gaussian
unit. -/
theorem
  AreConsecutiveBest.integralTransition_of_two_index_two
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient : GaussianInt,
      GaussianInt.normNat lowerCoefficient = 1 ∧
        upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle
          lowerCoefficient middleCoefficient := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientSpan_or_centeredCoset consecutive) upper with
    integral | centered
  · rcases integral with
      ⟨lowerCoefficient, middleCoefficient, upperIdentity⟩
    refine ⟨lowerCoefficient, middleCoefficient, ?_, upperIdentity⟩
    have determinantIdentity :=
      congrArg (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle) upperIdentity
    rw [GaussianInt.Pair.LinearCombination.coefficientDeterminant_right_linearCombination] at determinantIdentity
    have normIdentity := congrArg GaussianInt.normNat determinantIdentity
    rw [GaussianInt.normNat_neg,
      GaussianInt.normNat_mul] at normIdentity
    change GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper =
      GaussianInt.normNat lowerCoefficient *
        GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle at normIdentity
    rw [leftIndexTwo, rightIndexTwo] at normIdentity
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by decide)
    calc
      GaussianInt.normNat lowerCoefficient * 2 = 2 := normIdentity.symm
      _ = 1 * 2 := rfl
  · change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle) leftCoefficient ∧
      ¬ GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle) rightCoefficient ∧
      GaussianInt.Pair.LinearCombination.scalePair (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower
        middle) upper =
        GaussianInt.Pair.LinearCombination.linearCombination lower middle leftCoefficient rightCoefficient
      at centered
    rcases centered with
      ⟨leftCoefficient, rightCoefficient, leftNotDivisible, _,
        scaledIdentity⟩
    have determinantIdentity :=
      congrArg (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle) scaledIdentity
    rw [GaussianInt.Pair.LinearCombination.coefficientDeterminant_scalePair_right,
      GaussianInt.Pair.LinearCombination.coefficientDeterminant_right_linearCombination] at determinantIdentity
    have normIdentity := congrArg GaussianInt.normNat determinantIdentity
    rw [GaussianInt.normNat_mul,
      GaussianInt.normNat_neg,
      GaussianInt.normNat_mul] at normIdentity
    have leftDeterminantNorm :
        GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle) = 2 := by
      simpa only [GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self] using leftIndexTwo
    have rightDeterminantNorm :
        GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle upper) = 2 := by
      simpa only [GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self] using rightIndexTwo
    have leftCoefficientNorm : GaussianInt.normNat leftCoefficient = 2 := by
      have normIdentity' := normIdentity
      rw [leftDeterminantNorm, rightDeterminantNorm] at normIdentity'
      have numericIdentity : 4 = 2 * GaussianInt.normNat leftCoefficient := by
        calc
          4 = 2 * 2 := by decide
          _ = GaussianInt.normNat leftCoefficient * 2 := normIdentity'
          _ = 2 * GaussianInt.normNat leftCoefficient := Nat.mul_comm _ _
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by decide)
      calc
        GaussianInt.normNat leftCoefficient * 2 = 2 * GaussianInt.normNat leftCoefficient :=
          Nat.mul_comm _ _
        _ = 4 := numericIdentity.symm
        _ = 2 * 2 := rfl
    exact False.elim
      (leftNotDivisible
        (GaussianInt.Divisibility.NormTwo.divides_of_norm_two
          leftDeterminantNorm leftCoefficientNorm))

/-- For two consecutive index-two transitions, the ordinary transition
coefficient on the middle pair is itself divisible by the first determinant.
Equivalently, the algebraic transition has Chevallier's displayed shape
`unit * lower + determinant * step * middle`.  This is the finite coefficient
part of the repeated-index analysis; it does not invoke the later geometric
argument excluding the transition altogether. -/
theorem
  AreConsecutiveBest.integralTransition_with_divisible_middleCoefficient
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerCoefficient middleCoefficient : GaussianInt,
      GaussianInt.normNat lowerCoefficient = 1 ∧
      GaussianInt.Divisibility.Basic.Divides
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle) middleCoefficient ∧
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle
        lowerCoefficient middleCoefficient := by
  obtain ⟨lowerCoefficient, middleCoefficient, lowerCoefficientNorm,
      upperIdentity⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.integralTransition_of_two_index_two first) leftIndexTwo
      rightIndexTwo
  let leftDeterminant := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle
  let rightDeterminant := GaussianInt.Pair.LinearCombination.coefficientDeterminant middle upper
  have leftDeterminantNorm : GaussianInt.normNat leftDeterminant = 2 := by
    simpa only [leftDeterminant, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
      using leftIndexTwo
  have rightDeterminantNorm : GaussianInt.normNat rightDeterminant = 2 := by
    simpa only [rightDeterminant, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
      using rightIndexTwo
  have oneNonzero : (1 : GaussianInt) ≠ 0 := by decide
  have oneNorm : GaussianInt.normNat (1 : GaussianInt) = 1 := rfl
  have oneNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides rightDeterminant 1 :=
    GaussianInt.Divisibility.Basic.not_divides_of_norm_lt oneNonzero
      (by rw [oneNorm, rightDeterminantNorm]; decide)
  obtain ⟨halfSum, halfSumIdentity⟩ :=
    (Best.Consecutive.Index.AreConsecutiveBest.exists_centeredCoefficientPair second) rightIndexTwo 1 1
      oneNotDivisible oneNotDivisible
  have determinantTransition :=
    congrArg (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle) upperIdentity
  rw [GaussianInt.Pair.LinearCombination.coefficientDeterminant_right_linearCombination] at determinantTransition
  have determinantTransition' :
      rightDeterminant = -(lowerCoefficient * leftDeterminant) := by
    simpa only [leftDeterminant, rightDeterminant, -eq_self, -iff_self] using determinantTransition
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientSpan_or_centeredCoset first) halfSum with
    integralHalfSum | centeredHalfSum
  · rcases integralHalfSum with
      ⟨lowerHalfCoefficient, middleHalfCoefficient, halfSumExpansion⟩
    have halfSumDeterminant :=
      congrArg (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle) halfSumIdentity
    rw [GaussianInt.Pair.LinearCombination.coefficientDeterminant_scalePair_right,
      GaussianInt.Pair.LinearCombination.coefficientDeterminant_left_linearCombination] at halfSumDeterminant
    have halfSpanDeterminant :=
      congrArg (GaussianInt.Pair.LinearCombination.coefficientDeterminant middle) halfSumExpansion
    rw [GaussianInt.Pair.LinearCombination.coefficientDeterminant_right_linearCombination] at halfSpanDeterminant
    rw [halfSpanDeterminant] at halfSumDeterminant
    have normIdentity := congrArg GaussianInt.normNat halfSumDeterminant
    rw [GaussianInt.normNat_mul,
      GaussianInt.normNat_neg,
      GaussianInt.normNat_mul, GaussianInt.one_mul]
        at normIdentity
    have normIdentity' := normIdentity
    rw [leftDeterminantNorm, rightDeterminantNorm] at normIdentity'
    have impossible : False := by
      have coefficientNormNonnegative :
          0 ≤ GaussianInt.normNat lowerHalfCoefficient := Nat.zero_le _
      omega
    exact False.elim impossible
  · change ∃ leftCoefficient rightCoefficient : GaussianInt,
      ¬ GaussianInt.Divisibility.Basic.Divides leftDeterminant leftCoefficient ∧
      ¬ GaussianInt.Divisibility.Basic.Divides leftDeterminant rightCoefficient ∧
      GaussianInt.Pair.LinearCombination.scalePair leftDeterminant halfSum =
        GaussianInt.Pair.LinearCombination.linearCombination lower middle leftCoefficient rightCoefficient
      at centeredHalfSum
    rcases centeredHalfSum with
      ⟨centeredLeft, centeredRight, _, centeredRightNotDivisible,
        centeredIdentity⟩
    have negatedScale :
        -lowerCoefficient * leftDeterminant = rightDeterminant := by
      calc
        -lowerCoefficient * leftDeterminant =
            -(lowerCoefficient * leftDeterminant) := by
          apply GaussianInt.ext <;>
            simp only [GaussianInt.neg_re,
              GaussianInt.neg_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
        _ = rightDeterminant := determinantTransition'.symm
    have centeredScaled :
        GaussianInt.Pair.LinearCombination.scalePair rightDeterminant halfSum =
          GaussianInt.Pair.LinearCombination.linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) := by
      calc
        GaussianInt.Pair.LinearCombination.scalePair rightDeterminant halfSum =
            GaussianInt.Pair.LinearCombination.scalePair (-lowerCoefficient * leftDeterminant) halfSum := by
          rw [negatedScale]
        _ = GaussianInt.Pair.LinearCombination.scalePair (-lowerCoefficient)
            (GaussianInt.Pair.LinearCombination.scalePair leftDeterminant halfSum) :=
          (GaussianInt.Pair.LinearCombination.scalePair_scalePair (-lowerCoefficient) leftDeterminant halfSum).symm
        _ = GaussianInt.Pair.LinearCombination.scalePair (-lowerCoefficient)
            (GaussianInt.Pair.LinearCombination.linearCombination lower middle centeredLeft centeredRight) :=
          congrArg (GaussianInt.Pair.LinearCombination.scalePair (-lowerCoefficient)) centeredIdentity
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) :=
          (GaussianInt.Pair.LinearCombination.linearCombination_scaleCoefficients lower middle
            (-lowerCoefficient) centeredLeft centeredRight).symm
    have halfSumFromTransition :
        GaussianInt.Pair.LinearCombination.scalePair rightDeterminant halfSum =
          GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) := by
      calc
        GaussianInt.Pair.LinearCombination.scalePair rightDeterminant halfSum =
            GaussianInt.Pair.LinearCombination.linearCombination middle upper 1 1 := halfSumIdentity
        _ = GaussianInt.Pair.LinearCombination.linearCombination middle
            (GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerCoefficient
              middleCoefficient) 1 1 := by rw [← upperIdentity]
        _ = GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) := by
          apply GaussianInt.Pair.LinearCombination.pair_ext <;>
            apply GaussianInt.ext <;>
            simp only [GaussianInt.Pair.LinearCombination.linearCombination,
              GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.add_re,
              GaussianInt.add_im,
              GaussianInt.mul_re,
              GaussianInt.mul_im, -eq_self, -iff_self] <;>
            ring1
    have combinationsEqual :
        GaussianInt.Pair.LinearCombination.linearCombination lower middle
            (-lowerCoefficient * centeredLeft)
            (-lowerCoefficient * centeredRight) =
          GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerCoefficient
            (1 + middleCoefficient) :=
      centeredScaled.symm.trans halfSumFromTransition
    have leftDeterminantNonzero : leftDeterminant ≠ 0 := by
      intro determinantZero
      rw [determinantZero] at leftDeterminantNorm
      contradiction
    have coefficientIdentities :=
      GaussianInt.Pair.LinearCombination.linearCombination_coefficients_eq_of_determinant_ne_zero
        lower middle leftDeterminantNonzero combinationsEqual
    have negatedCoefficientNorm :
        GaussianInt.normNat (-lowerCoefficient) = 1 := by
      rw [GaussianInt.normNat_neg,
        lowerCoefficientNorm]
    have negatedCoefficientNonzero : -lowerCoefficient ≠ 0 := by
      intro coefficientZero
      have zeroNorm := congrArg GaussianInt.normNat coefficientZero
      rw [negatedCoefficientNorm] at zeroNorm
      contradiction
    have negatedCoefficientNotDivisible :
        ¬ GaussianInt.Divisibility.Basic.Divides leftDeterminant
          (-lowerCoefficient) :=
      GaussianInt.Divisibility.Basic.not_divides_of_norm_lt
        negatedCoefficientNonzero
        (by rw [negatedCoefficientNorm, leftDeterminantNorm]; decide)
    have sumNotDivisible :
        ¬ GaussianInt.Divisibility.Basic.Divides leftDeterminant
          (1 + middleCoefficient) := by
      rw [← coefficientIdentities.2]
      exact GaussianInt.Divisibility.NormTwo.not_divides_mul_of_norm_two
        leftDeterminantNorm negatedCoefficientNotDivisible
          centeredRightNotDivisible
    have negativeOneNonzero : (-1 : GaussianInt) ≠ 0 := by decide
    have negativeOneNorm : GaussianInt.normNat (-1 : GaussianInt) = 1 := by decide
    have negativeOneNotDivisible :
        ¬ GaussianInt.Divisibility.Basic.Divides leftDeterminant (-1) :=
      GaussianInt.Divisibility.Basic.not_divides_of_norm_lt negativeOneNonzero
        (by rw [negativeOneNorm, leftDeterminantNorm]; decide)
    have middleCoefficientDivisibleSum :=
      GaussianInt.Divisibility.NormTwo.divides_add_of_not_divides_of_norm_two
        leftDeterminantNorm sumNotDivisible negativeOneNotDivisible
    rcases middleCoefficientDivisibleSum with
      ⟨middleQuotient, middleSumIdentity⟩
    have middleCoefficientDivisible :
        GaussianInt.Divisibility.Basic.Divides leftDeterminant middleCoefficient := by
      refine ⟨middleQuotient, ?_⟩
      calc
        middleCoefficient = (1 + middleCoefficient) + (-1) := by
          apply GaussianInt.ext <;>
            simp only [GaussianInt.one_re,
              GaussianInt.one_im,
              GaussianInt.neg_re,
              GaussianInt.neg_im,
              GaussianInt.add_re,
              GaussianInt.add_im, -eq_self, -iff_self] <;>
            ring1
        _ = leftDeterminant * middleQuotient := middleSumIdentity
    exact ⟨lowerCoefficient, middleCoefficient, lowerCoefficientNorm,
      middleCoefficientDivisible, upperIdentity⟩

/-- Fully witnessed repeated-index normal form.  Two hypothetical successive
index-two transitions produce a Gaussian unit on the first pair and a
nonzero displayed Gaussian step multiplying the first determinant on the
middle pair.  The nonzeroness follows from the strict increase through the
two denominator levels. -/
theorem
  AreConsecutiveBest.repeatedIndexTwo_normalForm
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      GaussianInt.normNat lowerUnit = 1 ∧ step ≠ 0 ∧
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerUnit
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, middleCoefficient, lowerUnitNorm,
      middleCoefficientDivisible, upperIdentity⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.integralTransition_with_divisible_middleCoefficient first) second
      leftIndexTwo rightIndexTwo
  rcases middleCoefficientDivisible with ⟨step, middleCoefficientIdentity⟩
  have witnessedIdentity :
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerUnit
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle * step) := by
    rw [← middleCoefficientIdentity]
    exact upperIdentity
  have stepNonzero : step ≠ 0 := by
    intro stepZero
    have upperDenominatorIdentity :
        upper.denominator = lowerUnit * lower.denominator := by
      rw [witnessedIdentity, stepZero]
      apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.linearCombination,
          GaussianInt.zero_re,
          GaussianInt.zero_im,
          GaussianInt.add_re,
          GaussianInt.add_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im, -eq_self, -iff_self] <;>
        ring1
    have denominatorQuadranceIdentity :=
      congrArg GaussianInt.normNat upperDenominatorIdentity
    rw [GaussianInt.normNat_mul, lowerUnitNorm, Nat.one_mul]
      at denominatorQuadranceIdentity
    have lowerBelowUpper :
        Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper :=
      first.2.2.1.trans second.2.2.1
    change Best.Error.denominatorQuadrance upper = Best.Error.denominatorQuadrance lower
      at denominatorQuadranceIdentity
    omega
  exact ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, witnessedIdentity⟩

/-- A nontrivial coefficient combination of consecutive best pairs is a
nonzero source-lattice vector. -/
theorem
  AreConsecutiveBest.linearCombination_pairNonzero
    {source : Gaussian.Basic.Canonical} {left right : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    GaussianInt.Pair.LinearCombination.PairNonzero
      (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) := by
  apply (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair _).mpr
  intro combinationZero
  rcases coefficientNonzero with leftNonzero | rightNonzero
  · have determinantZero :
        GaussianInt.Pair.LinearCombination.coefficientDeterminant
            (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient)
              right = 0 := by
      rw [combinationZero]
      apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.coefficientDeterminant, GaussianInt.Pair.Basis.determinant,
          GaussianInt.Pair.LinearCombination.zeroPair,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.zero_re,
          GaussianInt.zero_im, -eq_self, -iff_self] <;>
        ring1
    have productZero :
        leftCoefficient * GaussianInt.Pair.LinearCombination.coefficientDeterminant left right = 0 := by
      rw [← GaussianInt.Pair.LinearCombination.coefficientDeterminant_linearCombination_right]
      exact determinantZero
    have normProductZero := congrArg GaussianInt.normNat productZero
    rw [GaussianInt.normNat_mul] at normProductZero
    have leftPositive := GaussianInt.normNat_pos leftNonzero
    have determinantPositive := consecutive.coefficientIndexQuadrance_pos
    change GaussianInt.normNat leftCoefficient * GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance left right
      = 0
      at normProductZero
    exact (Nat.ne_of_gt
      (Nat.mul_pos leftPositive determinantPositive)) normProductZero
  · have determinantZero :
        GaussianInt.Pair.LinearCombination.coefficientDeterminant left
            (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) =
          0 := by
      rw [combinationZero]
      apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.coefficientDeterminant, GaussianInt.Pair.Basis.determinant,
          GaussianInt.Pair.LinearCombination.zeroPair,
          GaussianInt.sub_re,
          GaussianInt.sub_im,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.zero_re,
          GaussianInt.zero_im, -eq_self, -iff_self] <;>
        ring1
    have productZero :
        rightCoefficient * GaussianInt.Pair.LinearCombination.coefficientDeterminant left right = 0 := by
      rw [← GaussianInt.Pair.LinearCombination.coefficientDeterminant_left_linearCombination]
      exact determinantZero
    have normProductZero := congrArg GaussianInt.normNat productZero
    rw [GaussianInt.normNat_mul] at normProductZero
    have rightPositive := GaussianInt.normNat_pos rightNonzero
    have determinantPositive := consecutive.coefficientIndexQuadrance_pos
    change GaussianInt.normNat rightCoefficient * GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance left
      right = 0
      at normProductZero
    exact (Nat.ne_of_gt
      (Nat.mul_pos rightPositive determinantPositive)) normProductZero

/-- Every Gaussian unit determines a displayed member of the centered coset
of an index-two consecutive pair.  Its empty mixed cylinder forces this
explicitly constructed half-difference to lie outside that cylinder. -/
theorem
  AreConsecutiveBest.exists_centeredUnitCandidate_outsideCylinder
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    ∃ candidate : GaussianInt.Pair.Basic.ConvergentPair,
      GaussianInt.Pair.LinearCombination.PairNonzero candidate ∧
      GaussianInt.Pair.LinearCombination.scalePair (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower
        upper) candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1 ∧
      ¬ Best.Consecutive.Basic.InOpenMixedCylinder source.value lower upper candidate := by
  let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper
  have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
    simpa only [determinantValue, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
      using indexTwo
  have unitNonzero : unit ≠ 0 := by
    intro unitZero
    have zeroNorm := congrArg GaussianInt.normNat unitZero
    rw [unitNorm] at zeroNorm
    contradiction
  have negatedUnitNonzero : -unit ≠ 0 := by
    intro negatedZero
    have zeroNorm := congrArg GaussianInt.normNat negatedZero
    rw [GaussianInt.normNat_neg,
      unitNorm] at zeroNorm
    contradiction
  have negatedUnitNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue (-unit) :=
    GaussianInt.Divisibility.Basic.not_divides_of_norm_lt negatedUnitNonzero
      (by
        rw [GaussianInt.normNat_neg,
          unitNorm, determinantNorm]
        decide)
  have oneNonzero : (1 : GaussianInt) ≠ 0 := by decide
  have oneNotDivisible :
      ¬ GaussianInt.Divisibility.Basic.Divides determinantValue 1 :=
    GaussianInt.Divisibility.Basic.not_divides_of_norm_lt oneNonzero
      (by rw [determinantNorm]; decide)
  obtain ⟨candidate, centeredIdentity⟩ :=
    (Best.Consecutive.Index.AreConsecutiveBest.exists_centeredCoefficientPair consecutive) indexTwo (-unit) 1
      negatedUnitNotDivisible oneNotDivisible
  have combinationNonzero :
      GaussianInt.Pair.LinearCombination.PairNonzero (GaussianInt.Pair.LinearCombination.linearCombination lower upper
        (-unit) 1) :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.linearCombination_pairNonzero consecutive) (-unit) 1
      (Or.inl negatedUnitNonzero)
  have candidateNonzero : GaussianInt.Pair.LinearCombination.PairNonzero candidate := by
    apply (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair candidate).mpr
    intro candidateZero
    have combinationZero :
        GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1 =
          GaussianInt.Pair.LinearCombination.zeroPair := by
      rw [← centeredIdentity, candidateZero]
      apply GaussianInt.Pair.LinearCombination.pair_ext <;>
        apply GaussianInt.ext <;>
        simp only [GaussianInt.Pair.LinearCombination.scalePair, GaussianInt.Pair.LinearCombination.zeroPair,
          GaussianInt.mul_re,
          GaussianInt.mul_im,
          GaussianInt.zero_re,
          GaussianInt.zero_im, -eq_self, -iff_self] <;>
        ring1
    exact (GaussianInt.Pair.LinearCombination.pairNonzero_iff_ne_zeroPair _).mp combinationNonzero combinationZero
  have cylinderEmpty :=
    (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source lower upper).mp
      consecutive |>.2.2.2
  exact ⟨candidate, candidateNonzero, centeredIdentity,
    cylinderEmpty candidate candidateNonzero⟩

/-- The same centered half-difference also lies outside the next mixed
cylinder whenever another consecutive level follows.  These four finite
candidates are the starting point of the geometric obstruction to two
successive index-two transitions. -/
theorem
  AreConsecutiveBest.exists_centeredUnitCandidate_outside_nextCylinder
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    ∃ candidate : GaussianInt.Pair.Basic.ConvergentPair,
      GaussianInt.Pair.LinearCombination.PairNonzero candidate ∧
      GaussianInt.Pair.LinearCombination.scalePair (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower
        middle) candidate =
        GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1 ∧
      ¬ Best.Consecutive.Basic.InOpenMixedCylinder source.value middle upper candidate := by
  obtain ⟨candidate, candidateNonzero, centeredIdentity, _⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.exists_centeredUnitCandidate_outsideCylinder first) leftIndexTwo
      unit unitNorm
  have nextCylinderEmpty :=
    (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source middle upper).mp second
      |>.2.2.2
  exact ⟨candidate, candidateNonzero, centeredIdentity,
    nextCylinderEmpty candidate candidateNonzero⟩

/-- The centered candidate tested against its own index-two cylinder gives
the exact finite constraint on the two normalized coordinates used in the
index-two geometry: at least one of its two scaled coordinate quadrances must
reach the corresponding boundary. -/
theorem
  AreConsecutiveBest.centeredUnit_selfObstruction
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower ≤
        Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) ∨
      2 * Best.Error.denominatorQuadrance upper ≤
        Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) := by
  obtain ⟨candidate, _, centeredIdentity, outside⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.exists_centeredUnitCandidate_outsideCylinder consecutive) indexTwo
      unit unitNorm
  have determinantNorm :
      GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper) = 2 := by
    simpa only [GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self] using indexTwo
  have errorIdentity :=
    congrArg (Best.Error.errorQuadrance source.value) centeredIdentity
  rw [Best.Error.errorQuadrance_scalePair, determinantNorm] at errorIdentity
  have denominatorIdentity :=
    congrArg Best.Error.denominatorQuadrance centeredIdentity
  rw [Best.Error.denominatorQuadrance_scalePair, determinantNorm] at denominatorIdentity
  by_cases errorInside :
      Best.Error.errorQuadrance source.value candidate <
        Best.Error.errorQuadrance source.value lower
  · have denominatorNotInside :
        ¬ Best.Error.denominatorQuadrance candidate < Best.Error.denominatorQuadrance upper := by
      intro denominatorInside
      exact outside ⟨errorInside, denominatorInside⟩
    right
    calc
      2 * Best.Error.denominatorQuadrance upper ≤
          2 * Best.Error.denominatorQuadrance candidate :=
        Nat.mul_le_mul_left 2 (Nat.le_of_not_gt denominatorNotInside)
      _ = Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) := denominatorIdentity
  · have errorOutside :
        Best.Error.errorQuadrance source.value lower ≤
          Best.Error.errorQuadrance source.value candidate :=
      le_of_not_gt errorInside
    left
    calc
      (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower ≤
          (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value candidate :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorOutside (by decide)
      _ = Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) := errorIdentity

/-- The self-cylinder obstruction in its geometric coordinate form.  This is
the form consumed by the finite repeated-index case table. -/
theorem
  AreConsecutiveBest.centeredUnit_selfCoordinateObstruction
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) ≤
        Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value upper -
          GaussianInt.toGaussian unit * Best.Error.error source.value lower) ∨
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator -
          GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
  rcases (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfObstruction consecutive) indexTwo unit
    unitNorm with
    errorExterior | denominatorExterior
  · left
    rw [← Best.Error.error_linearCombination_negUnit_one]
    exact errorExterior
  · right
    have castExterior :=
      Fraction.Cast.Order.natCast_le_direct denominatorExterior
    calc
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) =
          ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational) := by
        rw [GaussianInt.normSq_toGaussian]
        change (2 : Fraction.Rational) *
            (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
          ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational)
        rw [Algebra.NatCast.mul, Nat.cast_ofNat]
      _ ≤
          (Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) : Fraction.Rational) :=
        castExterior
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian
            (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1).denominator) :=
        (GaussianInt.normSq_toGaussian _).symm
      _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator -
          GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
        rw [Best.Error.toGaussian_denominator_linearCombination_negUnit_one]

/-- Two opposite unit translates cannot both reach twice the larger
quadrance when the moving vector is strictly shorter.  This is the
parallelogram calculation used in the finite four-unit argument. -/
theorem not_both_opposite_exterior
    {large small firstDifference secondDifference : Fraction.Rational}
    (ordered : small < large)
    (firstExterior : 2 * large ≤ firstDifference)
    (secondExterior : 2 * large ≤ secondDifference)
    (parallelogram :
      firstDifference + secondDifference = 2 * (large + small)) : False := by
  have summed : 2 * large + 2 * large ≤
      firstDifference + secondDifference :=
    add_le_add firstExterior secondExterior
  rw [parallelogram] at summed
  have twiceOrderedReverse : 2 * large ≤ 2 * small := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct summed (2 * large)
    convert shifted using 1 <;> ring1
  have orderedReverse : large ≤ small := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := 2)
    · simpa only [Fraction.Field.mul_comm, -eq_self, -iff_self] using
        twiceOrderedReverse
    · decide
  exact (not_lt_of_ge orderedReverse) ordered

/-- Two adjacent unit translates cannot both reach twice the larger
quadrance once the larger quadrance is at least four times the smaller one.
The two associated projections are orthogonal, so their squared sum is the
product of the two quadrances. -/
theorem
  not_both_adjacent_exterior_of_four_mul_small_le
    {large small firstProjection secondProjection : Fraction.Rational}
    (largeNonnegative : 0 ≤ large) (smallNonnegative : 0 ≤ small)
    (ordered : small < large) (fourSmallLe : 4 * small ≤ large)
    (projectionSquares :
      firstProjection ^ 2 + secondProjection ^ 2 = large * small)
    (firstExterior :
      2 * large ≤ large + small - 2 * firstProjection)
    (secondExterior :
      2 * large ≤ large + small - 2 * secondProjection) : False := by
  let gap := large - small
  have gapPositive : 0 < gap := by
    dsimp only [gap, -eq_self, -iff_self]
    exact Fraction.Order.Arithmetic.sub_pos_direct ordered
  have firstProjectionBound : gap ≤ -2 * firstProjection := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct firstExterior (large + small)
    change 2 * large - (large + small) ≤
      (large + small - 2 * firstProjection) - (large + small) at shifted
    convert shifted using 1
    · dsimp only [gap, -eq_self, -iff_self]
      ring1
    · ring1
  have secondProjectionBound : gap ≤ -2 * secondProjection := by
    have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct secondExterior (large + small)
    change 2 * large - (large + small) ≤
      (large + small - 2 * secondProjection) - (large + small) at shifted
    convert shifted using 1
    · dsimp only [gap, -eq_self, -iff_self]
      ring1
    · ring1
  have firstSquare : gap ^ 2 ≤ (-2 * firstProjection) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.le_of_lt_direct gapPositive)
      firstProjectionBound 2
  have secondSquare : gap ^ 2 ≤ (-2 * secondProjection) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Fraction.Order.Arithmetic.le_of_lt_direct gapPositive)
      secondProjectionBound 2
  have twiceGapBound : 2 * gap ^ 2 ≤ 4 * (large * small) := by
    calc
      2 * gap ^ 2 = gap ^ 2 + gap ^ 2 := by ring1
      _ ≤ (-2 * firstProjection) ^ 2 +
          (-2 * secondProjection) ^ 2 :=
        add_le_add firstSquare secondSquare
      _ = 4 * (firstProjection ^ 2 + secondProjection ^ 2) := by ring1
      _ = 4 * (large * small) := by rw [projectionSquares]
  have gapSquareLe : gap ^ 2 ≤ 2 * large * small := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := 2)
    · calc
        gap ^ 2 * 2 = 2 * gap ^ 2 := by ring1
        _ ≤ 4 * (large * small) := twiceGapBound
        _ = (2 * large * small) * 2 := by ring1
    · decide
  have largeMinusFourSmallNonnegative : 0 ≤ large - 4 * small :=
    Fraction.Order.Arithmetic.sub_nonneg_direct fourSmallLe
  have leadingNonnegative : 0 ≤ large * (large - 4 * small) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct largeNonnegative
      largeMinusFourSmallNonnegative
  have strictPolynomial : 0 < large * (large - 4 * small) + small ^ 2 := by
    by_cases smallZero : small = 0
    · rw [smallZero] at ordered ⊢
      have largePositive : 0 < large := ordered
      calc
        0 < large * large :=
          Fraction.Order.Arithmetic.mul_pos_direct largePositive largePositive
        _ = large * (large - 4 * 0) + 0 ^ 2 := by ring1
    · have smallPositive : 0 < small :=
        lt_of_le_of_ne smallNonnegative (Ne.symm smallZero)
      have smallSquarePositive : 0 < small ^ 2 := by
        simpa only [pow_two, -eq_self, -iff_self] using
          Fraction.Order.Arithmetic.mul_pos_direct smallPositive smallPositive
      exact lt_of_lt_of_le smallSquarePositive
        (le_add_of_nonneg_left leadingNonnegative)
  have strictGap : 2 * large * small < gap ^ 2 := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      0 < large * (large - 4 * small) + small ^ 2 := strictPolynomial
      _ = gap ^ 2 - 2 * large * small := by
        dsimp only [gap, -eq_self, -iff_self]
        ring1
  exact (not_lt_of_ge gapSquareLe strictGap).elim

/-- Four centered-unit cylinder obstructions force a quantitative separation
between the two error levels.  The proof is a finite sixteen-case argument:
two error exteriors are impossible by the preceding opposite/adjacent
calculations, while any three denominator exteriors contain an opposite
pair and are impossible by the parallelogram identity. -/
theorem
  four_unit_obstructions_force_error_lt_four_mul
    (largeError smallError lowerDenominator upperDenominator : Gaussian.Basic.Canonical)
    (errorOrdered : Data.Gaussian.Norm.Basic.normSq smallError < Data.Gaussian.Norm.Basic.normSq largeError)
    (denominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq lowerDenominator < Data.Gaussian.Norm.Basic.normSq upperDenominator)
    (positiveOneObstruction :
      2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (1 : GaussianInt) * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (1 : GaussianInt) * lowerDenominator))
    (negativeOneObstruction :
      2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (-1 : GaussianInt) * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (-1 : GaussianInt) * lowerDenominator))
    (positiveImaginaryObstruction :
      2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * lowerDenominator))
    (negativeImaginaryObstruction :
      2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * largeError) ∨
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) *
              lowerDenominator)) :
    Data.Gaussian.Norm.Basic.normSq largeError < 4 * Data.Gaussian.Norm.Basic.normSq smallError := by
  apply lt_of_not_ge
  intro fourSmallLe
  let large := Data.Gaussian.Norm.Basic.normSq largeError
  let small := Data.Gaussian.Norm.Basic.normSq smallError
  let firstProjection : Fraction.Rational :=
    smallError.re * largeError.re + smallError.im * largeError.im
  let secondProjection : Fraction.Rational :=
    -smallError.re * largeError.im + smallError.im * largeError.re
  have largeNonnegative : 0 ≤ large := Gaussian.Norm.Basic.normSq_nonneg largeError
  have smallNonnegative : 0 ≤ small := Gaussian.Norm.Basic.normSq_nonneg smallError
  have projectionSquares :
      firstProjection ^ 2 + secondProjection ^ 2 = large * small := by
    dsimp only [firstProjection, secondProjection, large, small, Data.Gaussian.Norm.Basic.normSq, -eq_self,
      -iff_self]
    ring1
  have positiveOneExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (1 : GaussianInt) * largeError) =
        large + small - 2 * firstProjection := by
    dsimp only [large, small, firstProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, -eq_self,
      -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.one_re,
      GaussianInt.one_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have negativeOneExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (-1 : GaussianInt) * largeError) =
        large + small - 2 * (-firstProjection) := by
    dsimp only [large, small, firstProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, -eq_self,
      -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.one_re,
      GaussianInt.one_im,
      -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have positiveImaginaryExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError) =
        large + small - 2 * secondProjection := by
    dsimp only [large, small, secondProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
      GaussianInt.Norm.Small.imaginaryUnit, -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have negativeImaginaryExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError -
          GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * largeError) =
        large + small - 2 * (-secondProjection) := by
    dsimp only [large, small, secondProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
      GaussianInt.Norm.Small.imaginaryUnit, -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have errorOneNegativeOneImpossible
      (positiveExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (1 : GaussianInt) * largeError))
      (negativeExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (-1 : GaussianInt) * largeError)) :
      False := by
    apply not_both_opposite_exterior errorOrdered positiveExterior
      negativeExterior
    rw [positiveOneExpansion, negativeOneExpansion]
    dsimp only [large, small, -eq_self, -iff_self]
    ring1
  have errorImaginaryOppositesImpossible
      (positiveExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError))
      (negativeExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * largeError)) :
      False := by
    apply not_both_opposite_exterior errorOrdered positiveExterior
      negativeExterior
    rw [positiveImaginaryExpansion, negativeImaginaryExpansion]
    dsimp only [large, small, -eq_self, -iff_self]
    ring1
  have errorOneImaginaryImpossible
      (oneExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (1 : GaussianInt) * largeError))
      (imaginaryExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError)) :
      False := by
    rw [positiveOneExpansion] at oneExterior
    rw [positiveImaginaryExpansion] at imaginaryExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      projectionSquares oneExterior imaginaryExterior
  have errorImaginaryNegativeOneImpossible
      (imaginaryExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError))
      (negativeOneExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (-1 : GaussianInt) * largeError)) :
      False := by
    rw [positiveImaginaryExpansion] at imaginaryExterior
    rw [negativeOneExpansion] at negativeOneExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          secondProjection ^ 2 + (-firstProjection) ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      imaginaryExterior negativeOneExterior
  have errorNegativeOneNegativeImaginaryImpossible
      (negativeOneExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (-1 : GaussianInt) * largeError))
      (negativeImaginaryExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * largeError)) :
      False := by
    rw [negativeOneExpansion] at negativeOneExterior
    rw [negativeImaginaryExpansion] at negativeImaginaryExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          (-firstProjection) ^ 2 + (-secondProjection) ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      negativeOneExterior negativeImaginaryExterior
  have errorNegativeImaginaryOneImpossible
      (negativeImaginaryExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) * largeError))
      (oneExterior :
        2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
          Data.Gaussian.Norm.Basic.normSq (smallError - GaussianInt.toGaussian (1 : GaussianInt) * largeError)) :
      False := by
    rw [negativeImaginaryExpansion] at negativeImaginaryExterior
    rw [positiveOneExpansion] at oneExterior
    exact not_both_adjacent_exterior_of_four_mul_small_le
      largeNonnegative smallNonnegative errorOrdered fourSmallLe
      (by
        calc
          (-secondProjection) ^ 2 + firstProjection ^ 2 =
              firstProjection ^ 2 + secondProjection ^ 2 := by ring1
          _ = large * small := projectionSquares)
      negativeImaginaryExterior oneExterior
  have denominatorOneNegativeOneImpossible
      (positiveExterior :
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (1 : GaussianInt) * lowerDenominator))
      (negativeExterior :
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (-1 : GaussianInt) * lowerDenominator)) : False := by
    apply not_both_opposite_exterior denominatorOrdered positiveExterior
      negativeExterior
    dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im,
      GaussianInt.one_re,
      GaussianInt.one_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have denominatorImaginaryOppositesImpossible
      (positiveExterior :
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * lowerDenominator))
      (negativeExterior :
        2 * Data.Gaussian.Norm.Basic.normSq upperDenominator ≤
          Data.Gaussian.Norm.Basic.normSq (upperDenominator -
            GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) *
              lowerDenominator)) : False := by
    apply not_both_opposite_exterior denominatorOrdered positiveExterior
      negativeExterior
    dsimp only [Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian, GaussianInt.Norm.Small.imaginaryUnit,
      -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im,
      GaussianInt.neg_re,
      GaussianInt.neg_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  rcases positiveOneObstruction with errorOne | denominatorOne <;>
    rcases negativeOneObstruction with errorNegativeOne |
      denominatorNegativeOne <;>
    rcases positiveImaginaryObstruction with errorImaginary |
      denominatorImaginary <;>
    rcases negativeImaginaryObstruction with errorNegativeImaginary |
      denominatorNegativeImaginary
  all_goals first
    | exact errorOneNegativeOneImpossible errorOne errorNegativeOne
    | exact errorImaginaryOppositesImpossible errorImaginary
        errorNegativeImaginary
    | exact errorOneImaginaryImpossible errorOne errorImaginary
    | exact errorImaginaryNegativeOneImpossible errorImaginary errorNegativeOne
    | exact errorNegativeOneNegativeImaginaryImpossible errorNegativeOne
        errorNegativeImaginary
    | exact errorNegativeImaginaryOneImpossible errorNegativeImaginary errorOne
    | exact denominatorOneNegativeOneImpossible denominatorOne
        denominatorNegativeOne
    | exact denominatorImaginaryOppositesImpossible denominatorImaginary
        denominatorNegativeImaginary

/-- Square-root-free reverse-triangle estimate at the numerical threshold
needed below.  If one summand has quadrance at least ten times the comparison
quadrance while the other has quadrance below four times it, their sum cannot
have smaller quadrance than the comparison value.  `dotBound` is the
two-coordinate Cauchy certificate. -/
theorem large_summand_sum_not_lt_comparison
    {multipliedNorm baseNorm comparisonNorm dotValue sumNorm : Fraction.Rational}
    (comparisonPositive : 0 < comparisonNorm)
    (baseNonnegative : 0 ≤ baseNorm)
    (tenComparisonLe : 10 * comparisonNorm ≤ multipliedNorm)
    (baseLtFourComparison : baseNorm < 4 * comparisonNorm)
    (dotBound : dotValue ^ 2 ≤ multipliedNorm * baseNorm)
    (sumExpansion :
      sumNorm = multipliedNorm + baseNorm + 2 * dotValue) :
    ¬ sumNorm < comparisonNorm := by
  intro sumSmaller
  let gap := multipliedNorm + baseNorm - comparisonNorm
  have nineComparisonPositive : 0 < 9 * comparisonNorm :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) comparisonPositive
  have nineComparisonLeGap : 9 * comparisonNorm ≤ gap := by
    have added := add_le_add tenComparisonLe baseNonnegative
    calc
      9 * comparisonNorm =
          (10 * comparisonNorm + 0) - comparisonNorm := by ring1
      _ ≤ (multipliedNorm + baseNorm) - comparisonNorm :=
        Fraction.Order.Arithmetic.sub_le_sub_right_direct added comparisonNorm
      _ = gap := by rfl
  have gapPositive : 0 < gap :=
    lt_of_lt_of_le nineComparisonPositive nineComparisonLeGap
  have gapLtNegTwiceDot : gap < -2 * dotValue := by
    rw [sumExpansion] at sumSmaller
    have shifted := Fraction.Order.Arithmetic.sub_lt_sub_right_direct
      sumSmaller (2 * dotValue)
    have shiftedAgain := Fraction.Order.Arithmetic.sub_lt_sub_right_direct
      shifted comparisonNorm
    calc
      gap =
          (multipliedNorm + baseNorm + 2 * dotValue - 2 * dotValue) -
            comparisonNorm := by
        dsimp only [gap, -eq_self, -iff_self]
        ring1
      _ < (comparisonNorm - 2 * dotValue) - comparisonNorm :=
        shiftedAgain
      _ = -2 * dotValue := by ring1
  have negTwiceDotPositive : 0 < -2 * dotValue :=
    gapPositive.trans gapLtNegTwiceDot
  have gapSquareLt : gap ^ 2 < (-2 * dotValue) ^ 2 := by
    have first : gap * gap < gap * (-2 * dotValue) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct gapPositive
        gapLtNegTwiceDot
    have second : gap * (-2 * dotValue) <
        (-2 * dotValue) * (-2 * dotValue) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        gapLtNegTwiceDot negTwiceDotPositive
    simpa only [pow_two, -eq_self, -iff_self] using first.trans second
  have gapSquareLtFourProduct :
      gap ^ 2 < 4 * (multipliedNorm * baseNorm) := by
    calc
      gap ^ 2 < (-2 * dotValue) ^ 2 := gapSquareLt
      _ = 4 * dotValue ^ 2 := by ring1
      _ ≤ 4 * (multipliedNorm * baseNorm) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          dotBound (by decide)
  have comparisonNonnegative : 0 ≤ comparisonNorm :=
    Fraction.Order.Arithmetic.le_of_lt_direct comparisonPositive
  have multipliedNonnegative : 0 ≤ multipliedNorm :=
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 10 by decide) comparisonNonnegative).trans
      tenComparisonLe
  have firstLeftNonnegative :
      0 ≤ multipliedNorm - 10 * comparisonNorm :=
    Fraction.Order.Arithmetic.sub_nonneg_direct tenComparisonLe
  have twiceBaseLtEightComparison :
      2 * baseNorm < 8 * comparisonNorm := by
    calc
      2 * baseNorm < 2 * (4 * comparisonNorm) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) baseLtFourComparison
      _ = 8 * comparisonNorm := by ring1
  have firstRightPositive :
      0 < multipliedNorm + 8 * comparisonNorm - 2 * baseNorm := by
    have baselineStrict :
        10 * comparisonNorm <
          10 * comparisonNorm + 8 * comparisonNorm - 2 * baseNorm := by
      have subtracted := Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        twiceBaseLtEightComparison
        (10 * comparisonNorm + 8 * comparisonNorm)
      convert subtracted using 1
      · ring1
    have baselineLe :
        10 * comparisonNorm + 8 * comparisonNorm - 2 * baseNorm ≤
          multipliedNorm + 8 * comparisonNorm - 2 * baseNorm := by
      have sumLe := add_le_add_left tenComparisonLe (8 * comparisonNorm)
      have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct sumLe (2 * baseNorm)
      exact shifted
    exact (Fraction.Order.Arithmetic.mul_pos_direct
      (show (0 : Fraction.Rational) < 10 by decide) comparisonPositive).trans
        (lt_of_lt_of_le baselineStrict baselineLe)
  have firstProductNonnegative :
      0 ≤ (multipliedNorm - 10 * comparisonNorm) *
        (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct firstLeftNonnegative
      (Fraction.Order.Arithmetic.le_of_lt_direct firstRightPositive)
  have secondLeftPositive : 0 < 4 * comparisonNorm - baseNorm :=
    Fraction.Order.Arithmetic.sub_pos_direct baseLtFourComparison
  have secondRightPositive : 0 < 18 * comparisonNorm - baseNorm :=
    Fraction.Order.Arithmetic.sub_pos_direct (baseLtFourComparison.trans
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (show (4 : Fraction.Rational) < 18 by decide) comparisonPositive))
  have secondProductNonnegative :
      0 ≤ (4 * comparisonNorm - baseNorm) *
        (18 * comparisonNorm - baseNorm) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.le_of_lt_direct secondLeftPositive)
      (Fraction.Order.Arithmetic.le_of_lt_direct secondRightPositive)
  have nineSquarePositive : 0 < 9 * comparisonNorm ^ 2 := by
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.pow_pos_direct comparisonPositive 2)
  have polynomialPositive :
      0 <
        (multipliedNorm - 10 * comparisonNorm) *
            (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
          (4 * comparisonNorm - baseNorm) *
            (18 * comparisonNorm - baseNorm) +
          9 * comparisonNorm ^ 2 := by
    apply lt_of_lt_of_le nineSquarePositive
    calc
      9 * comparisonNorm ^ 2 ≤
          (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 :=
        le_add_of_nonneg_left secondProductNonnegative
      _ ≤
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            ((4 * comparisonNorm - baseNorm) *
                (18 * comparisonNorm - baseNorm) +
              9 * comparisonNorm ^ 2) :=
        le_add_of_nonneg_left firstProductNonnegative
      _ =
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 := by ring1
  have fourProductLtGapSquare :
      4 * (multipliedNorm * baseNorm) < gap ^ 2 := by
    apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
    calc
      0 <
          (multipliedNorm - 10 * comparisonNorm) *
              (multipliedNorm + 8 * comparisonNorm - 2 * baseNorm) +
            (4 * comparisonNorm - baseNorm) *
              (18 * comparisonNorm - baseNorm) +
            9 * comparisonNorm ^ 2 := polynomialPositive
      _ = gap ^ 2 - 4 * (multipliedNorm * baseNorm) := by
        dsimp only [gap, -eq_self, -iff_self]
        ring1
  exact (not_lt_of_ge
    (Fraction.Order.Arithmetic.le_of_lt_direct fourProductLtGapSquare)
    gapSquareLtFourProduct).elim

/-- An index-two consecutive pair has a uniform rational error-ratio gap:
the lower error quadrance is strictly less than four times the upper error
quadrance.  This deliberately weaker square-root-free form of Chevallier's
chamber bound is already strong enough to bound the coefficient in a
hypothetical repeated-index transition. -/
theorem
  AreConsecutiveBest.errorQuadrance_lower_lt_four_mul_upper_of_index_two
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper)
    (indexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper = 2) :
    Best.Error.errorQuadrance source.value lower <
      4 * Best.Error.errorQuadrance source.value upper := by
  have errorOrdered :
      Best.Error.errorQuadrance source.value upper <
        Best.Error.errorQuadrance source.value lower :=
    consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1
  have denominatorOrdered :
      Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian lower.denominator) <
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) := by
    rw [GaussianInt.normSq_toGaussian, GaussianInt.normSq_toGaussian]
    exact Fraction.Cast.Order.natCast_lt_direct consecutive.2.2.1
  have translatedObstruction
      (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
      (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value lower ≤
          Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value upper -
            GaussianInt.toGaussian unit * Best.Error.error source.value lower) ∨
        (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) ≤
          Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
    rcases (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfObstruction consecutive) indexTwo unit
      unitNorm with
      errorExterior | denominatorExterior
    · left
      have combinationError :
          Best.Error.error source.value
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) =
            Best.Error.error source.value upper -
              GaussianInt.toGaussian unit * Best.Error.error source.value lower := by
        rw [Best.Error.error_linearCombination]
        apply Gaussian.Basic.ext <;>
          simp only [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
            Gaussian.Basic.neg_re,
            Gaussian.Basic.neg_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
          ring1
      simpa only [Best.Error.errorQuadrance, combinationError, -eq_self, -iff_self] using errorExterior
    · right
      have castExterior :=
        Fraction.Cast.Order.natCast_le_direct denominatorExterior
      have denominatorIdentity :
          GaussianInt.toGaussian
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1).denominator =
            GaussianInt.toGaussian upper.denominator -
              GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator := by
        apply Gaussian.Basic.ext <;>
          simp only [GaussianInt.Pair.LinearCombination.linearCombination, GaussianInt.toGaussian_add,
            GaussianInt.toGaussian_mul,
            GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
            Gaussian.Basic.neg_re,
            Gaussian.Basic.neg_im,
            Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
            Gaussian.Basic.add_re,
            Gaussian.Basic.add_im,
            Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
            Gaussian.Basic.one_re,
            Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
          ring1
      calc
        (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) =
            ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational) := by
          rw [GaussianInt.normSq_toGaussian]
          change (2 : Fraction.Rational) *
              (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
            ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational)
          rw [Algebra.NatCast.mul, Nat.cast_ofNat]
        _ ≤
            (Best.Error.denominatorQuadrance
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1) : Fraction.Rational) :=
          castExterior
        _ = Data.Gaussian.Norm.Basic.normSq
            (GaussianInt.toGaussian
              (GaussianInt.Pair.LinearCombination.linearCombination lower upper (-unit) 1).denominator) :=
          (GaussianInt.normSq_toGaussian _).symm
        _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator -
            GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
          rw [denominatorIdentity]
  have positiveOneObstruction := translatedObstruction 1 rfl
  have negativeOneObstruction := translatedObstruction (-1) (by decide)
  have positiveImaginaryObstruction :=
    translatedObstruction GaussianInt.Norm.Small.imaginaryUnit (by decide)
  have negativeImaginaryObstruction :=
    translatedObstruction (-GaussianInt.Norm.Small.imaginaryUnit) (by decide)
  exact four_unit_obstructions_force_error_lt_four_mul
    (Best.Error.error source.value lower) (Best.Error.error source.value upper)
    (GaussianInt.toGaussian lower.denominator) (GaussianInt.toGaussian upper.denominator)
    errorOrdered denominatorOrdered positiveOneObstruction
      negativeOneObstruction positiveImaginaryObstruction
      negativeImaginaryObstruction

/-- Constructive finite counterpart of the coefficient bound in Chevallier's
repeated-index lemma.  In the fully witnessed normal form, the nonzero
Gaussian step has quadrance at most four.  The proof combines the four-unit
error-ratio bound with one exact two-coordinate Cauchy calculation. -/
theorem
  AreConsecutiveBest.repeatedIndexTwo_boundedNormalForm
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      GaussianInt.normNat lowerUnit = 1 ∧ step ≠ 0 ∧ GaussianInt.normNat step ≤ 4 ∧
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerUnit
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepNonzero,
      transitionIdentity⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.repeatedIndexTwo_normalForm first) second leftIndexTwo rightIndexTwo
  have stepBound : GaussianInt.normNat step ≤ 4 := by
    apply Nat.le_of_not_gt
    intro stepGreaterThanFour
    have stepAtLeastFive : 5 ≤ GaussianInt.normNat step := by omega
    let determinantValue := GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle
    let baseValue :=
      GaussianInt.toGaussian lowerUnit * Best.Error.error source.value lower
    let multipliedValue :=
      GaussianInt.toGaussian (determinantValue * step) * Best.Error.error source.value middle
    let dotValue : Fraction.Rational :=
      multipliedValue.re * baseValue.re +
        multipliedValue.im * baseValue.im
    have determinantNorm : GaussianInt.normNat determinantValue = 2 := by
      simpa only [determinantValue, GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self]
        using leftIndexTwo
    have comparisonPositive :
        0 < Best.Error.errorQuadrance source.value middle := by
      have upperSmaller :
          Best.Error.errorQuadrance source.value upper <
            Best.Error.errorQuadrance source.value middle :=
        second.2.1.2.1 middle second.1.1 second.2.2.1
      exact (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value upper)).trans_lt upperSmaller
    have comparisonNonnegative :
        0 ≤ Best.Error.errorQuadrance source.value middle :=
      Fraction.Order.Arithmetic.le_of_lt_direct comparisonPositive
    have baseNormIdentity :
        Data.Gaussian.Norm.Basic.normSq baseValue = Best.Error.errorQuadrance source.value lower := by
      dsimp only [baseValue, Best.Error.errorQuadrance, -eq_self, -iff_self]
      rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, lowerUnitNorm]
      ring1
    have multipliedNormIdentity :
        Data.Gaussian.Norm.Basic.normSq multipliedValue =
          (2 * GaussianInt.normNat step : Nat) *
            Best.Error.errorQuadrance source.value middle := by
      dsimp only [multipliedValue, determinantValue, Best.Error.errorQuadrance, -eq_self, -iff_self]
      rw [Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian, GaussianInt.normNat_mul, determinantNorm]
    have tenLeMultiplierNormNat :
        10 ≤ 2 * GaussianInt.normNat step := by omega
    have tenComparisonLe :
        (10 : Fraction.Rational) * Best.Error.errorQuadrance source.value middle ≤
          Data.Gaussian.Norm.Basic.normSq multipliedValue := by
      have castBound :=
        Fraction.Cast.Order.natCast_le_direct tenLeMultiplierNormNat
      have scaled :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          castBound comparisonNonnegative
      rw [multipliedNormIdentity]
      exact scaled
    have baseLtFourComparison :
        Data.Gaussian.Norm.Basic.normSq baseValue <
          4 * Best.Error.errorQuadrance source.value middle := by
      rw [baseNormIdentity]
      exact (Best.Consecutive.NormalForm.AreConsecutiveBest.errorQuadrance_lower_lt_four_mul_upper_of_index_two first)
        leftIndexTwo
    have dotBound :
        dotValue ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq multipliedValue * Data.Gaussian.Norm.Basic.normSq
          baseValue := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      calc
        0 ≤
            (multipliedValue.re * baseValue.im -
              multipliedValue.im * baseValue.re) ^ 2 :=
          Fraction.Order.Arithmetic.sq_nonneg_direct _
        _ = Data.Gaussian.Norm.Basic.normSq multipliedValue * Data.Gaussian.Norm.Basic.normSq baseValue -
            dotValue ^ 2 := by
          dsimp only [dotValue, Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
          ring1
    have errorTransition :
        Best.Error.error source.value upper = baseValue + multipliedValue := by
      rw [transitionIdentity, Best.Error.error_linearCombination]
    have sumExpansion :
        Best.Error.errorQuadrance source.value upper =
          Data.Gaussian.Norm.Basic.normSq multipliedValue + Data.Gaussian.Norm.Basic.normSq baseValue + 2 *
            dotValue := by
      rw [Best.Error.errorQuadrance, errorTransition]
      dsimp only [dotValue, Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
      simp only [Gaussian.Basic.add_re,
        Gaussian.Basic.add_im, -eq_self, -iff_self]
      ring1
    have upperSmaller :
        Best.Error.errorQuadrance source.value upper <
          Best.Error.errorQuadrance source.value middle :=
      second.2.1.2.1 middle second.1.1 second.2.2.1
    exact large_summand_sum_not_lt_comparison comparisonPositive
      (Gaussian.Norm.Basic.normSq_nonneg baseValue) tenComparisonLe baseLtFourComparison
      dotBound sumExpansion upperSmaller
  exact ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, stepBound,
    transitionIdentity⟩

/-- The bounded nonzero step has exactly one of the three Gaussian
quadrances `1`, `2`, or `4`.  Thus the remaining no-repeated-index argument
has only twelve displayed step values before unit symmetries are used. -/
theorem
  AreConsecutiveBest.repeatedIndexTwo_enumeratedNormalForm
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (rightIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper = 2) :
    ∃ lowerUnit step : GaussianInt,
      GaussianInt.normNat lowerUnit = 1 ∧
      (GaussianInt.normNat step = 1 ∨ GaussianInt.normNat step = 2 ∨ GaussianInt.normNat step = 4) ∧
      upper = GaussianInt.Pair.LinearCombination.linearCombination lower middle lowerUnit
        (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle * step) := by
  obtain ⟨lowerUnit, step, lowerUnitNorm, stepNonzero, stepBound,
      transitionIdentity⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.repeatedIndexTwo_boundedNormalForm first) second leftIndexTwo
      rightIndexTwo
  have stepCases :=
    GaussianInt.Norm.Small.normNat_eq_one_or_two_or_four_of_nonzero_of_le_four step stepNonzero
      stepBound
  exact ⟨lowerUnit, step, lowerUnitNorm, stepCases, transitionIdentity⟩

open Purelib.NumberTheory in
/-- The only boundary pattern left by the diagonal centered-unit case cannot
occur over the displayed rationals.  Its four inequalities pin the real and
imaginary coordinates to opposite halves of `quadrance - 1`; substituting
back into the quadrance identity would give a rational square root of three.

This lemma records that final arithmetic obstruction independently of the
finite cylinder case table which produces the four hypotheses. -/
theorem centered_diagonal_boundary_impossible
    (realPart imaginaryPart : Fraction.Rational) :
    let quadrance := realPart ^ 2 + imaginaryPart ^ 2
    2 ≤ 1 + quadrance - 2 * realPart →
    2 * quadrance ≤ 1 + quadrance + 2 * realPart →
    2 * quadrance ≤ 1 + quadrance - 2 * imaginaryPart →
    2 ≤ 1 + quadrance + 2 * imaginaryPart →
    False := by
  dsimp only
  let quadrance := realPart ^ 2 + imaginaryPart ^ 2
  intro positiveOneSelf negativeOneNext positiveImaginaryNext
    negativeImaginarySelf
  have realUpper : 2 * realPart ≤ quadrance - 1 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * realPart) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct positiveOneSelf
      _ = (quadrance - 1) - 2 * realPart := by ring1
  have realLower : quadrance - 1 ≤ 2 * realPart := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * realPart) - 2 * quadrance :=
        Fraction.Order.Arithmetic.sub_nonneg_direct negativeOneNext
      _ = 2 * realPart - (quadrance - 1) := by ring1
  have realIdentity : 2 * realPart = quadrance - 1 :=
    le_antisymm realUpper realLower
  have imaginaryUpper : 2 * imaginaryPart ≤ 1 - quadrance := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance - 2 * imaginaryPart) - 2 * quadrance :=
        Fraction.Order.Arithmetic.sub_nonneg_direct positiveImaginaryNext
      _ = (1 - quadrance) - 2 * imaginaryPart := by ring1
  have imaginaryLower : 1 - quadrance ≤ 2 * imaginaryPart := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 + quadrance + 2 * imaginaryPart) - 2 :=
        Fraction.Order.Arithmetic.sub_nonneg_direct negativeImaginarySelf
      _ = 2 * imaginaryPart - (1 - quadrance) := by ring1
  have imaginaryIdentity : 2 * imaginaryPart = 1 - quadrance :=
    le_antisymm imaginaryUpper imaginaryLower
  have scaledQuadrance :
      2 * (2 * quadrance) = 2 * (quadrance - 1) ^ 2 := by
    calc
      2 * (2 * quadrance) =
          (2 * realPart) ^ 2 + (2 * imaginaryPart) ^ 2 := by
        dsimp only [quadrance, -eq_self, -iff_self]
        ring1
      _ = (quadrance - 1) ^ 2 + (1 - quadrance) ^ 2 := by
        rw [realIdentity, imaginaryIdentity]
      _ = 2 * (quadrance - 1) ^ 2 := by ring1
  have quadranceIdentity :
      2 * quadrance = (quadrance - 1) ^ 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (2 : Fraction.Rational) ≠ 0 by decide)
    simpa only [Fraction.Field.mul_comm, -eq_self, -iff_self] using scaledQuadrance
  have forbiddenSquare : (quadrance - 2) ^ 2 = (3 : Fraction.Rational) := by
    calc
      (quadrance - 2) ^ 2 =
          (quadrance - 1) ^ 2 - 2 * quadrance + 3 := by ring1
      _ = 3 := by rw [← quadranceIdentity]; ring1
  exact SquareClass.Rational.Nonsquare.square_ne_three
    (quadrance - 2) forbiddenSquare

/-- Homogeneous form of `centered_diagonal_boundary_impossible`.  Two
opposite self-cylinder error exteriors and the two interleaved next-cylinder
error exteriors force the same forbidden rational boundary, without first
naming a complex quotient. -/
theorem centered_diagonal_error_pattern_impossible
    (largeError smallError : Gaussian.Basic.Canonical) (largeNonzero : largeError ≠ 0)
    (positiveOneSelf :
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq largeError ≤
        Data.Gaussian.Norm.Basic.normSq (smallError - largeError))
    (negativeOneNext :
      2 * Data.Gaussian.Norm.Basic.normSq smallError ≤ Data.Gaussian.Norm.Basic.normSq (smallError +
        largeError))
    (positiveImaginaryNext :
      2 * Data.Gaussian.Norm.Basic.normSq smallError ≤
        Data.Gaussian.Norm.Basic.normSq (smallError -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError))
    (negativeImaginarySelf :
      2 * Data.Gaussian.Norm.Basic.normSq largeError ≤
        Data.Gaussian.Norm.Basic.normSq (smallError +
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError)) :
    False := open Purelib.NumberTheory in by
  let largeNorm := Data.Gaussian.Norm.Basic.normSq largeError
  let smallNorm := Data.Gaussian.Norm.Basic.normSq smallError
  let realProjection :=
    smallError.re * largeError.re + smallError.im * largeError.im
  let imaginaryProjection :=
    -smallError.re * largeError.im + smallError.im * largeError.re
  have positiveOneExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError - largeError) =
        smallNorm + largeNorm - 2 * realProjection := by
    dsimp only [smallNorm, largeNorm, realProjection, Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, -eq_self, -iff_self]
    ring1
  have negativeOneExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError + largeError) =
        smallNorm + largeNorm + 2 * realProjection := by
    dsimp only [smallNorm, largeNorm, realProjection, Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im, -eq_self, -iff_self]
    ring1
  have positiveImaginaryExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError) =
        smallNorm + largeNorm - 2 * imaginaryProjection := by
    dsimp only [smallNorm, largeNorm, imaginaryProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
      GaussianInt.Norm.Small.imaginaryUnit, -eq_self, -iff_self]
    simp only [Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  have negativeImaginaryExpansion :
      Data.Gaussian.Norm.Basic.normSq (smallError +
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit * largeError) =
        smallNorm + largeNorm + 2 * imaginaryProjection := by
    dsimp only [smallNorm, largeNorm, imaginaryProjection, Data.Gaussian.Norm.Basic.normSq, GaussianInt.toGaussian,
      GaussianInt.Norm.Small.imaginaryUnit, -eq_self, -iff_self]
    simp only [Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im, -eq_self, -iff_self]
    simp only [-eq_self, -iff_self, ← Rat.Fraction.Cast.intCast_eq_fromInt]
    ring1
  rw [positiveOneExpansion] at positiveOneSelf
  rw [negativeOneExpansion] at negativeOneNext
  rw [positiveImaginaryExpansion] at positiveImaginaryNext
  rw [negativeImaginaryExpansion] at negativeImaginarySelf
  have realUpper : 2 * realProjection ≤ smallNorm - largeNorm := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (smallNorm + largeNorm - 2 * realProjection) - 2 * largeNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct positiveOneSelf
      _ = (smallNorm - largeNorm) - 2 * realProjection := by ring1
  have realLower : smallNorm - largeNorm ≤ 2 * realProjection := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (smallNorm + largeNorm + 2 * realProjection) - 2 * smallNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct negativeOneNext
      _ = 2 * realProjection - (smallNorm - largeNorm) := by ring1
  have realIdentity :
      2 * realProjection = smallNorm - largeNorm :=
    le_antisymm realUpper realLower
  have imaginaryUpper :
      2 * imaginaryProjection ≤ largeNorm - smallNorm := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (smallNorm + largeNorm - 2 * imaginaryProjection) -
            2 * smallNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct positiveImaginaryNext
      _ = (largeNorm - smallNorm) - 2 * imaginaryProjection := by ring1
  have imaginaryLower :
      largeNorm - smallNorm ≤ 2 * imaginaryProjection := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤
          (smallNorm + largeNorm + 2 * imaginaryProjection) -
            2 * largeNorm :=
        Fraction.Order.Arithmetic.sub_nonneg_direct negativeImaginarySelf
      _ = 2 * imaginaryProjection - (largeNorm - smallNorm) := by ring1
  have imaginaryIdentity :
      2 * imaginaryProjection = largeNorm - smallNorm :=
    le_antisymm imaginaryUpper imaginaryLower
  have projectionSquares :
      realProjection ^ 2 + imaginaryProjection ^ 2 =
        smallNorm * largeNorm := by
    dsimp only [realProjection, imaginaryProjection, smallNorm, largeNorm,
      Data.Gaussian.Norm.Basic.normSq, -eq_self, -iff_self]
    ring1
  have scaledProjectionIdentity :
      2 * (2 * (smallNorm * largeNorm)) =
        2 * (smallNorm - largeNorm) ^ 2 := by
    calc
      2 * (2 * (smallNorm * largeNorm)) =
          2 * (2 *
            (realProjection ^ 2 + imaginaryProjection ^ 2)) := by
        rw [projectionSquares]
      _ = (2 * realProjection) ^ 2 +
          (2 * imaginaryProjection) ^ 2 := by ring1
      _ = (smallNorm - largeNorm) ^ 2 +
          (largeNorm - smallNorm) ^ 2 := by
        rw [realIdentity, imaginaryIdentity]
      _ = 2 * (smallNorm - largeNorm) ^ 2 := by ring1
  have productIdentity :
      2 * (smallNorm * largeNorm) =
        (smallNorm - largeNorm) ^ 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (2 : Fraction.Rational) ≠ 0 by decide)
    simpa only [Fraction.Field.mul_comm, -eq_self, -iff_self] using
      scaledProjectionIdentity
  have homogeneousSquare :
      (smallNorm - 2 * largeNorm) ^ 2 = 3 * largeNorm ^ 2 := by
    calc
      (smallNorm - 2 * largeNorm) ^ 2 =
          (smallNorm - largeNorm) ^ 2 -
            2 * (smallNorm * largeNorm) + 3 * largeNorm ^ 2 := by ring1
      _ = 3 * largeNorm ^ 2 := by rw [← productIdentity]; ring1
  have largeNormPositive : 0 < largeNorm := by
    dsimp only [largeNorm, -eq_self, -iff_self]
    exact Gaussian.Norm.Basic.normSq_pos largeNonzero
  have largeNormNonzero : largeNorm ≠ 0 := ne_of_gt largeNormPositive
  let forbiddenRoot : Fraction.Rational :=
    (smallNorm - 2 * largeNorm) * largeNorm⁻¹
  have forbiddenSquare : forbiddenRoot ^ 2 = (3 : Fraction.Rational) := by
    dsimp only [forbiddenRoot, -eq_self, -iff_self]
    rw [pow_two]
    calc
      ((smallNorm - 2 * largeNorm) * largeNorm⁻¹) *
          ((smallNorm - 2 * largeNorm) * largeNorm⁻¹) =
          ((smallNorm - 2 * largeNorm) *
              (smallNorm - 2 * largeNorm)) *
            (largeNorm⁻¹ * largeNorm⁻¹) :=
        Fraction.Field.mul_pair_swap _ _ _ _
      _ = (3 * (largeNorm * largeNorm)) *
          (largeNorm⁻¹ * largeNorm⁻¹) := by
        rw [← pow_two, homogeneousSquare, pow_two]
      _ = 3 * ((largeNorm * largeNorm) *
          (largeNorm⁻¹ * largeNorm⁻¹)) :=
        Fraction.Field.mul_assoc _ _ _
      _ = 3 * ((largeNorm * largeNorm⁻¹) *
          (largeNorm * largeNorm⁻¹)) := by
        rw [Fraction.Field.mul_pair_swap largeNorm largeNorm
          largeNorm⁻¹ largeNorm⁻¹]
      _ = 3 := by
        rw [Fraction.Field.mul_inv_cancel largeNorm
          largeNormNonzero]
        ring1
  exact SquareClass.Rational.Nonsquare.square_ne_three forbiddenRoot
    forbiddenSquare

/-- Eliminating the centered candidate gives a finite, square-root-free
obstruction for each of the four Gaussian units.  Either the scaled
half-difference misses the next cylinder through its error coordinate, or it
misses through its denominator coordinate. -/
theorem
  AreConsecutiveBest.centeredUnit_obstruction
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value middle ≤
        Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1) ∨
      2 * Best.Error.denominatorQuadrance upper ≤
        Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1) := by
  obtain ⟨candidate, _, centeredIdentity, outside⟩ :=
    (Best.Consecutive.NormalForm.AreConsecutiveBest.exists_centeredUnitCandidate_outside_nextCylinder first) second
      leftIndexTwo unit unitNorm
  have determinantNorm :
      GaussianInt.normNat (GaussianInt.Pair.LinearCombination.coefficientDeterminant lower middle) = 2 := by
    simpa only [GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance, -eq_self, -iff_self] using leftIndexTwo
  have errorIdentity :=
    congrArg (Best.Error.errorQuadrance source.value) centeredIdentity
  rw [Best.Error.errorQuadrance_scalePair, determinantNorm] at errorIdentity
  have denominatorIdentity :=
    congrArg Best.Error.denominatorQuadrance centeredIdentity
  rw [Best.Error.denominatorQuadrance_scalePair, determinantNorm] at denominatorIdentity
  by_cases errorInside :
      Best.Error.errorQuadrance source.value candidate <
        Best.Error.errorQuadrance source.value middle
  · have denominatorNotInside :
        ¬ Best.Error.denominatorQuadrance candidate < Best.Error.denominatorQuadrance upper := by
      intro denominatorInside
      exact outside ⟨errorInside, denominatorInside⟩
    right
    calc
      2 * Best.Error.denominatorQuadrance upper ≤
          2 * Best.Error.denominatorQuadrance candidate :=
        Nat.mul_le_mul_left 2 (Nat.le_of_not_gt denominatorNotInside)
      _ = Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1) := denominatorIdentity
  · have errorOutside :
        Best.Error.errorQuadrance source.value middle ≤
          Best.Error.errorQuadrance source.value candidate :=
      le_of_not_gt errorInside
    left
    calc
      (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value middle ≤
          (2 : Fraction.Rational) * Best.Error.errorQuadrance source.value candidate :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorOutside (by decide)
      _ = Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1) := errorIdentity

/-- The next-cylinder obstruction in geometric coordinate form. -/
theorem
  AreConsecutiveBest.centeredUnit_nextCoordinateObstruction
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2)
    (unit : GaussianInt) (unitNorm : GaussianInt.normNat unit = 1) :
    (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value middle) ≤
        Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value middle -
          GaussianInt.toGaussian unit * Best.Error.error source.value lower) ∨
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
  rcases (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_obstruction first) second leftIndexTwo unit
    unitNorm with
    errorExterior | denominatorExterior
  · left
    rw [← Best.Error.error_linearCombination_negUnit_one]
    exact errorExterior
  · right
    have castExterior :=
      Fraction.Cast.Order.natCast_le_direct denominatorExterior
    calc
      (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) =
          ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational) := by
        rw [GaussianInt.normSq_toGaussian]
        change (2 : Fraction.Rational) *
            (Best.Error.denominatorQuadrance upper : Fraction.Rational) =
          ((2 * Best.Error.denominatorQuadrance upper : Nat) : Fraction.Rational)
        rw [Algebra.NatCast.mul, Nat.cast_ofNat]
      _ ≤
          (Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1) : Fraction.Rational) :=
        castExterior
      _ = Data.Gaussian.Norm.Basic.normSq
          (GaussianInt.toGaussian
            (GaussianInt.Pair.LinearCombination.linearCombination lower middle (-unit) 1).denominator) :=
        (GaussianInt.normSq_toGaussian _).symm
      _ = Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian unit * GaussianInt.toGaussian lower.denominator) := by
        rw [Best.Error.toGaussian_denominator_linearCombination_negUnit_one]

/-- The four interleaved centered-unit tests cannot all escape through their
error coordinates.  Consequently at least one of the displayed denominator
exteriors is forced.  This removes the sole diagonal boundary pattern left
by the real polynomial relaxation before the remaining denominator cases
are considered. -/
theorem
  AreConsecutiveBest.centeredDiagonal_forces_denominator_obstruction
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (leftIndexTwo : GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle = 2) :
    ((2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian (1 : GaussianInt) * GaussianInt.toGaussian lower.denominator)) ∨
      ((2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian (-1 : GaussianInt) * GaussianInt.toGaussian lower.denominator)) ∨
      ((2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian upper.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
            GaussianInt.toGaussian lower.denominator)) ∨
      ((2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator) ≤
        Data.Gaussian.Norm.Basic.normSq (GaussianInt.toGaussian middle.denominator -
          GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) *
            GaussianInt.toGaussian lower.denominator)) := by
  have positiveOne := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfCoordinateObstruction first)
    leftIndexTwo 1 rfl
  have negativeOne := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_nextCoordinateObstruction first)
    second
    leftIndexTwo (-1) (by decide)
  have positiveImaginary := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_nextCoordinateObstruction
    first)
    second leftIndexTwo GaussianInt.Norm.Small.imaginaryUnit (by decide)
  have negativeImaginary := (Best.Consecutive.NormalForm.AreConsecutiveBest.centeredUnit_selfCoordinateObstruction
    first)
    leftIndexTwo (-GaussianInt.Norm.Small.imaginaryUnit) (by decide)
  rcases positiveOne with positiveOneError | positiveOneDenominator
  · rcases negativeOne with negativeOneError | negativeOneDenominator
    · rcases positiveImaginary with
        positiveImaginaryError | positiveImaginaryDenominator
      · rcases negativeImaginary with
          negativeImaginaryError | negativeImaginaryDenominator
        · have errorOrdered :
              Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value middle) <
                Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) :=
            first.2.1.2.1 lower first.1.1 first.2.2.1
          have largeNonzero : Best.Error.error source.value lower ≠ 0 := by
            intro errorZero
            have lowerNormZero := congrArg Data.Gaussian.Norm.Basic.normSq errorZero
            rw [Gaussian.Norm.Basic.normSq_zero] at lowerNormZero
            have middleNonnegative := Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source.value middle)
            rw [lowerNormZero] at errorOrdered
            exact (not_lt_of_ge middleNonnegative) errorOrdered
          have negativeOneIdentity :
              Best.Error.error source.value middle -
                  GaussianInt.toGaussian (-1 : GaussianInt) * Best.Error.error source.value lower =
                Best.Error.error source.value middle + Best.Error.error source.value lower := by
            apply Gaussian.Basic.ext <;>
              simp only [GaussianInt.toGaussian_neg, GaussianInt.toGaussian_one,
                Gaussian.Basic.neg_re,
                Gaussian.Basic.neg_im,
                Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.add_re,
                Gaussian.Basic.add_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im,
                Gaussian.Basic.one_re,
                Gaussian.Basic.one_im, -eq_self, -iff_self] <;>
              ring1
          have negativeImaginaryIdentity :
              Best.Error.error source.value middle -
                  GaussianInt.toGaussian (-GaussianInt.Norm.Small.imaginaryUnit) *
                    Best.Error.error source.value lower =
                Best.Error.error source.value middle +
                  GaussianInt.toGaussian GaussianInt.Norm.Small.imaginaryUnit *
                    Best.Error.error source.value lower := by
            apply Gaussian.Basic.ext <;>
              simp only [GaussianInt.toGaussian_neg,
                Gaussian.Basic.neg_re,
                Gaussian.Basic.neg_im,
                Gaussian.Basic.sub_re,
                Gaussian.Basic.sub_im,
                Gaussian.Basic.add_re,
                Gaussian.Basic.add_im,
                Gaussian.Basic.mul_re,
                Gaussian.Basic.mul_im, -eq_self, -iff_self] <;>
              ring1
          rw [negativeOneIdentity] at negativeOneError
          rw [negativeImaginaryIdentity] at negativeImaginaryError
          have positiveOneError' :
              (2 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value lower) ≤
                Data.Gaussian.Norm.Basic.normSq (Best.Error.error source.value middle -
                  Best.Error.error source.value lower) := by
            simpa only [GaussianInt.toGaussian_one,
              Gaussian.Basic.one_mul, -eq_self, -iff_self] using
              positiveOneError
          exact (centered_diagonal_error_pattern_impossible
            (Best.Error.error source.value lower) (Best.Error.error source.value middle)
            largeNonzero positiveOneError' negativeOneError
            positiveImaginaryError negativeImaginaryError).elim
        · exact Or.inr (Or.inr (Or.inr negativeImaginaryDenominator))
      · exact Or.inr (Or.inr (Or.inl positiveImaginaryDenominator))
    · exact Or.inr (Or.inl negativeOneDenominator)
  · exact Or.inl positiveOneDenominator

/-- The empty-cylinder criterion excludes every nontrivial displayed integral
linear combination of two consecutive best pairs from the mixed interior. -/
theorem
  AreConsecutiveBest.linearCombination_not_in_mixedCylinder
    {source : GaussianInt.Fraction} {left right : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    ¬ Best.Consecutive.Basic.InOpenMixedCylinder source.value left right
      (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) := by
  have cylinderEmpty :=
    (Best.Consecutive.Basic.areConsecutiveBest_iff_mixedCylinderEmpty source left right).mp consecutive
      |>.2.2.2
  exact cylinderEmpty _
    ((Best.Consecutive.NormalForm.AreConsecutiveBest.linearCombination_pairNonzero consecutive) leftCoefficient
      rightCoefficient
      coefficientNonzero)

/-- Square-root-free exterior alternative for every nontrivial integral
combination: either its error reaches the lower boundary or its denominator
reaches the upper boundary. -/
theorem
  AreConsecutiveBest.linearCombination_outside_mixedCylinder
    {source : GaussianInt.Fraction} {left right : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value left right)
    (leftCoefficient rightCoefficient : GaussianInt)
    (coefficientNonzero :
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0) :
    Best.Error.errorQuadrance source.value left ≤
        Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) ∨
      Best.Error.denominatorQuadrance right ≤
        Best.Error.denominatorQuadrance
          (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) := by
  by_cases errorInside :
      Best.Error.errorQuadrance source.value
          (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) <
        Best.Error.errorQuadrance source.value left
  · by_cases denominatorInside :
        Best.Error.denominatorQuadrance
            (GaussianInt.Pair.LinearCombination.linearCombination left right leftCoefficient rightCoefficient) <
          Best.Error.denominatorQuadrance right
    · exact ((Best.Consecutive.NormalForm.AreConsecutiveBest.linearCombination_not_in_mixedCylinder consecutive)
        leftCoefficient rightCoefficient coefficientNonzero
        ⟨errorInside, denominatorInside⟩).elim
    · exact Or.inr (Nat.le_of_not_gt denominatorInside)
  · exact Or.inl (le_of_not_gt errorInside)

/-- A source-computed finite bound for the coefficient-index quadrance of any
two consecutive best pairs.  The much sharper universal values `1` and `2`
require the local geometry-of-numbers argument; this bound uses only the
already verified global candidate rectangle. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_le_sourceBound
    {source : GaussianInt.Fraction} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper ≤
      4 * Best.Search.numeratorQuadranceBound source * GaussianInt.normNat source.denominator := by
  have lowerNumeratorBound := Best.Search.numeratorQuadrance_le_bound
    (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.1)
    consecutive.1.errorQuadrance_le_half
  have upperNumeratorBound := Best.Search.numeratorQuadrance_le_bound
    (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.2.1)
    consecutive.2.1.errorQuadrance_le_half
  have lowerDenominatorBound := (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.1)
  have upperDenominatorBound :=
    (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.2.1)
  calc
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper =
        GaussianInt.normNat
          (lower.numerator * upper.denominator -
            upper.numerator * lower.denominator) := rfl
    _ ≤ 2 *
        (GaussianInt.normNat (lower.numerator * upper.denominator) +
          GaussianInt.normNat (upper.numerator * lower.denominator)) :=
      by
        have bound := GaussianInt.Norm.Bounds.normNat_add_le_two
          (lower.numerator * upper.denominator) (-(upper.numerator * lower.denominator))
        rw [← GaussianInt.sub_eq_add_neg, GaussianInt.normNat_neg] at bound
        exact bound
    _ = 2 *
        (GaussianInt.normNat lower.numerator * GaussianInt.normNat upper.denominator +
          GaussianInt.normNat upper.numerator * GaussianInt.normNat lower.denominator) := by
      rw [GaussianInt.normNat_mul, GaussianInt.normNat_mul]
    _ ≤ 2 *
        (Best.Search.numeratorQuadranceBound source * GaussianInt.normNat source.denominator +
          Best.Search.numeratorQuadranceBound source * GaussianInt.normNat source.denominator) := by
      exact Nat.mul_le_mul_left 2
        (Nat.add_le_add
          (Nat.mul_le_mul lowerNumeratorBound upperDenominatorBound)
          (Nat.mul_le_mul upperNumeratorBound lowerDenominatorBound))
    _ = 4 * Best.Search.numeratorQuadranceBound source *
        GaussianInt.normNat source.denominator := by ring1
end Purelib.NumberTheory.Approximation.Best.Consecutive.NormalForm

end
