module
import Purelib.Algebra.Group.Basic
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.NumberTheory.Approximation.Best.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Best.Search

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section

/-!
# Consecutive Gaussian approximation heights

Best pairs retain their exact error and denominator comparisons. Consecutive
heights have no intervening best pair; the empty mixed cylinder characterizes
that adjacency and certifies the nonzero coefficient determinant.
-/

namespace Purelib.NumberTheory.Approximation.Best.Consecutive.Basic

/-! ## Consecutive minimal-vector levels -/

/-- Two best pairs are consecutive when their denominator quadrances are
strictly ordered and no best pair occurs at an intermediate quadrance.  Unit
associates and other ties at either endpoint belong to the same height level. -/
@[expose] def AreConsecutiveBest (source :
  Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Basic.IsBest source lower ∧ Best.Basic.IsBest source upper ∧
    Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper ∧
    ∀ middle : GaussianInt.Pair.Basic.ConvergentPair, Best.Basic.IsBest source middle →
      ¬ (Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance middle ∧
        Best.Error.denominatorQuadrance middle < Best.Error.denominatorQuadrance upper)

/-- The mixed open cylinder determined by a lower best error and an upper
best denominator. -/
@[expose] def InOpenMixedCylinder
    (source : Gaussian.Basic.Canonical) (lower upper candidate : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  Best.Error.errorQuadrance source candidate < Best.Error.errorQuadrance source lower ∧
    Best.Error.denominatorQuadrance candidate < Best.Error.denominatorQuadrance upper

/-- No nonzero displayed source-lattice vector lies in the mixed open
cylinder between two supplied pairs. -/
@[expose] def MixedCylinderEmpty (source :
  Gaussian.Basic.Canonical) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) : Prop :=
  ∀ candidate : GaussianInt.Pair.Basic.ConvergentPair, GaussianInt.Pair.LinearCombination.PairNonzero candidate →
    ¬ InOpenMixedCylinder source lower upper candidate

/-- For displayed rational sources, the global definition by consecutive
best levels is equivalent to the local empty-open-cylinder criterion.  The
forward direction uses the executable finite descent to a best pair rather
than selecting a minimum from an infinite lattice. -/
theorem areConsecutiveBest_iff_mixedCylinderEmpty
    (source : GaussianInt.Fraction) (lower upper : GaussianInt.Pair.Basic.ConvergentPair) :
    AreConsecutiveBest source.value lower upper ↔
      Best.Basic.IsBest source.value lower ∧ Best.Basic.IsBest source.value upper ∧
        Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper ∧
        MixedCylinderEmpty source.value lower upper := by
  constructor
  · intro consecutive
    refine ⟨consecutive.1, consecutive.2.1, consecutive.2.2.1, ?_⟩
    intro candidate candidateNonzero inside
    by_cases candidateDenominatorNonzero : candidate.denominator ≠ 0
    · have candidateDenominatorBound :
          Best.Error.denominatorQuadrance candidate ≤ GaussianInt.normNat source.denominator :=
        inside.2.le.trans
          (Best.Search.IsBest.denominatorQuadrance_le_source consecutive.2.1)
      have candidateSmall :
          Best.Error.errorQuadrance source.value candidate ≤ 1 / 2 :=
        inside.1.le.trans consecutive.1.errorQuadrance_le_half
      obtain ⟨selected, selectedBest, selectedDenominatorLe,
          selectedErrorLe⟩ :=
        Best.Search.exists_best_below_of_small candidateDenominatorNonzero
          candidateDenominatorBound candidateSmall
      have lowerLtSelected :
          Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance selected := by
        apply Nat.lt_of_not_ge
        intro selectedNoHigher
        have lowerErrorLeSelected := consecutive.1.2.2 selected
          selectedBest.1 selectedNoHigher
        exact (not_lt_of_ge
          (lowerErrorLeSelected.trans selectedErrorLe)) inside.1
      have selectedLtUpper :
          Best.Error.denominatorQuadrance selected < Best.Error.denominatorQuadrance upper :=
        selectedDenominatorLe.trans_lt inside.2
      exact consecutive.2.2.2 selected selectedBest
        ⟨lowerLtSelected, selectedLtUpper⟩
    · have denominatorZero : candidate.denominator = 0 := by
        by_cases zero : candidate.denominator = 0
        · exact zero
        · exact (candidateDenominatorNonzero zero).elim
      have numeratorNonzero : candidate.numerator ≠ 0 := by
        rcases candidateNonzero with numeratorNonzero | impossible
        · exact numeratorNonzero
        · exact (impossible denominatorZero).elim
      have oneLeCandidate := Best.Basic.one_le_errorQuadrance_of_vertical source.value
        numeratorNonzero denominatorZero
      have impossible : (1 : Fraction.Rational) ≤ 1 / 2 :=
        oneLeCandidate.trans
          (inside.1.le.trans consecutive.1.errorQuadrance_le_half)
      exact ((show ¬ ((1 : Fraction.Rational) ≤ 1 / 2) by decide) impossible).elim
  · intro localData
    refine ⟨localData.1, localData.2.1, localData.2.2.1, ?_⟩
    intro middle middleBest between
    apply localData.2.2.2 middle (Or.inr middleBest.1)
    exact ⟨middleBest.2.1 lower localData.1.1 between.1, between.2⟩

/-- Best pairs at strictly different denominator levels are coefficientwise
independent.  This is the constructive part of the usual statement that two
consecutive minimal vectors span a finite-index sublattice. -/
theorem determinant_ne_zero_of_ordered_best
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (lowerBest : Best.Basic.IsBest source lower) (upperBest : Best.Basic.IsBest source upper)
    (denominatorOrdered :
      Best.Error.denominatorQuadrance lower < Best.Error.denominatorQuadrance upper) :
    GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper ≠ 0 := by
  intro determinantZero
  have determinantIdentity :=
    Best.Error.toGaussian_coefficientDeterminant source lower upper
  rw [determinantZero, GaussianInt.toGaussian_zero] at determinantIdentity
  have productIdentity :
      GaussianInt.toGaussian lower.denominator * Best.Error.error source upper =
        GaussianInt.toGaussian upper.denominator * Best.Error.error source lower := by
    apply Gaussian.Basic.ext
    · have coordinateIdentity := congrArg
        Gaussian.Basic.re determinantIdentity
      simp only [Gaussian.Basic.zero_re,
        Gaussian.Basic.sub_re, -eq_self, -iff_self] at coordinateIdentity
      exact Algebra.Group.eq_of_sub_eq_zero coordinateIdentity.symm
    · have coordinateIdentity := congrArg
        Gaussian.Basic.im determinantIdentity
      simp only [Gaussian.Basic.zero_im,
        Gaussian.Basic.sub_im, -eq_self, -iff_self] at coordinateIdentity
      exact Algebra.Group.eq_of_sub_eq_zero coordinateIdentity.symm
  have quadranceIdentity := congrArg Data.Gaussian.Norm.Basic.normSq productIdentity
  rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul, GaussianInt.normSq_toGaussian,
    GaussianInt.normSq_toGaussian]
      at quadranceIdentity
  have upperErrorSmaller :
      Best.Error.errorQuadrance source upper < Best.Error.errorQuadrance source lower :=
    upperBest.2.1 lower lowerBest.1 denominatorOrdered
  have lowerDenominatorPositive :
      (0 : Fraction.Rational) < (Best.Error.denominatorQuadrance lower : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_lt_direct
      (GaussianInt.normNat_pos lowerBest.1)
  have errorScaledStrict :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
          Best.Error.errorQuadrance source upper <
        (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
          Best.Error.errorQuadrance source lower :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      lowerDenominatorPositive upperErrorSmaller
  have denominatorCastBound :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) ≤
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct denominatorOrdered.le
  have denominatorScaledBound :
      (Best.Error.denominatorQuadrance lower : Fraction.Rational) *
          Best.Error.errorQuadrance source lower ≤
        (Best.Error.denominatorQuadrance upper : Fraction.Rational) *
          Best.Error.errorQuadrance source lower :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      denominatorCastBound (Gaussian.Norm.Basic.normSq_nonneg (Best.Error.error source lower))
  have productStrict := errorScaledStrict.trans_le denominatorScaledBound
  exact (ne_of_lt productStrict) quadranceIdentity

/-- Consecutive best pairs have nonzero coefficient determinant. -/
theorem
  AreConsecutiveBest.coefficientDeterminant_ne_zero
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : AreConsecutiveBest source lower upper) :
    GaussianInt.Pair.LinearCombination.coefficientDeterminant lower upper ≠ 0 :=
  determinant_ne_zero_of_ordered_best consecutive.1 consecutive.2.1
    consecutive.2.2.1

/-- Consecutive best pairs have a positive displayed coefficient-index
quadrance. -/
theorem
  AreConsecutiveBest.coefficientIndexQuadrance_pos
    {source : Gaussian.Basic.Canonical} {lower upper : GaussianInt.Pair.Basic.ConvergentPair}
    (consecutive : AreConsecutiveBest source lower upper) :
    0 < GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower upper :=
  GaussianInt.normNat_pos consecutive.coefficientDeterminant_ne_zero
end Purelib.NumberTheory.Approximation.Best.Consecutive.Basic

end
