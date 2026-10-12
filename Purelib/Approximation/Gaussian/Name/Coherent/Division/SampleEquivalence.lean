module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Sample
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Approximation.Rational.Budget

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

/-- One positive lower bound shared by two independently apart denominator names. -/
def commonLower {first second :
  Coherent.CoherentNamed}
    (firstApart : Named.Apart first.name) (secondApart : Named.Apart second.name) :
    Fraction.Rational :=
  min firstApart.certificate.lowerSq secondApart.certificate.lowerSq

/-- The minimum of the two retained denominator lower squared norms is strictly positive.

Each original apartness certificate supplies its own positive squared-norm
floor. Their unchanged minimum retains a shared lower bound for both names. -/
theorem commonLower_positive {first
  second : Coherent.CoherentNamed}
    (firstApart : Named.Apart first.name) (secondApart : Named.Apart second.name) :
    0 < Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart secondApart :=
  Fraction.Order.Basic.lt_min firstApart.certificate.positive secondApart.certificate.positive

/-- Sensitivity coefficient for comparing two quotients. -/
def quotientComparisonCoefficient
    (secondNumerator secondDenominator : Coherent.CoherentNamed)
    {firstDenominator : Coherent.CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name) : Fraction.Rational :=
  (2 *
      ((Sampling.approximation
          secondDenominator.name).centerBound +
        (Sampling.approximation
          secondNumerator.name).centerBound)) /
    (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart secondApart *
      Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart secondApart)

/-- The quotient comparison coefficient is nonnegative for the retained denominator apartness certificates. -/
theorem
  quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator : Coherent.CoherentNamed)
    {firstDenominator : Coherent.CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name) :
    0 <= Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
      secondNumerator secondDenominator
      firstApart secondApart := by
  unfold Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Sampling.approximation
          secondDenominator.name).centerBound_nonneg
        (Sampling.approximation
          secondNumerator.name).centerBound_nonneg))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower_positive firstApart secondApart).le
      (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower_positive firstApart secondApart).le)

/-- The operand comparison target obtained by dividing the requested quotient tolerance by one plus its retained
sensitivity coefficient. -/
def quotientComparisonTarget
    (secondNumerator secondDenominator : Coherent.CoherentNamed)
    {firstDenominator : Coherent.CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    (target : Fraction.Rational) : Fraction.Rational :=
  target / (1 + Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
    secondNumerator
    secondDenominator firstApart secondApart)

/-- A positive output tolerance gives a positive operand quotient-comparison target.

The retained quotient sensitivity is nonnegative. Adding one makes its same
original denominator positive before dividing the supplied output tolerance. -/
theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator : Coherent.CoherentNamed)
    {firstDenominator : Coherent.CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonTarget secondNumerator
      secondDenominator
      firstApart secondApart target :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient_nonnegative
        secondNumerator
        secondDenominator firstApart secondApart))

/-- The retained operand target times its sensitivity stays below the positive output tolerance.

The original sensitivity is strictly smaller than its incremented denominator.
Positive scaling and exact division rearrangement retain the same operand target. -/
theorem
  quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator : Coherent.CoherentNamed)
    {firstDenominator : Coherent.CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    {target : Fraction.Rational} (positive : 0 < target) :
    Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonTarget secondNumerator
      secondDenominator
        firstApart secondApart target *
      Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient secondNumerator
        secondDenominator
        firstApart secondApart < target := by
  let coefficient := Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
    secondNumerator
    secondDenominator firstApart secondApart
  have coefficientNonnegative : 0 <= coefficient :=
    Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient_nonnegative
      secondNumerator
      secondDenominator firstApart secondApart
  have denominatorPositive : 0 < 1 + coefficient :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide) coefficientNonnegative
  have fractionLt : coefficient / (1 + coefficient) < 1 := by
    apply (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
    calc
      coefficient = 0 + coefficient :=
        (Fraction.Field.zero_add coefficient).symm
      _ < 1 + coefficient :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct (by decide) _
      _ = 1 * (1 + coefficient) := by ring1
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    positive fractionLt
  change target / (1 + coefficient) * coefficient < target
  calc
    target / (1 + coefficient) * coefficient =
        target * (coefficient / (1 + coefficient)) := by
      rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
        Algebra.Field.ExplicitField.div_eq_mul_inv]
      ring1
    _ < target * 1 := scaled
    _ = target := Fraction.Field.mul_one_direct _

open Purelib.Data.Nat in
/-- Canonical finite quotient approximations preserve operational equality in both operands.

Each original denominator retains its own positive apartness certificate.
The same maxima synchronize numerator and denominator comparison indices,
and the original shared lower floor pays their quotient error bound. -/
def sampledQuotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      Coherent.CoherentNamed)
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    (numeratorEquivalent : Gaussian.Equivalence.NamedEquivalent firstNumerator.name
      secondNumerator.name)
    (denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent firstDenominator.name
      secondDenominator.name) :
    Gaussian.Equivalence.Equivalent
      (Sample.sampledQuotientApproximation firstNumerator firstDenominator firstApart)
      (Sample.sampledQuotientApproximation secondNumerator secondDenominator
        secondApart) where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonTarget
      secondNumerator
      secondDenominator firstApart secondApart target
    have inputPositive : 0 < inputTarget :=
      Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonTarget_positive secondNumerator
        secondDenominator
        firstApart secondApart positive
    let numeratorComparison := numeratorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let denominatorComparison := denominatorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let firstIndex := max numeratorComparison.leftIndex
      denominatorComparison.leftIndex
    let secondIndex := max numeratorComparison.rightIndex
      denominatorComparison.rightIndex
    have firstNumeratorBound : numeratorComparison.leftIndex <= firstIndex := by
      change numeratorComparison.leftIndex <= max numeratorComparison.leftIndex denominatorComparison.leftIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have firstDenominatorBound : denominatorComparison.leftIndex <= firstIndex := by
      change denominatorComparison.leftIndex <= max numeratorComparison.leftIndex denominatorComparison.leftIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have secondNumeratorBound : numeratorComparison.rightIndex <= secondIndex := by
      change numeratorComparison.rightIndex <= max numeratorComparison.rightIndex denominatorComparison.rightIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have secondDenominatorBound : denominatorComparison.rightIndex <= secondIndex := by
      change denominatorComparison.rightIndex <= max numeratorComparison.rightIndex denominatorComparison.rightIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := numeratorComparison.left_ge.trans firstNumeratorBound
        right_ge := numeratorComparison.right_ge.trans secondNumeratorBound
        close := by
          intro firstLater secondLater firstOrder secondOrder
          let firstNumeratorSource :=
            Sampling.approximation firstNumerator.name
          let secondNumeratorSource :=
            Sampling.approximation secondNumerator.name
          let firstDenominatorSource :=
            Sampling.approximation firstDenominator.name
          let secondDenominatorSource :=
            Sampling.approximation secondDenominator.name
          have numeratorClose := numeratorComparison.close
            (firstNumeratorBound.trans firstOrder)
            (secondNumeratorBound.trans secondOrder)
          have denominatorCloseForward := denominatorComparison.close
            (firstDenominatorBound.trans firstOrder)
            (secondDenominatorBound.trans secondOrder)
          have denominatorClose :
              Data.Gaussian.Norm.Basic.normSq (secondDenominatorSource.sample secondLater -
                  firstDenominatorSource.sample firstLater) <= inputTarget := by
            have identity :
                secondDenominatorSource.sample secondLater -
                    firstDenominatorSource.sample firstLater =
                  -(firstDenominatorSource.sample firstLater -
                    secondDenominatorSource.sample secondLater) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact denominatorCloseForward.le
          have commonFirst : Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart
            secondApart <=
              Data.Gaussian.Norm.Basic.normSq (firstDenominatorSource.sample firstLater) :=
            (Fraction.Order.Basic.min_le_left _ _).trans
              (Apart.Sampling.sampled_lower firstDenominator firstApart firstLater)
          have commonSecond : Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart
            secondApart <=
              Data.Gaussian.Norm.Basic.normSq (secondDenominatorSource.sample secondLater) :=
            (Fraction.Order.Basic.min_le_right _ _).trans
              (Apart.Sampling.sampled_lower secondDenominator secondApart secondLater)
          have quotientBound :=
            Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
              (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower_positive firstApart
                secondApart)
              (leftNumerator := firstNumeratorSource.sample firstLater)
              (rightNumerator := secondNumeratorSource.sample secondLater)
              (leftDenominator := firstDenominatorSource.sample firstLater)
              (rightDenominator := secondDenominatorSource.sample secondLater)
              (numeratorSlope := (1 : Fraction.Rational))
              (numeratorBound := secondNumeratorSource.centerBound)
              (denominatorBound := secondDenominatorSource.centerBound)
              (pointMovement := inputTarget)
              (rootMovement := inputTarget)
              (by
                simpa only [Fraction.Field.one_mul]
                  using numeratorClose.le)
              (secondNumeratorSource.sample_bounded secondLater)
              (secondDenominatorSource.sample_bounded secondLater)
              denominatorClose commonFirst commonSecond
          change Data.Gaussian.Norm.Basic.normSq
              (firstNumeratorSource.sample firstLater /
                  firstDenominatorSource.sample firstLater -
                secondNumeratorSource.sample secondLater /
                  secondDenominatorSource.sample secondLater) < target
          calc
            Data.Gaussian.Norm.Basic.normSq
                (firstNumeratorSource.sample firstLater /
                    firstDenominatorSource.sample firstLater -
                  secondNumeratorSource.sample secondLater /
                    secondDenominatorSource.sample secondLater) <=
              Purelib.Approximation.Rational.Budget.Quotient.quotientBound
                1 secondNumeratorSource.centerBound
                secondDenominatorSource.centerBound
                (Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.commonLower firstApart secondApart)
                  inputTarget inputTarget :=
              quotientBound
            _ = inputTarget *
                Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
                  secondNumerator
                  secondDenominator firstApart secondApart := by
              dsimp only [firstNumeratorSource, secondNumeratorSource,
                firstDenominatorSource, secondDenominatorSource]
              unfold Purelib.Approximation.Rational.Budget.Quotient.quotientBound
                Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonCoefficient
              rw [Algebra.Field.ExplicitField.div_eq_mul_inv,
                Algebra.Field.ExplicitField.div_eq_mul_inv]
              ring1
            _ < target :=
              Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence.quotientComparisonTarget_budget_lt
              secondNumerator secondDenominator firstApart secondApart positive }
end Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

end
