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

open Purelib.Data.Rat.Fraction.Order

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
  CoherentNamed}
    (firstApart : Named.Apart first.name) (secondApart : Named.Apart second.name) :
    Fraction.Rational :=
  min firstApart.certificate.lowerSq secondApart.certificate.lowerSq

/-- The minimum of the two retained denominator lower squared norms is strictly positive.

Each original apartness certificate supplies its own positive squared-norm
floor. Their unchanged minimum retains a shared lower bound for both names. -/
theorem commonLower_positive {first
  second : CoherentNamed}
    (firstApart : Named.Apart first.name) (secondApart : Named.Apart second.name) :
    0 < commonLower firstApart secondApart :=
  Basic.lt_min firstApart.certificate.positive secondApart.certificate.positive

/-- Sensitivity coefficient for comparing two quotients. -/
def quotientComparisonCoefficient
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name) : Fraction.Rational :=
  Quotient.comparisonCoefficient
    (Sampling.approximation secondNumerator.name).centerBound
    (Sampling.approximation secondDenominator.name).centerBound
    (commonLower firstApart secondApart)

/-- The quotient comparison coefficient is nonnegative for the retained denominator apartness certificates. -/
theorem
  quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name) :
    0 <= quotientComparisonCoefficient
      secondNumerator secondDenominator
      firstApart secondApart :=
  Quotient.comparisonCoefficient_nonnegative
    (Sampling.approximation secondNumerator.name).centerBound_nonneg
    (Sampling.approximation secondDenominator.name).centerBound_nonneg
    (commonLower_positive firstApart secondApart).le

/-- The operand comparison target obtained by dividing the requested quotient tolerance by one plus its retained
sensitivity coefficient. -/
def quotientComparisonTarget
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    (target : Fraction.Rational) : Fraction.Rational :=
  Quotient.comparisonTarget
    (Sampling.approximation secondNumerator.name).centerBound
    (Sampling.approximation secondDenominator.name).centerBound
    (commonLower firstApart secondApart) target

/-- A positive output tolerance gives a positive operand quotient-comparison target.

The retained quotient sensitivity is nonnegative. Adding one makes its same
original denominator positive before dividing the supplied output tolerance. -/
theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < quotientComparisonTarget secondNumerator
      secondDenominator
      firstApart secondApart target :=
  Quotient.comparisonTarget_positive
    (Sampling.approximation secondNumerator.name).centerBound_nonneg
    (Sampling.approximation secondDenominator.name).centerBound_nonneg
    (commonLower_positive firstApart secondApart).le positive

/-- The retained operand target times its sensitivity stays below the positive output tolerance.

The original sensitivity is strictly smaller than its incremented denominator.
Positive scaling and exact division rearrangement retain the same operand target. -/
theorem
  quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    {target : Fraction.Rational} (positive : 0 < target) :
    quotientComparisonTarget secondNumerator
      secondDenominator
        firstApart secondApart target *
      quotientComparisonCoefficient secondNumerator
        secondDenominator
        firstApart secondApart < target :=
  Quotient.comparisonTarget_budget_lt
    (Sampling.approximation secondNumerator.name).centerBound_nonneg
    (Sampling.approximation secondDenominator.name).centerBound_nonneg
    (commonLower_positive firstApart secondApart).le positive

open Purelib.Data.Nat in
/-- Compare the actual finite sampled quotients from two retained bounded operand comparisons.

Both original denominator apartness guards remain in the output. The same
maxima synchronize their actual operand indices, and the original finite
quotient-variation bound pays the supplied strict output budget. Numerator
and denominator comparisons may retain distinct nonzero spatial errors.
-/
def sampledQuotientComparison
    (firstNumerator secondNumerator firstDenominator secondDenominator : CoherentNamed)
    (firstApart : Named.Apart firstDenominator.name) (secondApart : Named.Apart secondDenominator.name)
    {firstStart secondStart : Nat} {numeratorTarget denominatorTarget : Fraction.Rational}
    (numeratorComparison : Equivalence.Comparison
      (Sampling.approximation firstNumerator.name) (Sampling.approximation secondNumerator.name)
      firstStart secondStart numeratorTarget)
    (denominatorComparison : Equivalence.Comparison
      (Sampling.approximation firstDenominator.name) (Sampling.approximation secondDenominator.name)
      firstStart secondStart denominatorTarget)
    (target : Fraction.Rational)
    (budget : Quotient.quotientBound 1 (Sampling.approximation secondNumerator.name).centerBound
      (Sampling.approximation secondDenominator.name).centerBound (commonLower firstApart secondApart)
      numeratorTarget denominatorTarget < target) :
    Equivalence.Comparison
      (Sample.sampledQuotientApproximation firstNumerator firstDenominator firstApart)
      (Sample.sampledQuotientApproximation secondNumerator secondDenominator secondApart)
      firstStart secondStart target := by
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
            Basic.normSq (secondDenominatorSource.sample secondLater -
                firstDenominatorSource.sample firstLater) <= denominatorTarget := by
          have identity :
              secondDenominatorSource.sample secondLater -
                  firstDenominatorSource.sample firstLater =
                -(firstDenominatorSource.sample firstLater -
                  secondDenominatorSource.sample secondLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
          rw [identity, Basic.normSq_neg]
          exact denominatorCloseForward.le
        have commonFirst : commonLower firstApart
          secondApart <=
            Basic.normSq (firstDenominatorSource.sample firstLater) :=
          (Basic.min_le_left _ _).trans
            (Apart.Sampling.sampled_lower firstDenominator firstApart firstLater)
        have commonSecond : commonLower firstApart
          secondApart <=
            Basic.normSq (secondDenominatorSource.sample secondLater) :=
          (Basic.min_le_right _ _).trans
            (Apart.Sampling.sampled_lower secondDenominator secondApart secondLater)
        have quotientBound :=
          Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
            (commonLower_positive firstApart
              secondApart)
            (leftNumerator := firstNumeratorSource.sample firstLater)
            (rightNumerator := secondNumeratorSource.sample secondLater)
            (leftDenominator := firstDenominatorSource.sample firstLater)
            (rightDenominator := secondDenominatorSource.sample secondLater)
            (numeratorSlope := (1 : Fraction.Rational))
            (numeratorBound := secondNumeratorSource.centerBound)
            (denominatorBound := secondDenominatorSource.centerBound)
            (pointMovement := numeratorTarget)
            (rootMovement := denominatorTarget)
            (by
              simpa only [Fraction.Field.one_mul]
                using numeratorClose.le)
            (secondNumeratorSource.sample_bounded secondLater)
            (secondDenominatorSource.sample_bounded secondLater)
            denominatorClose commonFirst commonSecond
        exact quotientBound.trans_lt budget }

end Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

end

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

/-- The original common quotient operand request pays the actual finite quotient-variation bound.

The same retained center bounds and denominator floor form its exact
coefficient. Both operand errors use that one original positive request;
its original coefficient payment then gives the strict output margin.
-/
theorem quotientComparison_budget_lt (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Named.Apart firstDenominator.name) (secondApart : Named.Apart secondDenominator.name)
    {target : Fraction.Rational} (positive : 0 < target) :
    Quotient.quotientBound 1 (Sampling.approximation secondNumerator.name).centerBound
      (Sampling.approximation secondDenominator.name).centerBound (commonLower firstApart secondApart)
      (quotientComparisonTarget secondNumerator secondDenominator firstApart secondApart target)
      (quotientComparisonTarget secondNumerator secondDenominator firstApart secondApart target) < target :=
  Quotient.comparison_budget_lt
    (Sampling.approximation secondNumerator.name).centerBound_nonneg
    (Sampling.approximation secondDenominator.name).centerBound_nonneg
    (commonLower_positive firstApart secondApart).le positive

end Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

end

@[expose] public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

open Purelib.Data.Nat in
/-- Canonical finite quotient approximations preserve operational equality in both operands.

Each original denominator retains its own positive apartness certificate.
The same maxima synchronize numerator and denominator comparison indices,
and the original shared lower floor pays their quotient error bound. -/
def sampledQuotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      CoherentNamed)
    (firstApart : Named.Apart firstDenominator.name)
    (secondApart : Named.Apart secondDenominator.name)
    (numeratorEquivalent : Equivalence.NamedEquivalent firstNumerator.name
      secondNumerator.name)
    (denominatorEquivalent : Equivalence.NamedEquivalent firstDenominator.name
      secondDenominator.name) :
    Equivalence.Equivalent
      (Sample.sampledQuotientApproximation firstNumerator firstDenominator firstApart)
      (Sample.sampledQuotientApproximation secondNumerator secondDenominator
        secondApart) where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := quotientComparisonTarget
      secondNumerator
      secondDenominator firstApart secondApart target
    have inputPositive : 0 < inputTarget :=
      quotientComparisonTarget_positive secondNumerator
        secondDenominator
        firstApart secondApart positive
    let numeratorComparison := numeratorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let denominatorComparison := denominatorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    apply sampledQuotientComparison firstNumerator secondNumerator firstDenominator secondDenominator
      firstApart secondApart numeratorComparison denominatorComparison target
    exact quotientComparison_budget_lt secondNumerator secondDenominator firstApart secondApart positive

end Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence

end
