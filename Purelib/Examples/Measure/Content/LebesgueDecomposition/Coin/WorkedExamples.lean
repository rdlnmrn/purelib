module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.AbsoluteContinuity.Atomic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
public import Purelib.Measure.Content.AbsoluteContinuity.Modulus
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Density.Basic
import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Content.Integral
public import Purelib.Measure.Content.Lebesgue.Basic
import Purelib.Measure.Content.Lebesgue.Uniqueness
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Operations
import Purelib.Measure.Content.Singularity
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Basic
public import Purelib.Measure.Distribution.Conditioning.Density
import Purelib.Measure.Distribution.Conditioning.Jensen
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Probability
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Product.TotalVariation
import Purelib.Measure.Distribution.Product.TotalVariation.Maximal
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Measure.Distribution.Sampling.TotalVariation
import Purelib.Measure.Distribution.Sampling.TotalVariation.Maximal
import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Distribution.TotalVariation.Density
import Purelib.Measure.Distribution.TotalVariation.Expectation
import Purelib.Measure.MaximalCoupling
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic
import Purelib.Measure.Content.Density.Transport

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Density
import Purelib.Measure.Distribution.Expectation

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Content.LebesgueDecomposition.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber coinPayoff fairCoin)
open Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic (fairCoin_true_positive trueCoin)

/-- The constant-one density relative to the fair coin. -/
def fairCoinDensity (_ : Bool) :
  Fraction.Rational := 1

/-- The density zero on tails and two on heads relative to the fair coin. -/
def trueCoinDensity (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 2 else 0

/-- The constant fair-coin density is pointwise nonnegative. -/
theorem fairCoinDensity_nonnegative :
    ∀ outcome, 0 ≤ fairCoinDensity outcome := by
  intro outcome
  unfold fairCoinDensity
  decide

/-- The conditioned heads density is pointwise nonnegative. -/
theorem trueCoinDensity_nonnegative :
    ∀ outcome, 0 ≤ trueCoinDensity outcome := by
  intro outcome
  cases outcome <;> decide

/-- The fair-coin density integrates to one. -/
theorem fairCoinDensity_normalizes :
    fairCoin.expectation
      fairCoinDensity = 1 := by
  decide

/-- The conditioned heads density integrates to one under the fair coin. -/
theorem trueCoinDensity_normalizes :
    fairCoin.expectation
      trueCoinDensity = 1 := by
  decide

/-- The fair coin reconstructed by reweighting with its constant density. -/
def fairCoinFromDensity : Distribution
  Bool :=
  fairCoin.reweight
    fairCoinDensity
    fairCoinDensity_nonnegative
    fairCoinDensity_normalizes

/-- The heads-only coin reconstructed by reweighting the fair coin with its displayed density. -/
def trueCoinFromDensity : Distribution
  Bool :=
  fairCoin.reweight
    trueCoinDensity
    trueCoinDensity_nonnegative
    trueCoinDensity_normalizes

/-- The retained finite Radon–Nikodym witness for the heads-only coin relative to the fair coin. -/
def trueCoinRadonNikodymWitness :
  AtomicChange.Witness
    fairCoin.toContent trueCoin.toContent :=
  Content.DensityWitness.ofAbsolutelyContinuous fairCoin.toContent
    trueCoin.toContent
    (fairCoin.conditioned_absolutelyContinuous
      (fun outcome => outcome) fairCoin_true_positive)

/-- The constructive absolute-continuity modulus for the heads-only coin relative to the fair coin. -/
def trueCoinAbsoluteContinuityModulus
  :
    Content.AbsoluteContinuityModulus
      trueCoin.toContent fairCoin.toContent
        :=
  (fairCoin.conditioned_absolutelyContinuous
    (fun outcome => outcome) fairCoin_true_positive).modulus

/-- The retained Lebesgue decomposition of fair-coin content relative to heads-only content. -/
def coinLebesgueDecomposition :
  Content.LebesgueDecomposition
    fairCoin.toContent trueCoin.toContent :=
  fairCoin.toContent.lebesgueDecomposition
    trueCoin.toContent

/-- The heads-only coin assigns probability one to heads. -/
example : trueCoin.probability (fun outcome => outcome) = 1 := by
  decide

/-- The fair and heads-only coins have total variation distance one half. -/
example : fairCoin.totalVariationDistance
  trueCoin = 1 / 2 := by
  decide

/-- Adding a common independent fair coin preserves total variation distance one half. -/
example : (fairCoin.product
  fairCoin).totalVariationDistance
      (trueCoin.product fairCoin) = 1 / 2 :=
        by
  rw [fairCoin.totalVariationDistance_product_common_right_eq
    trueCoin fairCoin]
  decide

/-- The total variation distance between the two coin products is bounded by the sum of the marginal distances. -/
example : (fairCoin.product
  fairCoin).totalVariationDistance
      (trueCoin.product
        trueCoin) ≤
    fairCoin.totalVariationDistance trueCoin
      +
      fairCoin.totalVariationDistance
        trueCoin :=
  fairCoin.totalVariationDistance_product_le_add
    trueCoin fairCoin
    trueCoin

/-- The total variation distance between the coin products satisfies the multiplicative complement bound. -/
example : (fairCoin.product
  fairCoin).totalVariationDistance
      (trueCoin.product
        trueCoin) ≤
    1 - (1 - fairCoin.totalVariationDistance
      trueCoin) *
      (1 - fairCoin.totalVariationDistance
        trueCoin) :=
  fairCoin.totalVariationDistance_product_le_one_sub_mul
    trueCoin fairCoin
      trueCoin

/-- Two independent fair tosses and two heads-only tosses have total variation distance three quarters. -/
example : (fairCoin.iidSamples 2).totalVariationDistance
    (trueCoin.iidSamples 2) = 3 / 4 := by
  decide

/-- The two-sample coin distance is bounded by twice the one-sample distance. -/
example : (fairCoin.iidSamples 2).totalVariationDistance
      (trueCoin.iidSamples 2) ≤
    (2 : Fraction.Rational) * fairCoin.totalVariationDistance
      trueCoin :=
  fairCoin.iidSamples_totalVariationDistance_le
    trueCoin 2

/-- The two-sample coin distance satisfies the complement-square bound. -/
example : (fairCoin.iidSamples 2).totalVariationDistance
      (trueCoin.iidSamples 2) ≤
    1 - (1 - fairCoin.totalVariationDistance
      trueCoin) ^ 2 :=
  fairCoin.iidSamples_totalVariationDistance_le_one_sub_pow
    trueCoin 2

/-- The displayed two densities have fair-coin L1 distance one. -/
example : fairCoin.l1Distance
  fairCoinDensity
  trueCoinDensity = 1 := by
  decide

/-- The density L1 distance equals twice the total variation distance of the reweighted coins. -/
example : fairCoin.l1Distance
  fairCoinDensity
  trueCoinDensity =
    2 * fairCoinFromDensity.totalVariationDistance
      trueCoinFromDensity :=
  fairCoin.l1Distance_eq_two_mul_totalVariationDistance_reweight
    fairCoinDensity
      trueCoinDensity
      fairCoinDensity_nonnegative
    trueCoinDensity_nonnegative
      fairCoinDensity_normalizes
    trueCoinDensity_normalizes

/-- The two reweighted coin laws have total variation distance one half. -/
example : fairCoinFromDensity.totalVariationDistance
    trueCoinFromDensity = 1 / 2 := by
  decide

/-- The fair and heads-only atom masses have L1 distance one. -/
example : fairCoin.atomMassL1Distance
  trueCoin = 1 := by
  decide

/-- Every event-probability difference is bounded by the coin laws' total variation distance. -/
example (event : Bool → Bool) :
    Distance.rationalSeparation (fairCoin.probability event)
        (trueCoin.probability event) ≤
      fairCoin.totalVariationDistance
        trueCoin :=
  fairCoin.probability_separation_le_totalVariationDistance
    trueCoin event

/-- The difference of the coin-number expectations is bounded by total variation distance. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinNumber)
      (trueCoin.expectation coinNumber) ≤
    fairCoin.totalVariationDistance trueCoin
      := by
  apply fairCoin.expectation_separation_le_totalVariationDistance_of_unitInterval
    trueCoin coinNumber
  · intro outcome
    cases outcome <;> decide
  · intro outcome
    cases outcome <;> decide

/-- The fair and heads-only coin-number expectations differ by one half. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinNumber)
    (trueCoin.expectation coinNumber) = 1 /
      2 := by
  decide

/-- The retained maximal coin coupling has mismatch probability one half. -/
example : (fairCoin.maximalLawCoupling
  trueCoin).mismatchProbability
      LawCoupling.equalityRelation = 1 / 2 := by
  rw [fairCoin.maximalLawCoupling_mismatchProbability]
  decide

/-- The heads-only integral is the fair-coin integral weighted by the retained Radon–Nikodym density. -/
example : trueCoin.toContent.integral
  coinNumber =
    fairCoin.toContent.integral (fun outcome =>
      trueCoinRadonNikodymWitness.density outcome *
        coinNumber outcome) :=
  trueCoinRadonNikodymWitness.integral_eq
    coinNumber

/-- The retained continuity request controls the heads-only probability of every sufficiently small fair-coin event. -/
example (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (event : Bool → Bool)
    (small : fairCoin.probability event <
      trueCoinAbsoluteContinuityModulus.request epsilon
        positive) :
    trueCoin.probability event < epsilon :=
  trueCoinAbsoluteContinuityModulus.controls epsilon positive
    event small

/-- Every fair-coin event splits into the retained regular and singular content contributions. -/
example (event : Bool → Bool) : fairCoin.toContent.measure event =
    coinLebesgueDecomposition.regular.measure event +
      coinLebesgueDecomposition.singular.measure event :=
  coinLebesgueDecomposition.measure_eq event

/-- The regular part of the retained decomposition is absolutely continuous with respect to heads-only content. -/
example : Content.AbsolutelyContinuous
    coinLebesgueDecomposition.regular
      trueCoin.toContent :=
  coinLebesgueDecomposition.regular_absolutelyContinuous

/-- The singular part of the retained decomposition is mutually singular with heads-only content. -/
example : Purelib.Measure.Content.MutuallySingular trueCoin.toContent
    coinLebesgueDecomposition.singular :=
  coinLebesgueDecomposition.source_mutuallySingular_singular

/-- Every other Lebesgue decomposition gives the same regular event measure. -/
example (other : Content.LebesgueDecomposition
      fairCoin.toContent trueCoin.toContent)
    (event : Bool → Bool) :
    other.regular.measure event =
      coinLebesgueDecomposition.regular.measure event :=
  other.regular_measure_eq coinLebesgueDecomposition event

/-- Every other Lebesgue decomposition gives the same singular event measure. -/
example (other : Content.LebesgueDecomposition
      fairCoin.toContent trueCoin.toContent)
    (event : Bool → Bool) :
    other.singular.measure event =
      coinLebesgueDecomposition.singular.measure event :=
  other.singular_measure_eq coinLebesgueDecomposition event

/-- The heads-only expectation equals the fair-coin conditional mean on heads. -/
example : trueCoin.expectation coinNumber =
    fairCoin.conditionalMean (fun outcome => outcome)
      coinNumber :=
  fairCoin.conditioned_expectation_eq_conditionalMean
    (fun outcome => outcome) fairCoin_true_positive
      coinNumber

/-- The conditional coin-payoff mean satisfies the square Jensen inequality. -/
example : fairCoin.conditionalMean (fun outcome => outcome)
  coinPayoff ^ 2 ≤
    fairCoin.conditionalMean (fun outcome => outcome)
      (fun outcome => coinPayoff outcome ^ 2) :=
  fairCoin.conditionalMean_sq_le (fun outcome => outcome)
    fairCoin_true_positive coinPayoff

/-- The absolute conditional mean is bounded by the conditional mean absolute payoff. -/
example : Distance.rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome)
        coinPayoff) 0 ≤
    fairCoin.conditionalMean (fun outcome => outcome) (fun item =>
      Distance.rationalSeparation (coinPayoff item) 0) :=
  fairCoin.conditionalMean_rationalSeparation_zero_le
    (fun outcome => outcome) fairCoin_true_positive
      coinPayoff

/-- Conditioning preserves the length of the original coin atom table. -/
example : trueCoin.atoms.length =
  fairCoin.atoms.length :=
  fairCoin.conditioned_atoms_length
    (fun outcome => outcome) fairCoin_true_positive

/-- The heads-only law gives the complement of heads probability zero. -/
example : trueCoin.probability
    (Purelib.Measure.complementEvent fun outcome => outcome) = 0 :=
  fairCoin.conditioned_probability_complement
    (fun outcome => outcome) fairCoin_true_positive

/-- The heads-only coin is absolutely continuous with respect to the fair coin. -/
example : Content.AbsolutelyContinuous trueCoin.toContent
    fairCoin.toContent :=
  fairCoin.conditioned_absolutelyContinuous
    (fun outcome => outcome) fairCoin_true_positive

/-- Coin absolute continuity is equivalent to preservation of zero singleton masses. -/
example : Content.AbsolutelyContinuous trueCoin.toContent
      fairCoin.toContent ↔
    ∀ outcome : Bool,
      fairCoin.toContent.measure (Purelib.Measure.atomEvent outcome) = 0 →
        trueCoin.toContent.measure (Purelib.Measure.atomEvent outcome) = 0
          :=
  Content.absolutelyContinuous_iff_atom_zero _ _

/-- A conditioned event probability is bounded by its original probability divided by the conditioning probability. -/
example (event : Bool → Bool) : trueCoin.probability event ≤
    (fairCoin.probability (fun outcome => outcome))⁻¹ *
      fairCoin.probability event :=
  fairCoin.conditioned_probability_le_inverse_mul
    (fun outcome => outcome) event fairCoin_true_positive

/-- The conditional probability of the full event equals its integral against the retained conditioning density. -/
example : fairCoin.conditionalProbability (fun _ => true)
      (fun outcome => outcome) fairCoin_true_positive =
    fairCoin.toContent.integral (fun item =>
      fairCoin.conditioningDensity (fun outcome => outcome)
          fairCoin_true_positive item *
        Purelib.Measure.Distribution.indicator (fun _ => true) item) :=
  fairCoin.conditionalProbability_eq_density_integral
    (fun outcome => outcome) (fun _ => true) fairCoin_true_positive

/-- Conditioning on the full event preserves the fair coin's evaluation law. -/
example : Purelib.Measure.Distribution.EvaluationEquivalent
    (fairCoin.conditioned (fun _ => true) (by decide))
      fairCoin :=
  fairCoin.conditioned_true_evaluationEquivalent (by decide)

/-- The conditional probability of the full event given heads is one. -/
example :
    fairCoin.conditionalProbability (fun _ => true) (fun outcome => outcome)
      fairCoin_true_positive = 1 := by
  decide

end Purelib.Examples.Measure.Content.LebesgueDecomposition.Coin.WorkedExamples

end
