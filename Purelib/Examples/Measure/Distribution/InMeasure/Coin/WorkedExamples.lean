module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Convergence
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Convergence.Bounded
import Purelib.Measure.Distribution.Convergence.InMeasure
public import Purelib.Measure.Distribution.Convergence.L2
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Event.RationalDistance
public import Purelib.Measure.Uniformity
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Rat.Order
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.PointwiseMinimum
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Content
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.InMeasure.Coin.WorkedExamples

open Purelib
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin reverseCoinNumber)

/-- The in-measure comparison of the two coin indicators obtained from their L1 distance at threshold one. -/
def coinInMeasureBudget :
  Distribution.InMeasureBudget
    fairCoin coinNumber
      reverseCoinNumber :=
  Distribution.InMeasureBudget.ofL1 fairCoin coinNumber
    reverseCoinNumber
    1 (by decide)

/-- The explicit half-threshold comparison budget with failure bound one. -/
def coinHalfInMeasureBudget :
  Distribution.InMeasureBudget
    fairCoin coinNumber
      reverseCoinNumber where
  threshold := 1 / 2
  threshold_positive := by decide
  failure := 1
  failure_nonnegative := by decide
  probability_le := by decide

/-- The L2 comparison budget retaining the half-threshold certificate and unit squared-distance ceiling. -/
def coinL2InMeasureBudget :
  Distribution.L2InMeasureBudget
    fairCoin coinNumber
      reverseCoinNumber where
  inMeasure := coinHalfInMeasureBudget
  ceiling := 1
  ceiling_nonnegative := by decide
  poweredL2Distance_le := by decide

/-- The half-threshold comparison has L1 excess one half. -/
example : coinHalfInMeasureBudget.l1Excess = 1 / 2 := by
  decide

/-- The squared L1 excess is bounded by the retained L2 ceiling times the failure bound. -/
example : coinHalfInMeasureBudget.l1Excess ^ 2 ≤
    coinL2InMeasureBudget.ceiling *
      coinHalfInMeasureBudget.failure :=
  coinL2InMeasureBudget.l1Excess_sq_le

/-- The original separation-event probability meets the retained in-measure failure bound. -/
example : fairCoin.probability
      (separationAtLeast coinInMeasureBudget.threshold
        coinNumber reverseCoinNumber) ≤
    coinInMeasureBudget.failure :=
  coinInMeasureBudget.probability_le

/-- The zero-failure in-measure budget comparing the coin indicator with itself. -/
def coinSelfInMeasureBudget :
  Distribution.InMeasureBudget
    fairCoin coinNumber
      coinNumber :=
  Distribution.InMeasureBudget.ofEqualAlmostEverywhere fairCoin
    coinNumber coinNumber
    (EqualOffZeroWeightOn.refl fairCoin.atoms
      coinNumber) 1 (by decide)

/-- The self-comparison has failure bound zero. -/
example : coinSelfInMeasureBudget.failure = 0 := rfl

/-- The common outside-exception budget for both coin indicators relative to one half at tolerance three quarters. -/
def coinUniformOutsideBudget :
  Distribution.UniformOutsideBudget fairCoin
    [coinNumber, reverseCoinNumber] (fun _ => 1 / 2) :=
  fairCoin.uniformOutsideBudget [coinNumber,
    reverseCoinNumber]
    (fun _ => 1 / 2) (3 / 4) (by decide)

/-- The common exceptional event has probability zero and the retained failure budget is zero. -/
example : coinUniformOutsideBudget.failure = 0 ∧
    fairCoin.probability
      coinUniformOutsideBudget.exceptional = 0 := by
  decide

/-- Each retained indicator differs from one half by less than three quarters on every original coin atom. -/
example (approximation : Bool → Fraction.Rational)
    (member : approximation ∈ [coinNumber,
      reverseCoinNumber])
    (atom : Weighted Bool) (atomMember : atom ∈ fairCoin.atoms) :
    Data.Rat.Distance.rationalSeparation (approximation atom.item) (1 / 2) < 3 / 4 := by
  apply coinUniformOutsideBudget.outside approximation member atom
    atomMember
  cases selected : atom.item <;> decide

/-- The product expectation of the two coin indicators satisfies the finite Cauchy-Schwarz bound. -/
example : fairCoin.expectation (fun outcome =>
      coinNumber outcome * reverseCoinNumber outcome) ^
        2 ≤
    fairCoin.poweredL2 coinNumber *
      fairCoin.poweredL2 reverseCoinNumber :=
  fairCoin.productExpectation_sq_le_poweredL2_mul
    coinNumber reverseCoinNumber

/-- The sum of the two indicators satisfies the retained powered-L2 radius bound. -/
example : fairCoin.toContent.poweredL2 (fun outcome =>
      coinNumber outcome + reverseCoinNumber outcome) ≤
    ((3 / 4 : Fraction.Rational) + 3 / 4) ^ 2 := by
  apply fairCoin.toContent.poweredL2_add_le_radius_add_sq
    coinNumber reverseCoinNumber (3 / 4) (3 / 4)
      (by decide) (by decide) <;> decide

/-- The product's powered L1 value is bounded by the first indicator's L1 value and the second indicator's unit bound.
-/
example : fairCoin.toContent.poweredL1 (fun outcome =>
      coinNumber outcome * reverseCoinNumber outcome) ≤
    1 * fairCoin.toContent.poweredL1 coinNumber := by
  apply fairCoin.toContent.poweredL1_mul_le_of_right_bounded
    coinNumber reverseCoinNumber 1 (by decide)
  intro atom member
  cases atom.item <;> decide

/-- The integrals of zero, the coin indicator and one form a monotone coordinate chain. -/
example : Purelib.Data.Rat.MonotoneCoordinateChain
    ([fun _ : Bool => (0 : Fraction.Rational), coinNumber, fun _ => 1].map
      fairCoin.toContent.integral) := by
  apply fairCoin.toContent.integral_monotoneChain
  simp only [PointwiseMonotoneChainOn]
  constructor
  · intro atom member
    cases atom.item <;> decide
  · constructor
    · intro atom member
      cases atom.item <;> decide
    · trivial

/-- The integral of the pointwise minimum of the two indicators is at most the first integral. -/
example : fairCoin.toContent.integral
      (Purelib.Data.Rat.pointwiseMinimum coinNumber
        [reverseCoinNumber]) ≤
    fairCoin.toContent.integral coinNumber := by
  apply fairCoin.toContent.integral_pointwiseMinimum_le_of_mem
  exact List.mem_cons_self

/-- The coin observable taking value two on heads and zero on tails. -/
def twoOnHeads (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 2 else 0

/-- The bounded in-measure budget for the two-on-heads observable relative to zero.

It retains threshold one, failure one half and pointwise error ceiling two. -/
def twoOnHeadsBoundedInMeasure :
  Distribution.BoundedInMeasureBudget
    fairCoin twoOnHeads (fun _ => 0)
      where
  inMeasure :=
    { threshold := 1
      threshold_positive := by decide
      failure := 1 / 2
      failure_nonnegative := by decide
      probability_le := by decide }
  ceiling := 2
  threshold_le_ceiling := by decide
  error_le := by
    intro atom member
    cases atom.item <;> decide

/-- The two-on-heads observable has L1 distance one from zero. -/
example : fairCoin.l1Distance
  twoOnHeads (fun _ => 0) = 1 := by
  decide

/-- The retained bounded-in-measure comparison gives L1 bound three halves. -/
example : twoOnHeadsBoundedInMeasure.l1Bound = 3 / 2 := by
  decide

/-- The actual L1 distance meets the retained bounded-in-measure bound. -/
example : fairCoin.l1Distance
  twoOnHeads (fun _ => 0) ≤
    twoOnHeadsBoundedInMeasure.l1Bound :=
  twoOnHeadsBoundedInMeasure.l1Distance_le

/-- The probability of separation at least two from zero is one half. -/
example : fairCoin.probability
    (separationAtLeast 2 twoOnHeads (fun _ => 0)) = 1 / 2 := by
  decide

/-- The separation-at-two probability satisfies the L1 tail bound. -/
example : fairCoin.probability
      (separationAtLeast 2 twoOnHeads (fun _ => 0)) ≤
    fairCoin.l1Distance twoOnHeads
      (fun _ => 0) / 2 :=
  fairCoin.probability_separationAtLeast_le_l1
    2 (by decide) twoOnHeads (fun _ => 0)

/-- The two-on-heads expectation gap from zero equals its L1 distance. -/
example : fairCoin.expectation
  twoOnHeads -
      fairCoin.expectation (fun _ => 0) =
    fairCoin.l1Distance twoOnHeads
      (fun _ => 0) := by
  decide

end Purelib.Examples.Measure.Distribution.InMeasure.Coin.WorkedExamples

end
