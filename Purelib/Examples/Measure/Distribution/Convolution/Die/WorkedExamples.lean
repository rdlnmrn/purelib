module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Convolution.Basic
import Purelib.Measure.Distribution.Convolution.Cumulative
import Purelib.Measure.Distribution.Convolution.Kolmogorov
import Purelib.Measure.Distribution.Convolution.Moments
import Purelib.Measure.Distribution.Cumulative.Basic
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kolmogorov.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Examples.Measure.Distribution.Coin.Law
public import Purelib.Examples.Measure.Distribution.Die.Basic
import Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Convolution.Die.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Law (coinNumberLaw)
open Purelib.Examples.Measure.Distribution.Die.Basic (rationalFairDie)
open Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples
  (coinNumberLawKolmogorovDistance_quarterCoinNumberLaw quarterCoinNumberLaw)

/-- The rational distribution of the sum of two independent fair dice. -/
def twoDieSum : Distribution
  Fraction.Rational :=
  rationalFairDie.convolve rationalFairDie

/-- Convolving the numeric coin and die laws in either order gives the same evaluation law. -/
example : Purelib.Measure.Distribution.EvaluationEquivalent
    (coinNumberLaw.convolve
      rationalFairDie)
    (rationalFairDie.convolve
      coinNumberLaw) :=
  coinNumberLaw.convolve_comm_evaluationEquivalent
    rationalFairDie

/-- Common left convolution keeps the fair-versus-quarter-heads Kolmogorov distance at most one quarter. -/
example (noise : Distribution Fraction.Rational) :
    (noise.convolve coinNumberLaw).kolmogorovDistance
        (noise.convolve quarterCoinNumberLaw) ≤ 1 / 4
          := by
  calc
    (noise.convolve coinNumberLaw).kolmogorovDistance
          (noise.convolve quarterCoinNumberLaw) ≤
        coinNumberLaw.kolmogorovDistance
          quarterCoinNumberLaw :=
      Distribution.kolmogorovDistance_convolve_left_le
        noise coinNumberLaw
          quarterCoinNumberLaw
    _ = 1 / 4 :=
      coinNumberLawKolmogorovDistance_quarterCoinNumberLaw

/-- Common right convolution keeps the fair-versus-quarter-heads Kolmogorov distance at most one quarter. -/
example (noise : Distribution Fraction.Rational) :
    (coinNumberLaw.convolve noise).kolmogorovDistance
        (quarterCoinNumberLaw.convolve noise) ≤ 1 / 4
          := by
  calc
    (coinNumberLaw.convolve noise).kolmogorovDistance
          (quarterCoinNumberLaw.convolve noise) ≤
        coinNumberLaw.kolmogorovDistance
          quarterCoinNumberLaw :=
      Distribution.kolmogorovDistance_convolve_right_le
        coinNumberLaw
          quarterCoinNumberLaw noise
    _ = 1 / 4 :=
      coinNumberLawKolmogorovDistance_quarterCoinNumberLaw

/-- The sum of two fair dice is at most seven with probability seven twelfths. -/
example : twoDieSum.cumulative 7 = 7 / 12 := by
  unfold twoDieSum
  rw [rationalFairDie.cumulative_convolve rationalFairDie
    7]
  decide

/-- The cumulative law of the two-die sum is the retained iterated cumulative expectation. -/
example : twoDieSum.cumulative 7 =
    rationalFairDie.expectation (fun first =>
      rationalFairDie.cumulative (7 - first)) :=
  rationalFairDie.cumulative_convolve rationalFairDie 7

/-- The rational event testing equality to seven. -/
def equalsSeven (value : Fraction.Rational)
  : Bool := decide (value = 7)

/-- The two-die sum equals seven with probability one sixth. -/
example : twoDieSum.probability
  equalsSeven = 1 / 6 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_probability rationalFairDie
    equalsSeven]
  decide

/-- The two-die sum has expectation seven. -/
example : twoDieSum.expectation (fun value => value) = 7 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_expectation
    rationalFairDie]
  decide

/-- The expectation of the two-die sum is the sum of the original die expectations. -/
example : twoDieSum.expectation (fun value => value) =
    rationalFairDie.expectation (fun value => value) +
      rationalFairDie.expectation (fun value => value) :=
  rationalFairDie.convolve_expectation rationalFairDie

/-- The two-die sum has variance thirty-five sixths. -/
example : twoDieSum.variance (fun value => value) = 35 / 6 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_variance rationalFairDie,
    Measure.Distribution.Die.Basic.rationalFairDie_coordinate_variance]
  rw [← two_mul]
  calc
    2 * (35 / 12 : Fraction.Rational) = 70 / 12 := by
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 35 / 6 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
      · exact (Fraction.Cast.Order.natCast_pos_direct
          (n := 12) (by decide)).ne'
      · exact (Fraction.Cast.Order.natCast_pos_direct
          (n := 6) (by decide)).ne'
      · ring1

/-- The variance of the two-die sum is the sum of the original die variances. -/
example : twoDieSum.variance (fun value => value) =
    rationalFairDie.variance (fun value => value) +
      rationalFairDie.variance (fun value => value) :=
  rationalFairDie.convolve_variance rationalFairDie

end Purelib.Examples.Measure.Distribution.Convolution.Die.WorkedExamples

end
