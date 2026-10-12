module
import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.EncodedPrefix.Observation
import Purelib.Approximation.CCL.EncodedPrefix.Sensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.EncodedPrefix.Concentration
import Purelib.Measure.CCL.EncodedPrefix.Estimator
import Purelib.Measure.CCL.EncodedPrefix.Law
import Purelib.Measure.CCL.EncodedPrefix.Quantile
import Purelib.Measure.CCL.EncodedPrefix.Sampling
import Purelib.Measure.CCL.EncodedPrefix.Sampling.ThresholdGrid
import Purelib.Measure.CCL.EncodedPrefix.Stability.Squared
import Purelib.Measure.CCL.EncodedPrefix.Threshold
import Purelib.Measure.CCL.EncodedPrefix.Transport
import Purelib.Measure.CCL.EncodedPrefix.Variance
import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
import Purelib.Measure.Distribution.Sampling.ThresholdGrid

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.GaussianInt.Basic

open Purelib.Data

section
@[expose] public section

/-!
# Exact executable CCL examples

The three CCL expansions printed in the manuscript are evaluated by the
active constructive encoder.  Kernel `decide` checks only the displayed
finite Gaussian-integer inputs and finite output lists; no native-code axiom
or completed stream is involved.
-/

namespace Purelib.Examples.Data.GaussianInt.Fraction.WorkedExamples

open Purelib.Examples

open Purelib.Measure

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)
open Purelib.Geometry.Projective.Chordal
open Purelib.Data.CCL.Encoding.Encoder
open Purelib.Geometry.Projective
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.CCL.Encoding.Cylinder

/-- The Gaussian-integer fraction `(3 + 4i)/5` with its nonzero denominator witness. -/
def threePlusFourIOverFive :
  GaussianInt.Fraction :=
  ⟨⟨3, 4⟩, ⟨5, 0⟩, by decide⟩

/-- The Gaussian-integer fraction `13/5` with its nonzero denominator witness. -/
def thirteenOverFive : GaussianInt.Fraction :=
  ⟨⟨13, 0⟩, ⟨5, 0⟩, by decide⟩

/-- The Gaussian-integer fraction `355/113` with its nonzero denominator witness. -/
def threeFiftyFiveOverOneThirteen :
  GaussianInt.Fraction :=
  ⟨⟨355, 0⟩, ⟨113, 0⟩, by decide⟩

/-- The displayed numerator `3 + 4i` is nonzero. -/
theorem threePlusFourIOverFive_num_ne :
    threePlusFourIOverFive.numerator ≠ 0 := by decide

/-- The displayed numerator thirteen is nonzero. -/
theorem thirteenOverFive_num_ne :
  thirteenOverFive.numerator ≠ 0 := by decide

/-- The displayed numerator 355 is nonzero. -/
theorem threeFiftyFiveOverOneThirteen_num_ne :
    threeFiftyFiveOverOneThirteen.numerator ≠ 0 := by decide

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

/-! The concrete encoder-to-measure bridge retains the exact homogeneous
coordinates emitted by the executable integral encoder. -/

/-- The encoder input retaining the exact Gaussian-integer coordinates of `(3 + 4i)/5`. -/
def encodedThreePlusFourIOverFive :
  SourceEncodingEncoderFracAlias :=
  ⟨⟨3, 4⟩, ⟨5, 0⟩, by decide⟩

section

/-- The displayed encoder input has nonzero numerator. -/
theorem
  encodedThreePlusFourIOverFive_num_ne :
    encodedThreePlusFourIOverFive.numerator ≠ 0 := by decide

/-- The encoded projective point and affine fraction value have the same chordal omega probe. -/
example :
    Probe.chordalOmegaProbe
        (Blocks.encodeBlocks
          encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).point =
      Probe.chordalOmegaProbe
        (Line.Proj.affine
          encodedThreePlusFourIOverFive.value) :=

  open Purelib.Approximation in CCL.EncodedPrefix.encodedChordalOmegaProbe_eq_value
    encodedThreePlusFourIOverFive
      encodedThreePlusFourIOverFive_num_ne

/-- Mapping a fair coin to the encoded probe or affine-value probe gives evaluation-equivalent laws. -/
example : Distribution.EvaluationEquivalent
    (fairCoin.map fun _ =>
      Probe.chordalOmegaProbe
      (Blocks.encodeBlocks
        encodedThreePlusFourIOverFive
        encodedThreePlusFourIOverFive_num_ne).point)
    (fairCoin.map fun _ =>
      Probe.chordalOmegaProbe
      (Line.Proj.affine
        encodedThreePlusFourIOverFive.value)) :=

    CCL.EncodedPrefix.encodedChordalOmegaProbeLaw_evaluationEquivalent
    fairCoin (fun _ =>
      encodedThreePlusFourIOverFive)
      (fun _ => encodedThreePlusFourIOverFive_num_ne)

end

/-- Accuracy one half requires eight encoded estimator blocks. -/
example : Budget.encodedChordalOmegaEstimatorBlockCount
    (1 / 2) = 8 := by decide

/-- Accuracy one half and failure budget one tenth require 161 estimator samples. -/
example : Budget.encodedChordalOmegaEstimatorSampleCount
    (1 / 2) (1 / 10) = 161 := by decide

section

/-- A nonnegative chordal-sensitivity bound yields a prefix probe enclosure containing the exact affine fraction value.
-/
example (probe : Line.GaussianLine →
  Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Basic.chordalSq left right) :
    (Purelib.Approximation.CCL.EncodedPrefix.encodedProjectivePrefixProbeBound
      encodedThreePlusFourIOverFive
        encodedThreePlusFourIOverFive_num_ne
      probe factor factorNonnegative sensitive).Contains
        (probe (Line.Proj.affine
          encodedThreePlusFourIOverFive.value)) :=

  open Purelib.Approximation in CCL.EncodedPrefix.encodedProjectivePrefixProbeBound_contains_value
    encodedThreePlusFourIOverFive
      encodedThreePlusFourIOverFive_num_ne
      probe factor factorNonnegative sensitive

/-- The squared probe-expectation separation is bounded by the expected encoded cylinder spread. -/
example :
    Distance.rationalSeparation
        (fairCoin.expectation fun _ =>
          Probe.chordalOmegaProbe
            (Blocks.encodeBlocks
              encodedThreePlusFourIOverFive
              encodedThreePlusFourIOverFive_num_ne).point)
        (fairCoin.expectation fun _ =>
          Probe.chordalOmegaProbe
            (Line.Proj.affine
              encodedThreePlusFourIOverFive.value)) ^ 2 ≤
      fairCoin.expectation fun _ =>
        2 * Purelib.Approximation.CCL.Cylinder.cylinderSpread
          (Blocks.encodeBlocks
            encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne).blocks :=    by
  apply CCL.EncodedPrefix.encodedChordalOmegaProbe_expectation_separation_sq_le
    fairCoin (fun _ =>
      encodedThreePlusFourIOverFive)
      (fun _ => encodedThreePlusFourIOverFive_num_ne)
      (fun _ => (Blocks.encodeBlocks
        encodedThreePlusFourIOverFive
        encodedThreePlusFourIOverFive_num_ne).point)
  intro atom member
  exact Data.CCL.Encoding.Encoder.Blocks.encodeBlocks_realizes
    encodedThreePlusFourIOverFive
    encodedThreePlusFourIOverFive_num_ne

/-- A distribution of realizations of the displayed prefix has probe variance at most twice its cylinder spread. -/
example {index : Type} (distribution : Distribution index)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks
          encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks
        (points atom.item)) :
    distribution.variance
        (fun item => Probe.chordalOmegaProbe (points item)) ≤
      2 * Purelib.Approximation.CCL.Cylinder.cylinderSpread
        (Blocks.encodeBlocks
          encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks :=

   CCL.EncodedPrefix.encodedChordalOmegaProbeVariance_le
    encodedThreePlusFourIOverFive
      encodedThreePlusFourIOverFive_num_ne
    distribution points pointsRealize

/-- The retained prefix variance budget supplies an independent-sample count whose mean-deviation probability is below
the requested positive failure budget. -/
example {index : Type} (distribution : Distribution index)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks
          encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks
        (points atom.item))
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget
            encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne 2)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (Distribution.requiredChebyshevSampleCount
          (CCL.EncodedPrefix.encodedProbeVarianceBudget
            encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne 2)
          threshold failure)
        (fun item => Probe.chordalOmegaProbe (points item))
        threshold) < failure :=

    CCL.EncodedPrefix.encodedChordalOmegaProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    encodedThreePlusFourIOverFive
      encodedThreePlusFourIOverFive_num_ne
    distribution points pointsRealize threshold thresholdPositive failure
    failurePositive

end

/-- Two realizations of sufficiently long encoded prefixes have identical threshold probabilities when the exact values
are separated from the threshold by a positive margin. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction atom.item).value) ∨
        Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (atLeastEvent threshold fun item =>
          Probe.chordalOmegaProbe (leftPoints item)) =
      distribution.probability
        (atLeastEvent threshold fun item =>
          Probe.chordalOmegaProbe (rightPoints item)) :=

   CCL.EncodedPrefix.encodedChordalOmegaProbe_thresholdProbabilities_eq_of_margin
    distribution fraction numeratorNonzero threshold margin marginPositive
    separated enough leftPoints rightPoints leftRealizes rightRealizes

/-- Sufficient encoded prefix length bounds the separation of corresponding lower quantiles by the requested positive
accuracy. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun item =>
          Probe.chordalOmegaProbe (points item)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun item => Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon :=

   CCL.EncodedPrefix.encodedChordalOmegaProbe_lowerQuantile_separation_le_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize level levelPositive levelAtMostOne

/-- Sufficient encoded prefix length bounds probe-variance separation by four times the requested positive accuracy. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.variance fun item =>
          Probe.chordalOmegaProbe (points item))
        (distribution.variance fun item =>
          Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction item).value)) ≤ 4 * epsilon :=

   CCL.EncodedPrefix.encodedChordalOmegaProbe_variance_separation_le_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize

/-- The original encoded probe-law coupling has squared transport cost below the square of the requested accuracy. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction
      Probe.chordalOmegaProbe points).transportCost
        (fun left right => Distance.rationalSeparation left right ^ 2) < epsilon ^ 2 :=

   CCL.EncodedPrefix.encodedChordalOmegaProbeLawCoupling_squaredTransportCost_lt_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize

/-- The encoded estimator's block and sample budgets bound deviation from the exact affine probe expectation by the
requested failure probability. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.encodedChordalOmegaEstimatorBlockCount epsilon ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Budget.encodedChordalOmegaEstimatorSampleCount
          epsilon failure)).probability
      (Distribution.Projective.Chordal.encodedChordalOmegaSampleMeanTargetDeviation
        distribution fraction
        (Budget.encodedChordalOmegaEstimatorSampleCount
          epsilon failure)
        points epsilon) < failure :=

   CCL.EncodedPrefix.encodedChordalOmegaSampleMean_targetDeviationProbability_lt_requested
    distribution fraction numeratorNonzero points pointsRealize epsilon
    epsilonPositive enough failure failurePositive

/-- The displayed two-threshold grid requires 1501 independent samples at the given tolerance and failure budget. -/
example :
    Distribution.Sampling.requiredEncodedChordalOmegaThresholdGridSampleCount
      (fun _ : Bool =>
        (Blocks.encodeBlocks
          encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).point)
      [0, 1] (1 / 10) (1 / 20) = 1501 := by decide

/-- A sample outside the retained threshold-grid deviation event satisfies the exact target bounds.

The original encoded realizations, finite threshold list, positive margin and sufficient block count identify the same
threshold events. -/
example {index : Type} (distribution : Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Projective.ProjectiveRealizes
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Fraction.Rational)
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) ∨
          Probe.chordalOmegaProbe
              (Line.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside :
      Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation
        distribution points thresholds count tolerance sample = false) :
    Distribution.Projective.Chordal.EncodedChordalOmegaThresholdGridTargetWithin
      distribution fraction points thresholds count tolerance sample :=

   CCL.EncodedPrefix.encodedChordalOmegaThresholdGridTargetWithin_of_outside
    distribution fraction numeratorNonzero points pointsRealize thresholds
    margin marginPositive separated enough count tolerance tolerancePositive
    sample outside

end Purelib.Examples.Data.GaussianInt.Fraction.WorkedExamples

end
