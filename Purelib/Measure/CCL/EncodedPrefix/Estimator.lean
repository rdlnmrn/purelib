module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Approximation.Rational.Budget.Dyadic
public import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.EncodedPrefix.Stability.Squared
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Projective.Chordal.Probe
public import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Event

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Sampling.Request
public import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.GaussianInt.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# End-to-end finite estimation of encoded affine expectations

For the concrete distance-to-`omega` observable, a heterogeneous finite table
of CCL encoder outputs can be estimated by an explicit finite iid sample.
Half of a requested rational error is assigned to finite-prefix bias and half
to sampling fluctuation.  The global `[0, 1]` range of the observable supplies
the uniform variance budget `1` used by the constructive Chebyshev request.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested encoder and sampling budgets control sample-mean error relative to the exact affine omega-probe
expectation.

Every sampled point realizes its fraction's exact encoded blocks. Positive tolerance and failure requests allocate
separate bounds to encoding bias and sampling variance under the original finite law. -/
theorem encodedChordalOmegaSampleMean_targetDeviationProbability_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.encodedChordalOmegaEstimatorBlockCount epsilon ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Budget.encodedChordalOmegaEstimatorSampleCount epsilon failure)).probability
      (Distribution.Projective.Chordal.encodedChordalOmegaSampleMeanTargetDeviation distribution fraction
        (Budget.encodedChordalOmegaEstimatorSampleCount epsilon failure)
        points epsilon) < failure := by
  let value : index → Fraction.Rational := fun item => Chordal.Probe.chordalOmegaProbe (points item)
  let observedMean := distribution.expectation value
  let exactMean := Distribution.Projective.Chordal.encodedChordalOmegaExactExpectation distribution fraction
  let half := epsilon / 2
  let count := Budget.encodedChordalOmegaEstimatorSampleCount epsilon failure
  have halfPositive : 0 < half := Fraction.half_positive epsilonPositive
  have biasSmall :
      Distance.rationalSeparation observedMean exactMean < half := by
    exact CCL.EncodedPrefix.encodedChordalOmegaProbe_expectation_separation_lt_requested
      distribution fraction numeratorNonzero half halfPositive
      (by
        intro atom member
        exact enough atom member)
      points pointsRealize
  have varianceLe : distribution.variance value ≤ 1 :=
    Distribution.Projective.Chordal.chordalOmegaProbe_variance_le_one distribution points (by
      intro atom member
      exact (pointsRealize atom member).valid)
  have samplingSmall :
      (distribution.iidSamples count).probability
          (distribution.sampleMeanDeviation count value half) < failure := by
    exact distribution.iidSamples_sampleMean_deviationProbability_lt_requested
      value 1 (by decide) varianceLe half halfPositive failure failurePositive
  calc
    (distribution.iidSamples count).probability
          (Distribution.Projective.Chordal.encodedChordalOmegaSampleMeanTargetDeviation distribution fraction
            count points epsilon) ≤
        (distribution.iidSamples count).probability
          (distribution.sampleMeanDeviation count value half) := by
      unfold Distribution.probability
      apply Measure.eventWeight_mono
      intro atom member selected
      have targetFar : epsilon ≤
          Distance.rationalSeparation
            (Distribution.sampleMean count value atom.item)
            exactMean := of_decide_eq_true selected
      apply decide_eq_true
      rw [← Distance.NaturalLp.rationalSeparation_sq]
      have halfLe : half ≤ Distance.rationalSeparation
          (Distribution.sampleMean count value atom.item)
          observedMean := by
        apply Fraction.Order.Arithmetic.le_of_not_gt_direct
        intro sampleClose
        have totalSmall : Distance.rationalSeparation
            (Distribution.sampleMean count value atom.item)
            exactMean < epsilon := by
          calc
            Distance.rationalSeparation
                (Distribution.sampleMean count value
                  atom.item) exactMean ≤
                Distance.rationalSeparation
                    (Distribution.sampleMean count value
                      atom.item) observedMean +
                  Distance.rationalSeparation observedMean
                    exactMean :=
              Distance.rationalSeparation_triangle _ _ _
            _ < half + half :=
              Fraction.Order.Arithmetic.add_lt_add_direct sampleClose biasSmall
            _ = epsilon := Fraction.half_add_half epsilon
        exact (not_lt_of_ge targetFar) totalSmall
      exact Fraction.Order.Arithmetic.pow_le_pow_direct halfPositive.le halfLe 2
    _ < failure := samplingSmall

end Purelib.Measure.CCL.EncodedPrefix

end
