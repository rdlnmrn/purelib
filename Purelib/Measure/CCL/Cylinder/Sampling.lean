module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.CCL.Cylinder.Spread
public import Purelib.Approximation.Rational.Budget.ReciprocalSquare
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.Cylinder.Concentration.Squared
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Sampling.Request
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Measure.Distribution.Sampling.Deviation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Sampling.Basic

section
@[expose] public section

/-!
# Finite iid sampling certificates from CCL encoder cylinders

A squared-sensitive probe on one finite CCL cylinder has an explicit rational
variance budget.  Substituting that budget into the constructive Chebyshev
sample-count request yields a finite iid sample-mean deviation certificate.
For an actual encoder run, every quantity in the request is executable.
-/

namespace Purelib.Measure.CCL.Cylinder

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The cylinder-spread variance budget supplies a sample request meeting the exact squared-sensitive probe deviation
tolerance.

All original atom points and the retained witness projectively realize the same blocks; the threshold and failure
tolerance are positive and the sensitivity factor is nonnegative. -/
theorem
  projectiveRealizedSquaredProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (blocks : List Data.CCL.Encoding.Block) (witness : Line.GaussianLine)
    (witnessRealizes : Cylinder.Projective.ProjectiveRealizes blocks witness)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes blocks (points atom.item))
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredChebyshevSampleCount
          (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) threshold failure)).probability
      (distribution.sampleMeanDeviation
        (Distribution.requiredChebyshevSampleCount
          (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) threshold failure)
        (fun item => probe (points item)) threshold) < failure := by
  exact distribution.iidSamples_sampleMean_deviationProbability_lt_requested
    (fun item => probe (points item)) (factor * Approximation.CCL.Cylinder.cylinderSpread blocks)
    (Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
      (Approximation.CCL.Cylinder.cylinderSpread_nonneg blocks))
    (CCL.Cylinder.projectiveRealizedSquaredProbeVariance_le distribution blocks witness
      witnessRealizes points pointsRealize probe factor factorNonnegative
      sensitive)
    threshold thresholdPositive failure failurePositive
end Purelib.Measure.CCL.Cylinder

end
