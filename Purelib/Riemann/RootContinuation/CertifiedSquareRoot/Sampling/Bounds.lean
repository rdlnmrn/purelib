module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Quantitative readback of paid original root observations

The square comparison's retained minimum index already pays root spread.
Its selected left index determines the actual cached state and observation;
these bounds specialize that unchanged request and comparison rather than
performing another root refinement or replacing its witness.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- The actual later observation spread pays four times the independently requested earlier root radius. -/
theorem spread_lt_after {parameter : Canonical} {root : Certificate parameter}
    {earlierAccuracy laterAccuracy : AccuracyRequest}
    (earlier : ResidualObservation root earlierAccuracy) (later : ResidualObservation root laterAccuracy)
    (after : earlier.comparison.leftIndex ≤ later.comparison.leftIndex) :
    later.observation.spread < 4 * (radiusRequest root earlierAccuracy).tolerance := by
  rewrite [later.observation_eq]
  exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
    (earlier.radius_lt_after later after)

/-- The exact cached observation spread meets four times that same paid ball-radius request. -/
theorem spread_lt {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    sample.observation.spread < 4 * (radiusRequest root accuracy).tolerance := by
  rewrite [sample.observation_eq]
  exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel) sample.radius_lt

/-- The actual root observation spread has the computed original accuracy divided by its sensitivity denominator. -/
theorem spread_le {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    sample.observation.spread ≤ 4 * (accuracy.tolerance / radiusDenominator root) := sample.spread_lt.le

/-- The same original radius/spread request pays the normalized sixteen-magnitude sensitivity scale. -/
theorem sensitivity_spread_lt {parameter : Canonical} {root : Certificate parameter} {accuracy : AccuracyRequest}
    (sample : ResidualObservation root accuracy) :
    16 * candidateBound root * sample.observation.spread < accuracy.tolerance := by
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
    (Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide +kernel)) (candidateBound_pos root)) sample.spread_lt
  apply scaled.trans_eq
  apply Fraction.Field.mul_right_cancel_of_ne (c := radiusDenominator root) (radiusDenominator_pos root).ne'
  change (16 * candidateBound root * (4 * (accuracy.tolerance / radiusDenominator root))) * radiusDenominator root =
    accuracy.tolerance * radiusDenominator root
  calc
    _ = radiusDenominator root * ((accuracy.tolerance / radiusDenominator root) * radiusDenominator root) := by
      unfold radiusDenominator
      ring1
    _ = _ := by
      rewrite [Fraction.Field.div_mul_cancel_of_ne _ _ (radiusDenominator_pos root).ne']
      ring1

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.ResidualObservation
