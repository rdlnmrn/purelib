module

import TestPurelib.Curves.Legendre.PeriodVariation.Sampling
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
import Purelib.Approximation.AccuracyRequest.Scaling

/-! # Two residual payments on one actual later nonsquare-root observation

The original fixture's full target certificate is retained. An additional
quarter of the original increment-fourth request is paid first; the actual
primary observation is then selected after that original comparison stage.
Both request payments apply to the selected primary candidates, with both
original comparison caches and actual indices retained.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Joint

open Purelib
open Purelib.Approximation
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.RootContinuation
open TestPurelib.Curves.Legendre.PeriodVariation

/-- The original nonzero-increment fourth-order residual request. -/
def primary : AccuracyRequest := Variation.Sampling.incrementRequest Sampling.increment (by decide +kernel)

/-- A separate tighter spatial residual request on that same retained original root process. -/
def additional : AccuracyRequest := primary.quarter

/-- Both actual comparisons and the primary state selected after the additional paid stage. -/
def retained := CertifiedSquareRoot.Sampling.requestJoint Sampling.target primary additional

attribute [local irreducible] retained

/-- The retained primary observation is selected no earlier than the actual additional comparison index. -/
theorem after_additional : retained.1.comparison.leftIndex ≤ retained.2.val.comparison.leftIndex :=
  retained.2.property

/-- The primary observation pays its exact original increment-fourth request. -/
theorem primary_residual : Norm.Basic.normSq
    (retained.2.val.reading * retained.2.val.reading -
      (Polynomials.curveValue (Sampling.parameter + Sampling.increment) 2)) <
        primary.tolerance := retained.2.val.reading_residual_lt

/-- That same actual primary witness also pays the independently requested finer spatial residual. -/
theorem additional_residual : Norm.Basic.normSq
    (retained.2.val.reading * retained.2.val.reading -
      (Polynomials.curveValue (Sampling.parameter + Sampling.increment) 2)) <
        additional.tolerance := retained.1.reading_residual_lt_after retained.2.val retained.2.property

/-- Every candidate of that exact same primary observation inherits the additional payment. -/
theorem additional_candidates {candidate : Canonical}
    (possible : retained.2.val.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate -
      (Polynomials.curveValue (Sampling.parameter + Sampling.increment) 2)) <
        additional.tolerance := retained.1.residual_lt_after retained.2.val retained.2.property possible

/-- The additional payment uses exactly one quarter of the original primary request. -/
theorem additional_tolerance : additional.tolerance = primary.tolerance / 4 :=
  AccuracyRequest.quarter_tolerance primary

end TestPurelib.Curves.Legendre.PeriodVariation.Joint
