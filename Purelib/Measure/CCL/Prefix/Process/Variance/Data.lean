module

import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.Approximation.Bound.Process
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Function.Rat.Distance
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.CCL.Prefix.Process.Enclosure
public import Purelib.Measure.CCL.Prefix.Process.Variance.Centered
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Progressive covariance from finite CCL prefixes

Three progressive witness-centred variance enclosures, for two rational
probes and their sum, combine by the exact finite polarization identity.
The resulting process retains only finite prefix states and computes a finite
request for every positive rational covariance tolerance.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
set_option genInjectivity false in
/-- Sensitivity data for a probe and its squared deviation about the process's fixed witness mean.

The certificate is indexed by the exact original prefix process, finite distribution and probe, with separate positive
factors for mean and deviation control. -/
structure ProbeCenteredVarianceProcessData {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) where
  /-- The sensitivity factor for the original probe's mean. -/ meanFactor : Fraction.Rational
  /-- The retained mean sensitivity factor is strictly positive. -/ meanFactorPositive : 0 < meanFactor
  /-- Probe separation is bounded by the retained mean factor times squared chordal distance. -/ meanSensitive : ∀ left
    right,
    Distance.rationalSeparation (probe left) (probe right) ≤
      meanFactor * Chordal.Basic.chordalSq left right
  /-- The sensitivity factor for squared deviation about the original witness expectation. -/ deviationFactor :
    Fraction.Rational
  /-- The retained centered-deviation sensitivity factor is strictly positive. -/ deviationFactorPositive : 0 <
    deviationFactor
  /-- Squared-deviation separation is bounded by its retained factor times squared chordal distance. -/
    deviationSensitive : ∀ left right,
    Distance.rationalSeparation
        (Function.Rat.poweredDeviationProbe probe
          ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 left)
        (Function.Rat.poweredDeviationProbe probe
          ((CCL.Prefix.PrefixFamilyProcess.witnessProbeExpectation process) distribution probe) 2 right) ≤
      deviationFactor * Chordal.Basic.chordalSq left right

constructive_injectivity ProbeCenteredVarianceProcessData

namespace ProbeCenteredVarianceProcessData

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Construct the centered variance bound process from the exact retained sensitivity certificate. -/
@[expose] def toBoundProcess {ι : Type} {process :
  Cylinder.PrefixFamilyProcess ι}
    {distribution : Measure.Distribution ι}
    {probe : Line.GaussianLine → Fraction.Rational}
    (data : CCL.Prefix.ProbeCenteredVarianceProcessData process distribution probe) :
    Approximation.BoundProcess :=
  (CCL.Prefix.PrefixFamilyProcess.toProbeCenteredVarianceProcess process) distribution probe data.meanFactor
    data.meanFactorPositive data.meanSensitive data.deviationFactor
    data.deviationFactorPositive data.deviationSensitive

end ProbeCenteredVarianceProcessData

namespace PrefixFamilyProcess
end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
