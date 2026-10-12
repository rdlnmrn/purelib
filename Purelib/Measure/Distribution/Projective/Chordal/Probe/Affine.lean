module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Measure.Coupling.Basic
public import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalOrder
public import Purelib.Measure.Sampling.Statistic
import Purelib.Measure.Weighted.Integral

import Purelib.Geometry.Projective.Line.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)

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

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Average the chordal omega probe of the exact original fraction values embedded as affine projective points. -/
def encodedChordalOmegaExactExpectation {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias) : Fraction.Rational :=
  distribution.expectation fun item =>
    Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Select samples whose observed-point chordal omega mean is separated from the exact fraction-value expectation by at
least epsilon. -/
def encodedChordalOmegaSampleMeanTargetDeviation {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (count : Nat) (points : index → Line.GaussianLine)
    (epsilon : Fraction.Rational) : List index → Bool :=
  fun sample => decide (epsilon ≤
    Distance.rationalSeparation
      (Distribution.sampleMean count
        (fun item => Chordal.Probe.chordalOmegaProbe (points item)) sample)
      (encodedChordalOmegaExactExpectation distribution fraction))
end Purelib.Measure.Distribution.Projective.Chordal

end

section
@[expose] public section

/-!
# Simultaneous finite CCL threshold-frequency estimation

One finite iid sample of a compatible realization table can estimate a
displayed list of chordal threshold probabilities simultaneously.  A common
positive witness margin identifies each encoded threshold probability with
the exact probability computed from the original affine Gaussian inputs.
The result is a finite survival-function grid certificate; no continuum of
thresholds or infinite sample stream is introduced.
-/

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Require squared frequency error below tolerance squared at every retained threshold relative to original affine
fraction-value probabilities. -/
def EncodedChordalOmegaThresholdGridTargetAccurate {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias) (points : index →
      Line.GaussianLine)
    (thresholds : List Fraction.Rational) (count : Nat)
    (tolerance : Fraction.Rational) (sample : List index) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    (Distribution.eventFrequency count
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (points item)) sample -
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction item).value))) ^ 2 < tolerance ^ 2

/-- Require strict frequency separation below tolerance at every retained threshold relative to original affine
fraction-value probabilities. -/
def EncodedChordalOmegaThresholdGridTargetWithin {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias) (points : index →
      Line.GaussianLine)
    (thresholds : List Fraction.Rational) (count : Nat)
    (tolerance : Fraction.Rational) (sample : List index) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    Distance.rationalSeparation
      (Distribution.eventFrequency count
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (points item)) sample)
      (distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction item).value))) < tolerance
end Purelib.Measure.Distribution.Projective.Chordal

end

section
@[expose] public section

/-!
# Finite frequency estimation of CCL threshold events

A displayed rational margin makes the threshold decision of every compatible
CCL realization equal to the decision on the original affine input.  The
constructive Bernoulli sample-count request then estimates that exact finite
threshold probability by a finite sample frequency.
-/

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Select samples whose observed-point threshold frequency has squared error at least tolerance squared relative to the
exact affine fraction-value probability. -/
def encodedChordalOmegaThresholdFrequencyTargetDeviation {index :
  Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (count : Nat) (points : index → Line.GaussianLine)
    (threshold tolerance : Fraction.Rational) : List index → Bool :=
  fun sample => decide (tolerance ^ 2 ≤
    (Distribution.sampleMean count
        (Distribution.indicator
          (Measure.atLeastEvent threshold fun item =>
            Chordal.Probe.chordalOmegaProbe (points item))) sample -
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction item).value))) ^ 2)
end Purelib.Measure.Distribution.Projective.Chordal

end

section
@[expose] public section

/-!
# Finite transport from actual CCL encoder tables

The same displayed source row canonically couples a compatible realization
with the original affine Gaussian input.  Squared rational separation is the
transport cost, so the exact cost is the source powered-L2 distance and CCL
cylinder contraction bounds it by an executable rational prefix budget.

This is the law-level approximation appropriate to nearby unequal atoms;
total variation need not become small in that situation.  No square root,
infimum over couplings, or completed Wasserstein space is introduced.
-/

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Couple the observed-point and exact affine fraction-value probe laws using their same retained original distribution
indices.

The two pushforwards retain the original source weights, and the coupling pairs the two probe readings from each same
original item. -/
def encodedProbeLawCoupling {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (probe : Line.GaussianLine → Fraction.Rational) (points : index →
      Line.GaussianLine) :
    Measure.LawCoupling
      (distribution.map fun item => probe (points item))
      (distribution.map fun item =>
        probe (Line.Proj.affine (fraction item).value)) :=
  Coupling.Law.probeLawCoupling distribution probe points fun item =>
    Line.Proj.affine (fraction item).value

/-- Squared transport cost of the exact paired probe-law coupling equals the original squared-L2 distance between its
two probe readings. -/
theorem Probe.encodedProbeLawCoupling_squaredTransportCost {index
  : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (probe : Line.GaussianLine → Fraction.Rational) (points : index →
      Line.GaussianLine) :
    (encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) =
      distribution.poweredL2Distance
        (fun item => probe (points item))
        (fun item => probe (Line.Proj.affine (fraction item).value)) := by
  unfold encodedProbeLawCoupling Coupling.Law.probeLawCoupling
  unfold LawCoupling.transportCost
  unfold LawCoupling.ofMaps
  unfold Coupling.transportCost
  rw [distribution.map_expectation]
  change distribution.expectation (fun item =>
      Distance.rationalSeparation
        (probe (points item))
        (probe (Line.Proj.affine (fraction item).value)) ^ 2) =
    distribution.expectation (fun item =>
      (probe (points item) -
        probe (Line.Proj.affine (fraction item).value)) ^ 2)
  exact distribution.expectation_congr _ _ fun item =>
    Distance.NaturalLp.rationalSeparation_sq _ _
end Purelib.Measure.Distribution.Projective.Chordal

end

section
section
@[expose] public section

/-!
# Empirical quantiles of actual CCL encoder probes

The encoder's computed homogeneous point and its reconstructed affine input
have exactly the same chordal distance-to-`omega` value.  Consequently their
finite pushforward tables are equal, and the constructive empirical-quantile
request applies directly to samples of the encoded observable.
-/

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Push the original distribution forward to chordal omega readings of its exact affine fraction values. -/
def affineChordalOmegaProbeLaw {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias) :
    Measure.Distribution Fraction.Rational :=
  distribution.map fun item =>
    Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)
end Purelib.Measure.Distribution.Projective.Chordal

end

end
