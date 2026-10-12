module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.EncodedPrefix.Sensitivity
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.List.Map
import Purelib.Data.Rat.Distance.Power
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.EncodedPrefix.Threshold
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
public import Purelib.Measure.Distribution.Sampling.ThresholdGrid
import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Distribution.Sampling.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)
open Purelib.Measure.Distribution.Projective.Chordal (EncodedChordalOmegaThresholdGridTargetWithin)

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

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Outside the encoder's grid-deviation event, every listed threshold satisfies the squared frequency-error bound
against the affine target. -/
theorem encodedChordalOmegaThresholdGridTargetAccurate_of_outside_encoder
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (thresholds : List Fraction.Rational) (count : Nat)
    (tolerance : Fraction.Rational) (sample : List index)
    (outside : Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample = false) :
    Distribution.Projective.Chordal.EncodedChordalOmegaThresholdGridTargetAccurate distribution fraction
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample := by
  have encodedAccurate :=
    distribution.eventFamilyFrequenciesAccurate_of_outside
      (Distribution.Sampling.encodedChordalOmegaThresholdEvents
        (fun item => (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        thresholds) count tolerance sample outside
  intro threshold member
  let encodedEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point
  let exactEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)
  have eventMember : encodedEvent ∈ Distribution.Sampling.encodedChordalOmegaThresholdEvents
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point) thresholds := by
    unfold Distribution.Sampling.encodedChordalOmegaThresholdEvents encodedEvent
    exact Map.mem_map.mpr ⟨threshold, member, rfl⟩
  have close := encodedAccurate encodedEvent eventMember
  have probabilityEqual : distribution.probability encodedEvent =
      distribution.probability exactEvent := by
    apply distribution.probability_congr
    intro item
    unfold encodedEvent exactEvent Measure.atLeastEvent
    change decide (threshold ≤ Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      decide (threshold ≤ Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value))
    rw [Approximation.CCL.EncodedPrefix.encodedChordalOmegaProbe_eq_value]
  rw [probabilityEqual] at close
  exact close

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- A positive tolerance turns encoder grid accuracy into strict frequency separation from every affine threshold
target. -/
theorem encodedChordalOmegaThresholdGridTargetWithin_of_outside_encoder
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (thresholds : List Fraction.Rational) (count : Nat)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside : Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetWithin distribution fraction
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds count tolerance sample := by
  have squared :=
    encodedChordalOmegaThresholdGridTargetAccurate_of_outside_encoder
      distribution fraction numeratorNonzero thresholds count tolerance
      sample outside
  intro threshold member
  apply Distance.rationalSeparation_lt_of_sq_lt_sq
    tolerancePositive
  rw [Distance.NaturalLp.rationalSeparation_sq]
  exact squared threshold member

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Certify the encoder threshold grid's requested failure probability and strict accuracy outside its deviation event.

The certificate uses the exact encoded points and the requested sample count for the retained threshold list; positive
tolerance and failure are required. -/
theorem encodedChordalOmegaThresholdGrid_encoderCertificate_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (thresholds : List Fraction.Rational)
    (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (failure : Fraction.Rational) (failurePositive : 0 < failure) :
    let points : index → Line.GaussianLine := fun item =>
      (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point
    let count := Distribution.Sampling.requiredEncodedChordalOmegaThresholdGridSampleCount points
      thresholds tolerance failure
    (distribution.iidSamples count).probability
        (Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution points
          thresholds count tolerance) < failure ∧
      ∀ sample, Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution points
          thresholds count tolerance sample = false →
        EncodedChordalOmegaThresholdGridTargetWithin distribution fraction
          points thresholds count tolerance sample := by
  dsimp only
  constructor
  · exact Distribution.Sampling.encodedChordalOmegaThresholdGrid_deviationProbability_lt_requested
      distribution
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)
      thresholds tolerance tolerancePositive failure failurePositive
  · intro sample outside
    exact encodedChordalOmegaThresholdGridTargetWithin_of_outside_encoder
      distribution fraction numeratorNonzero thresholds
      (Distribution.Sampling.requiredEncodedChordalOmegaThresholdGridSampleCount
        (fun item => (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        thresholds tolerance failure)
      tolerance tolerancePositive sample outside

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Outside a realizing family's grid-deviation event, the margin budget gives squared accuracy against every affine
threshold target.

The same positive margin resolves all retained thresholds on every original atom, using that atom's exact fraction
encoding and retained block count. -/
theorem encodedChordalOmegaThresholdGridTargetAccurate_of_outside
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Fraction.Rational)
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) ∨
          Chordal.Probe.chordalOmegaProbe
              (Line.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Fraction.Rational) (sample : List index)
    (outside : Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution points
      thresholds count tolerance sample = false) :
    Distribution.Projective.Chordal.EncodedChordalOmegaThresholdGridTargetAccurate distribution fraction
      points thresholds count tolerance sample := by
  have realizedAccurate :=
    distribution.eventFamilyFrequenciesAccurate_of_outside
      (Distribution.Sampling.encodedChordalOmegaThresholdEvents points thresholds)
      count tolerance sample outside
  intro threshold member
  let realizedEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (points item)
  let exactEvent : index → Bool :=
    Measure.atLeastEvent threshold fun item =>
      Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)
  have eventMember : realizedEvent ∈
      Distribution.Sampling.encodedChordalOmegaThresholdEvents points thresholds := by
    unfold Distribution.Sampling.encodedChordalOmegaThresholdEvents realizedEvent
    exact Map.mem_map.mpr ⟨threshold, member, rfl⟩
  have close := realizedAccurate realizedEvent eventMember
  have probabilityEqual : distribution.probability realizedEvent =
      distribution.probability exactEvent :=
    CCL.EncodedPrefix.encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
      distribution fraction numeratorNonzero threshold margin marginPositive
      (separated threshold member) enough points pointsRealize
  rw [probabilityEqual] at close
  exact close

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Positive tolerance and the common margin budget give strict affine-target accuracy outside the realizing
grid-deviation event. -/
theorem encodedChordalOmegaThresholdGridTargetWithin_of_outside
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Fraction.Rational)
    (margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) ∨
          Chordal.Probe.chordalOmegaProbe
              (Line.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Fraction.Rational) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside : Distribution.Sampling.encodedChordalOmegaThresholdGridDeviation distribution points
      thresholds count tolerance sample = false) :
    EncodedChordalOmegaThresholdGridTargetWithin distribution fraction points
      thresholds count tolerance sample := by
  have squared :=
    encodedChordalOmegaThresholdGridTargetAccurate_of_outside distribution
      fraction numeratorNonzero points pointsRealize thresholds margin
      marginPositive separated enough count tolerance sample outside
  intro threshold member
  apply Distance.rationalSeparation_lt_of_sq_lt_sq
    tolerancePositive
  rw [Distance.NaturalLp.rationalSeparation_sq]
  exact squared threshold member

end Purelib.Measure.CCL.EncodedPrefix

end
