module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.EncodedPrefix.Sensitivity
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Equivalence
public import Purelib.Measure.Distribution.Kolmogorov.Basic

public import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.GaussianInt.Basic
import Purelib.Measure.Distribution.Expectation

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)
open Purelib.Geometry.Projective.Chordal.Probe (SquaredProbeSensitive)

section
@[expose] public section

/-!
# Root-free L2 stability for actual finite CCL encoder tables

This module applies squared-probe prefix stability directly to the block lists
and projective realization certificates computed by `encodeBlocks`.  The
comparison target is the original affine Gaussian fraction, connected to the
computed homogeneous witness by the encoder's explicit reconstruction proof.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- A squared-sensitive probe has the same expectation on encoder points and the original affine fraction values. -/
theorem encodedSquaredSensitiveProbe_expectation_eq_values {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor) :
    distribution.expectation (fun item =>
        probe (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.expectation (fun item =>
        probe (Line.Proj.affine (fraction item).value)) := by
  exact distribution.expectation_congr _ _ (fun item =>
    Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)

section
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Encoder-point and affine-value laws of a squared-sensitive probe are evaluation-equivalent. -/
theorem encodedSquaredSensitiveProbeLaw_evaluationEquivalent {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor) :
    Distribution.EvaluationEquivalent
      (distribution.map fun item =>
        probe (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
      (distribution.map fun item =>
        probe (Line.Proj.affine (fraction item).value)) := by
  have lawsEqual := distribution.map_congr
    (fun item => probe (Encoder.Blocks.encodeBlocks
      (fraction item) (numeratorNonzero item)).point)
    (fun item => probe (Line.Proj.affine (fraction item).value))
    (fun item => Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)
  rw [lawsEqual]
  exact Distribution.EvaluationEquivalent.refl _

/-- Every rational event has equal probe probability on encoder points and affine fraction values. -/
theorem encodedSquaredSensitiveProbe_eventProbability_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor)
    (event : Fraction.Rational → Bool) :
    distribution.probability (fun item => event (probe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.probability (fun item => event
        (probe (Line.Proj.affine (fraction item).value))) := by
  calc
    distribution.probability (fun item => event (probe
          (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point)) =
        (distribution.map fun item => probe
          (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point).probability event :=
      (distribution.map_probability _ event).symm
    _ = (distribution.map fun item =>
          probe (Line.Proj.affine (fraction item).value)).probability event :=
      (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
        fraction numeratorNonzero probe factor sensitive).probability_eq event
    _ = distribution.probability (fun item => event
          (probe (Line.Proj.affine (fraction item).value))) :=
      distribution.map_probability _ event

/-- Every rational observable has equal probe expectation on encoder points and affine fraction values. -/
theorem encodedSquaredSensitiveProbe_observableExpectation_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor)
    (observable : Fraction.Rational → Fraction.Rational) :
    distribution.expectation (fun item => observable (probe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.expectation (fun item => observable
        (probe (Line.Proj.affine (fraction item).value))) := by
  calc
    distribution.expectation (fun item => observable (probe
          (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point)) =
        (distribution.map fun item => probe
          (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point).expectation
              observable :=
      (distribution.map_expectation _ observable).symm
    _ = (distribution.map fun item =>
          probe (Line.Proj.affine (fraction item).value)).expectation
            observable :=
      (encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
        fraction numeratorNonzero probe factor sensitive).expectation_eq
          observable
    _ = distribution.expectation (fun item => observable
          (probe (Line.Proj.affine (fraction item).value))) :=
      distribution.map_expectation _ observable

end

open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The exact encoder omega-probe law is evaluation-equivalent to the original affine-value law. -/
theorem encodedChordalOmegaProbeLaw_evaluationEquivalent {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    Distribution.EvaluationEquivalent
      (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
      (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value)) :=
  encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 Chordal.Probe.chordalOmegaProbe_squaredSensitive

open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- An omega-probe event has the same probability on encoder points and affine values. -/
theorem encodedChordalOmegaProbe_eventProbability_eq_values {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (event : Fraction.Rational → Bool) :
    distribution.probability (fun item => event (Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.probability (fun item => event (Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value))) :=
  encodedSquaredSensitiveProbe_eventProbability_eq_values distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2
    Chordal.Probe.chordalOmegaProbe_squaredSensitive event

/-- Every rational observable of the omega probe has the same expectation on encoder points and affine values. -/
theorem encodedChordalOmegaProbe_observableExpectation_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (observable : Fraction.Rational → Fraction.Rational) :
    distribution.expectation (fun item => observable (Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)) =
      distribution.expectation (fun item => observable (Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value))) :=
  encodedSquaredSensitiveProbe_observableExpectation_eq_values distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2
    Chordal.Probe.chordalOmegaProbe_squaredSensitive observable
end

end Purelib.Measure.CCL.EncodedPrefix

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

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Push the original finite law forward by the omega probe of each exact encoded fraction point.

Each fraction retains its supplied nonzero-numerator certificate; the map preserves the original weighted occurrences.
-/
def encodedChordalOmegaProbeLaw {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    Measure.Distribution Fraction.Rational :=
  distribution.map fun item => Chordal.Probe.chordalOmegaProbe
    (Encoder.Blocks.encodeBlocks
      (fraction item) (numeratorNonzero item)).point

open Purelib
open Purelib.Data
open Purelib.Measure
/-- The exact encoded omega-probe law equals the original affine-value omega-probe law. -/
theorem encodedChordalOmegaProbeLaw_eq_affine {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero =
      Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction := by
  unfold encodedChordalOmegaProbeLaw Distribution.Projective.Chordal.affineChordalOmegaProbeLaw
  exact distribution.map_congr _ _ (fun item =>
    Approximation.CCL.EncodedPrefix.encodedChordalOmegaProbe_eq_value (fraction item)
      (numeratorNonzero item))

/-- The encoded and affine omega-probe laws have zero Kolmogorov distance. -/
theorem encodedChordalOmegaProbeLaw_kolmogorovDistance_affine_eq_zero
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    Distribution.kolmogorovDistance
      (encodedChordalOmegaProbeLaw distribution fraction numeratorNonzero)
      (Distribution.Projective.Chordal.affineChordalOmegaProbeLaw distribution fraction) = 0 := by
  rw [encodedChordalOmegaProbeLaw_eq_affine distribution fraction
    numeratorNonzero]
  exact Distribution.kolmogorovDistance_refl _
end Purelib.Measure.CCL.EncodedPrefix

end

end
