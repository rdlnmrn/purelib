module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.ProjectiveObservation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Basic
public import Purelib.Measure.CCL.Prefix.ProjectiveEnclosure
import Purelib.Measure.Distribution.Basic

public import Purelib.Approximation.CCL.EncodedPrefix.Observation
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Gaussian.Basic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)

section
@[expose] public section

/-!
# Finite measure certificates emitted by the executable CCL encoder

This module is the concrete bridge from `Purelib.CCL.Encoding.Encoder.encodeBlocks` to the
projectively rescaled prefix-measure facade.  It packages each finite encoder
result as an inhabited rational enclosure and lifts a finite input table to a
finite expectation enclosure.

The reconstructed affine input is used only through the encoder's explicit
finite projective-equivalence proof.  No quotient representative is chosen.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The encoded-prefix family interval contains the original expected probe value at the exact encoder witness points.

Each original fraction has nonzero numerator, and the shared nonnegative sensitivity bound controls its retained
projective-prefix probe interval. -/
theorem encodedProjectivePrefixExpectationBound_contains_points {ι : Type}
    (distribution : Measure.Distribution ι)
    (fraction : ι → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (CCL.Prefix.projectivePrefixFamilyProbeExpectationBound
      (Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun item =>
          probe (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point) := by
  have inside := CCL.Prefix.projectivePrefixFamilyProbeExpectationBound_contains
    (Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution distribution fraction
      numeratorNonzero)
    probe factor factorNonnegative sensitive
    (fun certificate => certificate.witness)
    (by
      intro atom member
      exact atom.item.witnessRealizes)
  rw [Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution, distribution.map_expectation]
    at inside
  exact inside

/-- The encoded-prefix family interval contains the original expected probe value at the affine values of the same
fractions. -/
theorem encodedProjectivePrefixExpectationBound_contains_values {ι : Type}
    (distribution : Measure.Distribution ι)
    (fraction : ι → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (CCL.Prefix.projectivePrefixFamilyProbeExpectationBound
      (Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun item =>
          probe (Line.Proj.affine (fraction item).value)) := by
  have inside := encodedProjectivePrefixExpectationBound_contains_points
    distribution fraction numeratorNonzero probe factor factorNonnegative
      sensitive
  have expectationEqual :
      distribution.expectation (fun item =>
          probe (Encoder.Blocks.encodeBlocks
            (fraction item) (numeratorNonzero item)).point) =
        distribution.expectation (fun item =>
          probe (Line.Proj.affine (fraction item).value)) := by
    exact distribution.expectation_congr _ _ (fun item =>
      Chordal.Probe.probe_eq_of_projectiveEquivalent probe factor sensitive
        (Encoder.Blocks.encodeBlocks_reconstruct
          (fraction item) (numeratorNonzero item)))
  rw [expectationEqual] at inside
  exact inside

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Sufficient block counts for every original atom's exact encoding make the probe-expectation interval narrower than
the positive target. -/
theorem encodedProjectivePrefixExpectationBound_width_lt_requested {ι : Type}
    (distribution : Measure.Distribution ι)
    (fraction : ι → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length) :
    (CCL.Prefix.projectivePrefixFamilyProbeExpectationBound
      (Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution distribution fraction
        numeratorNonzero)
      probe factor factorPositive.le sensitive).width < target := by
  have halfPositive : (0 : Fraction.Rational) < target / 2 :=
    Fraction.Order.Field.div_pos_direct targetPositive (by decide)
  have halfSmall : target / 2 < target := by
    apply (Fraction.Order.Field.div_lt_iff_pos
      (by decide : (0 : Fraction.Rational) < 2)).2
    calc
      target = target * 1 := by ring1
      _ < target * 2 :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          targetPositive (by decide)
  rw [CCL.Prefix.projectivePrefixFamilyProbeExpectationBound_width,
    Approximation.CCL.EncodedPrefix.encodedProjectivePrefixDistribution, distribution.map_expectation]
  calc
    distribution.expectation (fun item =>
          2 * (factor * Approximation.CCL.Cylinder.cylinderSpread
            (Cylinder.encodedProjectivePrefixCertificate
              (fraction item) (numeratorNonzero item)).blocks)) ≤
        distribution.expectation (fun _ => target / 2) := by
      apply distribution.expectation_mono
      intro atom member
      have widthSmall := Approximation.CCL.Prefix.completedProjectivePrefixProbeBound_width_lt_requested
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).point
        (Encoder.Blocks.encodeBlocks_realizes (fraction atom.item)
          (numeratorNonzero atom.item))
        probe factor factorPositive sensitive (target / 2) halfPositive
        (enough atom member)
      rw [Approximation.CCL.Prefix.completedProjectivePrefixProbeBound_width] at widthSmall
      exact widthSmall.le
    _ = target / 2 := distribution.expectation_constant _
    _ < target := halfSmall

end Purelib.Measure.CCL.EncodedPrefix

end
