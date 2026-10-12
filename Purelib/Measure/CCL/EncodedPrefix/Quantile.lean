module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Measure.CCL.EncodedPrefix.Law
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Median.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Quantile.Stability
import Purelib.Measure.Distribution.Quantile.Equivalence
import Purelib.Measure.Distribution.Median.Equivalence
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Quantile.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.CCL.Encoding.Cylinder.Projective (ProjectiveRealizes)
open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)
open Purelib.Geometry.Projective.Chordal.Probe (SquaredProbeSensitive)

section
/-!
# Quantile stability from finite squared-sensitive CCL prefixes

Uniform finite CCL cylinder contraction controls executable lower quantiles
of squared-sensitive rational probes.  The result is a direct finite
pushforward theorem at a displayed rational quantile level; no limiting law,
infimum, or completed real value is introduced.
-/

@[expose] public section

namespace Purelib.Measure.CCL.EncodedPrefix
namespace PrefixFamilyProcess
end PrefixFamilyProcess

/-! ## Actual executable encoder tables -/

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Encoder and affine laws of a squared-sensitive probe have the same lower quantile at every level in `(0, 1]`. -/
theorem encodedSquaredSensitiveProbe_lowerQuantile_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    (distribution.map fun item => probe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).lowerQuantile
          level levelPositive levelAtMostOne =
      (distribution.map fun item =>
        probe (Line.Proj.affine (fraction item).value)).lowerQuantile
          level levelPositive levelAtMostOne :=
  (CCL.EncodedPrefix.encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
    fraction numeratorNonzero probe factor sensitive).lowerQuantile_eq
      level levelPositive levelAtMostOne

/-- Encoder and affine laws of a squared-sensitive probe have the same median. -/
theorem encodedSquaredSensitiveProbe_median_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : SquaredProbeSensitive probe factor) :
    (distribution.map fun item => probe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).median =
      (distribution.map fun item =>
        probe (Line.Proj.affine (fraction item).value)).median :=
  (CCL.EncodedPrefix.encodedSquaredSensitiveProbeLaw_evaluationEquivalent distribution
    fraction numeratorNonzero probe factor sensitive).median_eq

/-- The encoded omega-probe lower quantile equals the affine-value quantile at the same valid level. -/
theorem encodedChordalOmegaProbe_lowerQuantile_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).lowerQuantile
          level levelPositive levelAtMostOne =
      (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value)).lowerQuantile
          level levelPositive levelAtMostOne :=
  encodedSquaredSensitiveProbe_lowerQuantile_eq_values distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 Chordal.Probe.chordalOmegaProbe_squaredSensitive
      level levelPositive levelAtMostOne

end

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The encoded omega-probe median equals the affine-value median. -/
theorem encodedChordalOmegaProbe_median_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point).median =
      (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value)).median :=
  encodedSquaredSensitiveProbe_median_eq_values distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 Chordal.Probe.chordalOmegaProbe_squaredSensitive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Sufficient encoded blocks bound a realizing probe law's lower-quantile error by the requested epsilon.

The probe has positive squared-sensitivity factor, the level lies in `(0, 1]`, and each retained atom's point realizes
the exact fraction encoding used for the block budget. -/
theorem encodedSquaredProbe_lowerQuantile_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun item => probe (points item)).lowerQuantile
          level levelPositive levelAtMostOne)
        ((distribution.map fun item =>
          probe (Line.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon := by
  apply distribution.map_lowerQuantile_rationalSeparation_le
  intro atom member
  let encoding := Encoder.Blocks.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (Line.Proj.affine (fraction atom.item).value) :=
    Chordal.Probe.squaredSensitive_probe_eq_of_projectiveEquivalent probe factor sensitive
      encoding.realizes.valid
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
        (fraction atom.item).value)
      encoding.reconstruct
  rw [← probeEqual]
  exact (Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_separation_lt_of_requested
    (pointsRealize atom member) encoding.realizes
    probe factor factorPositive sensitive epsilon epsilonPositive
    (enough atom member)).le

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The requested squared-probe block budget bounds the realizing and affine laws' median separation by epsilon. -/
theorem encodedSquaredProbe_median_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.map fun item => probe (points item)).median
        (distribution.map fun item =>
          probe (Line.Proj.affine (fraction item).value)).median ≤ epsilon := by
  simpa only [Distribution.median] using
    encodedSquaredProbe_lowerQuantile_separation_le_requested distribution
      fraction numeratorNonzero probe factor factorPositive sensitive
      epsilon epsilonPositive enough points pointsRealize
      (1 / 2) (by decide) (by decide)

/-- The requested omega-probe block budget bounds realizing and affine lower-quantile separation by epsilon. -/
theorem encodedChordalOmegaProbe_lowerQuantile_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (level : Fraction.Rational) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    Distance.rationalSeparation
        ((distribution.map fun item =>
          Chordal.Probe.chordalOmegaProbe (points item)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun item => Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon :=
  encodedSquaredProbe_lowerQuantile_separation_le_requested distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize level levelPositive levelAtMostOne

/-- The requested omega-probe block budget bounds realizing and affine median separation by epsilon. -/
theorem encodedChordalOmegaProbe_median_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.map fun item => Chordal.Probe.chordalOmegaProbe (points item)).median
        (distribution.map fun item => Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction item).value)).median ≤ epsilon :=
  encodedSquaredProbe_median_separation_le_requested distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize

end Purelib.Measure.CCL.EncodedPrefix

end
