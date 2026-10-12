module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Threshold.Squared
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalOrder

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.GaussianInt.Basic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Projective (ProjectiveRealizes)
open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)

section
@[expose] public section

/-!
# Threshold stability for squared-sensitive finite CCL probes

Discontinuous threshold events cannot be controlled from a shrinking metric
bound alone when a value may lie on the threshold.  An explicit positive
rational witness margin repairs this constructively.  Squared-probe
sensitivity then requires a finite request at `margin^2`; after that request
every compatible realization has exactly the witness's Boolean
classification, so all resulting finite probabilities are equal.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

/-! ## Concrete finite encoder-table specialization -/

section
open Purelib
open Purelib.Approximation.Rational
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Two realizations of the same fraction encodings have identical threshold-event probabilities when the encoded margin
budget is met.

The exact affine values lie at least the positive margin on either side of the threshold, and every retained atom
supplies enough blocks for the squared-sensitive probe. -/
theorem encodedSquaredProbe_thresholdProbabilities_eq_of_margin {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤
          probe (Line.Proj.affine (fraction atom.item).value) ∨
        probe (Line.Proj.affine (fraction atom.item).value) + margin ≤
          threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (leftPoints item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (rightPoints item)) := by
  apply distribution.probability_congr_off_zero
  intro atom member
  apply Or.inr
  unfold Measure.atLeastEvent
  let encoding := Encoder.Blocks.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have witnessEqual : probe encoding.point =
      probe (Line.Proj.affine (fraction atom.item).value) :=
    Chordal.Probe.squaredSensitive_probe_eq_of_projectiveEquivalent probe factor sensitive
      encoding.realizes.valid
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
        (fraction atom.item).value)
      encoding.reconstruct
  have witnessSeparated : threshold + margin ≤ probe encoding.point ∨
      probe encoding.point + margin ≤ threshold := by
    rw [witnessEqual]
    exact separated atom member
  have budgetSmall :=
    Approximation.CCL.Cylinder.scaledCylinderSpread_lt_of_requiredSquaredVarianceBlockCount_le
      (margin ^ 2) factor
      (Fraction.Order.Arithmetic.pow_pos_direct marginPositive 2)
      factorPositive (enough atom member)
  have leftEqual :=
    Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      encoding.realizes (leftRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      witnessSeparated budgetSmall
  have rightEqual :=
    Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_atLeastDecision_eq_of_margin
      encoding.realizes (rightRealizes atom member)
      probe factor factorPositive.le sensitive threshold margin marginPositive
      witnessSeparated budgetSmall
  exact leftEqual.trans rightEqual.symm

open Purelib.Measure
/-- A realizing squared-probe threshold event has the exact affine-value probability under the retained margin and block
budget. -/
theorem encodedSquaredProbe_thresholdProbability_eq_values_of_margin
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤
          probe (Line.Proj.affine (fraction atom.item).value) ∨
        probe (Line.Proj.affine (fraction atom.item).value) + margin ≤
          threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (points item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          probe (Line.Proj.affine (fraction item).value)) := by
  let encodedPoints : index → Line.GaussianLine := fun item =>
    (Encoder.Blocks.encodeBlocks (fraction item)
      (numeratorNonzero item)).point
  have compatibleEquality :=
    encodedSquaredProbe_thresholdProbabilities_eq_of_margin distribution
      fraction numeratorNonzero probe factor factorPositive sensitive
      threshold margin marginPositive separated enough points encodedPoints
      pointsRealize (by
        intro atom member
        exact Encoder.Blocks.encodeBlocks_realizes
          (fraction atom.item) (numeratorNonzero atom.item))
  calc
    distribution.probability
          (Measure.atLeastEvent threshold fun item =>
            probe (points item)) =
        distribution.probability
          (Measure.atLeastEvent threshold fun item =>
            probe (encodedPoints item)) := compatibleEquality
    _ = distribution.probability
          (Measure.atLeastEvent threshold fun item =>
            probe (Line.Proj.affine (fraction item).value)) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      unfold Measure.atLeastEvent
      change decide (threshold ≤ probe (encodedPoints atom.item)) =
        decide (threshold ≤
          probe (Line.Proj.affine (fraction atom.item).value))
      have probeEqual : probe (encodedPoints atom.item) =
          probe (Line.Proj.affine (fraction atom.item).value) :=
        Chordal.Probe.squaredSensitive_probe_eq_of_projectiveEquivalent probe factor
          sensitive
          (Encoder.Blocks.encodeBlocks (fraction atom.item)
            (numeratorNonzero atom.item)).realizes.valid
          (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
            (fraction atom.item).value)
          (Encoder.Blocks.encodeBlocks_reconstruct
            (fraction atom.item) (numeratorNonzero atom.item))
      rw [probeEqual]

/-- Two realizing omega-probe families have identical threshold-event probabilities under the retained margin and block
budget. -/
theorem encodedChordalOmegaProbe_thresholdProbabilities_eq_of_margin
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction atom.item).value) ∨
        Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → Line.GaussianLine)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (leftPoints item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (rightPoints item)) :=
  encodedSquaredProbe_thresholdProbabilities_eq_of_margin distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive threshold margin marginPositive
    separated enough leftPoints rightPoints leftRealizes rightRealizes

/-- A realizing omega-probe threshold event has the affine-value probability under the retained margin and block budget.
-/
theorem encodedChordalOmegaProbe_thresholdProbability_eq_values_of_margin
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (threshold margin : Fraction.Rational) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction atom.item).value) ∨
        Chordal.Probe.chordalOmegaProbe
            (Line.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredThresholdBlockCount margin 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (points item)) =
      distribution.probability
        (Measure.atLeastEvent threshold fun item =>
          Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)) :=
  encodedSquaredProbe_thresholdProbability_eq_values_of_margin distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive threshold margin marginPositive
    separated enough points pointsRealize

end

end Purelib.Measure.CCL.EncodedPrefix

end
