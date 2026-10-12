module
import Purelib.Data.Rat.Fraction
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.EncodedPrefix.Sensitivity
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Weighted.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.Comparison
import Purelib.Measure.Distribution.AlmostEverywhere
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.CCL.Encoding.Block.Basic
import Mathlib.Order.Basic

section
public section

/-!
# Root-free L2 stability for actual finite CCL encoder tables

This module applies squared-probe prefix stability directly to the block lists
and projective realization certificates computed by `encodeBlocks`.  The
comparison target is the original affine Gaussian fraction, connected to the
computed homogeneous witness by the encoder's explicit reconstruction proof.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The squared-L2 probe error between retained realizations and original fraction values is bounded by expected
sensitivity-scaled cylinder spread.

Each original atom retains its exact nonzero-numerator encoding and projective realization; the same squared-sensitivity
certificate controls every pair. -/
theorem encodedSquaredProbe_poweredL2Distance_values_le {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.poweredL2Distance
        (fun item => probe (points item))
        (fun item => probe (Line.Proj.affine (fraction item).value)) ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread
          (Encoder.Blocks.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  change distribution.expectation (fun item =>
      (probe (points item) -
        probe (Line.Proj.affine (fraction item).value)) ^ 2) ≤
    distribution.expectation fun item =>
      factor * Approximation.CCL.Cylinder.cylinderSpread
        (Encoder.Blocks.encodeBlocks (fraction item)
          (numeratorNonzero item)).blocks
  apply distribution.expectation_mono
  intro atom member
  let encoding := Encoder.Blocks.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (Line.Proj.affine (fraction atom.item).value) :=
    Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction atom.item)
      (numeratorNonzero atom.item) probe factor sensitive
  rw [← probeEqual, ← Distance.NaturalLp.rationalSeparation_sq]
  exact Approximation.CCL.Prefix.projectiveRealized_probe_separation_sq_le
    (pointsRealize atom member) encoding.realizes probe factor
      factorNonnegative sensitive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The required block count makes the exact realized probe value at each retained atom lie within the positive
tolerance of its original fraction value. -/
theorem encodedSquaredProbe_separation_lt_requested_on_atom {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (atom : Measure.Weighted index)
    (member : atom ∈ distribution.atoms) :
    Distance.rationalSeparation
        (probe (points atom.item))
        (probe (Line.Proj.affine (fraction atom.item).value)) < epsilon := by
  let encoding := Encoder.Blocks.encodeBlocks (fraction atom.item)
    (numeratorNonzero atom.item)
  have probeEqual : probe encoding.point =
      probe (Line.Proj.affine (fraction atom.item).value) :=
    Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction atom.item)
      (numeratorNonzero atom.item) probe factor sensitive
  rw [← probeEqual]
  exact Approximation.CCL.Prefix.projectiveRealizedSquaredProbe_separation_lt_of_requested
    (pointsRealize atom member) encoding.realizes probe factor factorPositive
    sensitive epsilon epsilonPositive (enough atom member)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Sufficient original block counts make the probe-versus-fraction-value separation event have probability zero. -/
theorem encodedSquaredProbe_separationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
      (Measure.separationAtLeast epsilon
        (fun item => probe (points item))
        (fun item =>
          probe (Line.Proj.affine (fraction item).value))) = 0 := by
  calc
    distribution.probability
        (Measure.separationAtLeast epsilon
          (fun item => probe (points item))
          (fun item =>
            probe (Line.Proj.affine (fraction item).value))) =
        distribution.probability (fun _ => false) := by
      apply distribution.probability_congr_off_zero
      intro atom member
      apply Or.inr
      unfold Measure.separationAtLeast
      apply decide_eq_false_iff_not.mpr
      exact not_le_of_gt
        (CCL.EncodedPrefix.encodedSquaredProbe_separation_lt_requested_on_atom distribution
          fraction numeratorNonzero probe factor factorPositive sensitive
          epsilon epsilonPositive enough points pointsRealize atom member)
    _ = 0 := distribution.probability_false

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Squared separation of the two original probe expectations is at most the expected sensitivity-scaled encoding
spread. -/
theorem encodedSquaredProbe_expectation_separation_sq_le {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item =>
          probe (Line.Proj.affine (fraction item).value)) ^ 2 ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread
          (Encoder.Blocks.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  exact (distribution.expectation_separation_sq_le_poweredL2Distance
    (fun item => probe (points item))
    (fun item => probe (Line.Proj.affine (fraction item).value))).trans
      (CCL.EncodedPrefix.encodedSquaredProbe_poweredL2Distance_values_le distribution fraction
        numeratorNonzero probe factor factorNonnegative sensitive points
        pointsRealize)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Sufficient block counts at every original atom make realized and fraction-value probe expectations closer than the
positive tolerance. -/
theorem encodedSquaredProbe_expectation_separation_lt_requested {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon factor ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item =>
          probe (Line.Proj.affine (fraction item).value)) < epsilon := by
  have poweredL2Le := CCL.EncodedPrefix.encodedSquaredProbe_poweredL2Distance_values_le
    distribution fraction numeratorNonzero probe factor factorPositive.le
    sensitive points pointsRealize
  have budgetLe : distribution.expectation (fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread
          (Encoder.Blocks.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks) ≤ epsilon ^ 2 / 2 := by
    calc
      distribution.expectation (fun item =>
            factor * Approximation.CCL.Cylinder.cylinderSpread
              (Encoder.Blocks.encodeBlocks (fraction item)
                (numeratorNonzero item)).blocks) ≤
          distribution.expectation (fun _ => epsilon ^ 2 / 2) := by
        apply distribution.expectation_mono
        intro atom member
        exact Approximation.CCL.Prefix.scaledCylinderSpread_le_half_sq_of_requested epsilon factor
          epsilonPositive factorPositive (enough atom member)
      _ = epsilon ^ 2 / 2 := distribution.expectation_constant _
  have poweredL2Small := poweredL2Le.trans_lt
    (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))
  exact distribution.expectation_separation_lt_of_poweredL2Distance_lt_sq
    (fun item => probe (points item))
    (fun item => probe (Line.Proj.affine (fraction item).value))
    epsilon epsilonPositive poweredL2Small

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The chordal omega probe's realized-versus-fraction separation event has probability zero at the requested block
count. -/
theorem encodedChordalOmegaProbe_separationProbability_eq_zero_of_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    distribution.probability
      (Measure.separationAtLeast epsilon
        (fun item => Chordal.Probe.chordalOmegaProbe (points item))
        (fun item => Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction item).value))) = 0 :=
  CCL.EncodedPrefix.encodedSquaredProbe_separationProbability_eq_zero_of_requested distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough points
    pointsRealize

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Squared separation of the original chordal omega expectations is at most the expectation of twice the exact encoding
spread. -/
theorem encodedChordalOmegaProbe_expectation_separation_sq_le {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => Chordal.Probe.chordalOmegaProbe (points item))
        (distribution.expectation fun item =>
          Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)) ^ 2 ≤
      distribution.expectation fun item =>
        2 * Approximation.CCL.Cylinder.cylinderSpread
          (Encoder.Blocks.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks :=
  CCL.EncodedPrefix.encodedSquaredProbe_expectation_separation_sq_le distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive points pointsRealize

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested original block counts make the two chordal omega expectations closer than the positive tolerance. -/
theorem encodedChordalOmegaProbe_expectation_separation_lt_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : Fraction.Rational) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredSquaredProbeBlockCount epsilon 2 ≤
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => Chordal.Probe.chordalOmegaProbe (points item))
        (distribution.expectation fun item =>
          Chordal.Probe.chordalOmegaProbe (Line.Proj.affine (fraction item).value)) < epsilon :=
  CCL.EncodedPrefix.encodedSquaredProbe_expectation_separation_lt_requested distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize

end Purelib.Measure.CCL.EncodedPrefix

end
