module
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Approximation.CCL.EncodedPrefix.Sensitivity
import Purelib.Approximation.CCL.Prefix.SquaredSensitivity
public import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Projective
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Distance.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Moments.Stability
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

@[expose] public section

/-!
# Variance stability for actual finite CCL encoder tables

Uniform squared-sensitive prefix contraction controls not only expectations
but, for unit-interval probes, exact finite variances.  The concrete
distance-to-`omega` probe supplies its own `[0, 1]` range proof.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- A squared-sensitive probe has equal variance on exact encoder points and affine fraction values. -/
theorem encodedSquaredSensitiveProbe_variance_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor) :
    distribution.variance (fun item => probe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.variance (fun item =>
        probe (Line.Proj.affine (fraction item).value)) := by
  exact distribution.variance_congr _ _ (fun item =>
    Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction item)
      (numeratorNonzero item) probe factor sensitive)

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The omega probe has equal variance on exact encoder points and affine fraction values. -/
theorem encodedChordalOmegaProbe_variance_eq_values
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe
        (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point) =
      distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe
        (Line.Proj.affine (fraction item).value)) :=
  CCL.EncodedPrefix.encodedSquaredSensitiveProbe_variance_eq_values distribution fraction
    numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 Chordal.Probe.chordalOmegaProbe_squaredSensitive

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The requested block budget bounds realizing and affine probe variances' separation by four times epsilon.

Both probe families lie in the unit interval on the original atoms, and each realizing point retains the corresponding
fraction's exact encoded blocks. -/
theorem encodedSquaredProbe_variance_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → CCL.Measure.Coordinate) (factor : CCL.Measure.Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor)
    (epsilon : CCL.Measure.Coordinate) (epsilonPositive : 0 < epsilon)
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
    (pointsRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ probe (points atom.item) ∧ probe (points atom.item) ≤ 1)
    (valuesRange : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ probe (Line.Proj.affine (fraction atom.item).value) ∧
        probe (Line.Proj.affine (fraction atom.item).value) ≤ 1) :
    Distance.rationalSeparation
        (distribution.variance fun item => probe (points item))
        (distribution.variance fun item =>
          probe (Line.Proj.affine (fraction item).value)) ≤ 4 * epsilon := by
  apply distribution.variance_rationalSeparation_le_of_unitInterval
    (fun item => probe (points item))
    (fun item => probe (Line.Proj.affine (fraction item).value)) epsilon
    pointsRange valuesRange
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

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested omega-probe block budget bounds realizing and affine variance separation by four times epsilon. -/
theorem encodedChordalOmegaProbe_variance_separation_le_requested
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (epsilon : CCL.Measure.Coordinate) (epsilonPositive : 0 < epsilon)
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
        (distribution.variance fun item => Chordal.Probe.chordalOmegaProbe (points item))
        (distribution.variance fun item => Chordal.Probe.chordalOmegaProbe
          (Line.Proj.affine (fraction item).value)) ≤ 4 * epsilon := by
  apply CCL.EncodedPrefix.encodedSquaredProbe_variance_separation_le_requested distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough
    points pointsRealize
  · intro atom member
    exact ⟨Chordal.Probe.chordalOmegaProbe_nonnegative (points atom.item),
      Chordal.Probe.chordalOmegaProbe_le_one (pointsRealize atom member).valid⟩
  · intro atom member
    exact ⟨Chordal.Probe.chordalOmegaProbe_nonnegative
        (Line.Proj.affine (fraction atom.item).value),
      Chordal.Probe.chordalOmegaProbe_le_one
        (Line.Gaussian.Proj.affine_hasNonzeroCoordinate
          (fraction atom.item).value)⟩

end Purelib.Measure.CCL.EncodedPrefix
