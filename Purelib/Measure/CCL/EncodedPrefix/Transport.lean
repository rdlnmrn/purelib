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
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.EncodedPrefix.Stability.Squared
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Projective.Chordal.Probe.Affine

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Measure.Coupling.Law.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

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

namespace Purelib.Measure.CCL.EncodedPrefix

section
open Purelib
open Purelib.Data
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The retained coupling between exact encoder and affine squared-sensitive probe laws has zero squared transport cost.
-/
theorem encodedSquaredSensitiveProbeLawCoupling_squaredTransportCost_eq_zero
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (sensitive : Chordal.Probe.SquaredProbeSensitive probe factor) :
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction probe
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) = 0 := by
  rw [Distribution.Projective.Chordal.Probe.encodedProbeLawCoupling_squaredTransportCost]
  calc
    distribution.poweredL2Distance
        (fun item => probe (Encoder.Blocks.encodeBlocks
          (fraction item) (numeratorNonzero item)).point)
        (fun item => probe (Line.Proj.affine (fraction item).value)) =
        distribution.poweredL2Distance
          (fun item => probe (Line.Proj.affine (fraction item).value))
          (fun item => probe (Line.Proj.affine (fraction item).value)) := by
      unfold Distribution.poweredL2Distance
        Content.poweredL2Distance
      exact distribution.toContent.poweredL2_congr _ _ fun item => by
        dsimp only
        rw [Approximation.CCL.EncodedPrefix.encodedSquaredSensitiveProbe_eq_value (fraction item)
          (numeratorNonzero item) probe factor sensitive]
    _ = 0 := distribution.poweredL2Distance_refl _

/-- The exact encoder-to-affine omega-probe coupling has zero squared transport cost. -/
theorem encodedChordalOmegaProbeLawCoupling_squaredTransportCost_eq_zero
    {index : Type}
    (distribution : Measure.Distribution index)
    (fraction : index → GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction Chordal.Probe.chordalOmegaProbe
      (fun item => (Encoder.Blocks.encodeBlocks
        (fraction item) (numeratorNonzero item)).point)).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) = 0 :=
  CCL.EncodedPrefix.encodedSquaredSensitiveProbeLawCoupling_squaredTransportCost_eq_zero
    distribution fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2
      Chordal.Probe.chordalOmegaProbe_squaredSensitive

/-- A realizing probe law's coupling to the affine law costs at most the expected scaled encoded-cylinder spread.

The original distribution couples each realized point with its own affine fraction value, and the squared-sensitivity
factor is nonnegative. -/
theorem encodedProbeLawCoupling_squaredTransportCost_le {index : Type}
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
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) ≤
      distribution.expectation fun item =>
        factor * Approximation.CCL.Cylinder.cylinderSpread
          (Encoder.Blocks.encodeBlocks (fraction item)
            (numeratorNonzero item)).blocks := by
  rw [Distribution.Projective.Chordal.Probe.encodedProbeLawCoupling_squaredTransportCost]
  exact CCL.EncodedPrefix.encodedSquaredProbe_poweredL2Distance_values_le distribution fraction
    numeratorNonzero probe factor factorNonnegative sensitive points
    pointsRealize

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested encoded block count makes the retained squared transport cost strictly smaller than epsilon squared.
-/
theorem encodedProbeLawCoupling_squaredTransportCost_lt_requested
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
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction probe points).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) <
      epsilon ^ 2 := by
  have costLe := CCL.EncodedPrefix.encodedProbeLawCoupling_squaredTransportCost_le distribution
    fraction numeratorNonzero probe factor factorPositive.le sensitive points
    pointsRealize
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
  exact costLe.trans_lt (budgetLe.trans_lt (Quadratic.Bounds.half_sq_lt_sq epsilonPositive))

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The requested omega-probe block count makes its retained affine coupling cost strictly smaller than epsilon squared.
-/
theorem encodedChordalOmegaProbeLawCoupling_squaredTransportCost_lt_requested
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
    (Distribution.Projective.Chordal.encodedProbeLawCoupling distribution fraction Chordal.Probe.chordalOmegaProbe
      points
      ).transportCost
        (fun left right =>
          Distance.rationalSeparation left right ^ 2) <
      epsilon ^ 2 :=
  CCL.EncodedPrefix.encodedProbeLawCoupling_squaredTransportCost_lt_requested distribution
    fraction numeratorNonzero Chordal.Probe.chordalOmegaProbe 2 (by decide)
    Chordal.Probe.chordalOmegaProbe_squaredSensitive epsilon epsilonPositive enough points
    pointsRealize

end Purelib.Measure.CCL.EncodedPrefix

end
