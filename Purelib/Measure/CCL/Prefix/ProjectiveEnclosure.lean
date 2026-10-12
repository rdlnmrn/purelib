module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
public import Purelib.Approximation.CCL.Prefix.ProjectiveObservation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Measure.Distribution.Expectation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite measure bounds for projectively rescaled CCL prefixes

The integral CCL encoder retains arbitrary nonzero homogeneous rescalings at
intermediate decoding stages.  Its certificates therefore use
`ProjectiveRealizes`, rather than the canonical-tail `Realizes` relation used
by the original prefix profile.  This module gives those exact encoder-facing
certificates the same finite observation and rational-enclosure interface.

No projective normalization, representative choice, completed point, or
infinite continuation is introduced.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Average the exact probe-bound intervals of the retained projective-prefix certificates.

Each interval uses its original block list and witness with the same chordal-square sensitivity certificate; the
enclosing expectation retains the original distribution weights. -/
def projectivePrefixFamilyProbeExpectationBound
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  distribution.enclosedExpectation fun certificate =>
    certificate.probeBound probe factor factorNonnegative sensitive

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The exact expectation-bound width equals the original expectation of twice the sensitivity-scaled cylinder spreads.
-/
theorem projectivePrefixFamilyProbeExpectationBound_width
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) := by
  unfold projectivePrefixFamilyProbeExpectationBound
  rw [Distribution.enclosedExpectation_width]
  exact distribution.expectation_congr _ _ (fun certificate =>
    Approximation.CCL.Prefix.completedProjectivePrefixProbeBound_width certificate.blocks
      certificate.witness certificate.witnessRealizes probe factor
      factorNonnegative sensitive)

/-- The exact family interval contains the expected probe value of points realizing their corresponding retained
projective prefixes. -/
theorem projectivePrefixFamilyProbeExpectationBound_contains
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedProjectivePrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes atom.item.blocks
        (points atom.item)) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) := by
  unfold projectivePrefixFamilyProbeExpectationBound
  apply Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact Approximation.CCL.Prefix.completedProjectivePrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

/-- A strict budget on the original expected scaled spread bounds the exact family interval's width. -/
theorem projectivePrefixFamilyProbeExpectationBound_width_lt_of_budget
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational)
    (budget : distribution.expectation (fun certificate =>
      2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks)) < target) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width < target := by
  rw [projectivePrefixFamilyProbeExpectationBound_width]
  exact budget

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Sufficient original block counts at half the positive target make the exact family expectation interval narrower
than that target. -/
theorem projectivePrefixFamilyProbeExpectationBound_width_lt_requested
    (distribution : Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (projectivePrefixFamilyProbeExpectationBound distribution probe factor
      factorPositive.le sensitive).width < target := by
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
  unfold projectivePrefixFamilyProbeExpectationBound
  apply distribution.enclosedExpectation_width_lt_of_uniform
    (fun certificate => certificate.probeBound probe factor
      factorPositive.le sensitive)
    (target / 2) target
  · intro atom member
    exact (Approximation.CCL.Prefix.completedProjectivePrefixProbeBound_width_lt_requested
      atom.item.witness atom.item.witnessRealizes probe factor factorPositive
      sensitive (target / 2) halfPositive (enough atom member)).le
  · exact halfSmall

end Purelib.Measure.CCL.Prefix

end
