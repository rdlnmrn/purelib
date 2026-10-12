module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
public import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.CCL.Prefix.Distribution
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Distribution.Expectation

import Purelib.CCL.Measure.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Measure.Distribution.Stability
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding (Block)
open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Average the common probe enclosure over the completed-prefix extension law.

The exact prefix witness and nonnegative sensitivity factor determine the same enclosure for every binary extension
occurrence. -/
def completedPrefixProbeExpectationBound
    (blocks : List Block) (depth : Nat) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  (CCL.Prefix.completedPrefixExtensionDistribution blocks depth).enclosedExpectation
    (fun _ => Approximation.CCL.Prefix.completedPrefixProbeBound blocks witness witnessRealizes
      probe factor factorNonnegative sensitive)

/-- Averaging the constant completed-prefix enclosure returns that exact probe bound. -/
theorem completedPrefixProbeExpectationBound_eq_probeBound
    (blocks : List Block) (depth : Nat) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
        probe factor factorNonnegative sensitive =
      Approximation.CCL.Prefix.completedPrefixProbeBound blocks witness witnessRealizes
        probe factor factorNonnegative sensitive := by
  unfold completedPrefixProbeExpectationBound
  apply Interval.ext
  · rw [Distribution.enclosedExpectation_lower,
      Distribution.expectation_constant]
  · rw [Distribution.enclosedExpectation_upper,
      Distribution.expectation_constant]

end

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The expectation enclosure contains the probe expectation of any points realizing the retained prefix on the
extension atoms. -/
theorem completedPrefixProbeExpectationBound_contains
    (blocks : List Block) (depth : Nat) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : List.BinaryPrefix.CCLMeasureWord → Line.GaussianLine)
    (pointsRealize : ∀ atom,
      atom ∈ (CCL.Prefix.completedPrefixExtensionDistribution blocks depth).atoms →
        Realizes blocks (points atom.item)) :
    (completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
      probe factor factorNonnegative sensitive).Contains
        ((CCL.Prefix.completedPrefixExtensionDistribution blocks depth).expectation
          (fun word => probe (points word))) := by
  apply Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains blocks witness witnessRealizes
    probe factor factorNonnegative sensitive (pointsRealize atom member)

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The completed-prefix expectation enclosure has width twice the sensitivity-scaled cylinder spread. -/
theorem completedPrefixProbeExpectationBound_width
    (blocks : List Block) (depth : Nat) (witness : Line.GaussianLine)
    (witnessRealizes : Realizes blocks witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (completedPrefixProbeExpectationBound blocks depth witness witnessRealizes
      probe factor factorNonnegative sensitive).width =
        2 * (factor * Approximation.CCL.Cylinder.cylinderSpread blocks) := by
  rw [completedPrefixProbeExpectationBound_eq_probeBound,
    Approximation.CCL.Prefix.completedPrefixProbeBound_width]

/-- Appending blocks refines the expectation enclosure while retaining the same realizing witness. -/
theorem completedPrefixProbeExpectationBound_append_refines
    (stem suffix : List Block) (depth : Nat) (witness : Line.GaussianLine)
    (witnessRealizes :
      Realizes (stem ++ suffix) witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (completedPrefixProbeExpectationBound (stem ++ suffix) depth witness
        witnessRealizes probe factor factorNonnegative sensitive)
      (completedPrefixProbeExpectationBound stem depth witness
        (Cylinder.realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) := by
  rw [completedPrefixProbeExpectationBound_eq_probeBound,
    completedPrefixProbeExpectationBound_eq_probeBound]
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_append_refines stem suffix witness
    witnessRealizes probe factor factorNonnegative sensitive

end

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Average the probe enclosures of the original completed-prefix certificate distribution.

Each atom retains its own blocks and realizing witness; lower and upper endpoint expectations form the resulting
rational interval. -/
def prefixFamilyProbeExpectationBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  distribution.enclosedExpectation fun certificate =>
    certificate.probeBound probe factor factorNonnegative sensitive

/-- Take the original expectation of the probe at each retained certificate witness. -/
def prefixFamilyProbeWitnessExpectation
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun certificate => probe certificate.witness

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- Take the original expectation of sensitivity-scaled cylinder spread for each retained certificate. -/
def prefixFamilyProbeRadius
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun certificate =>
    factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- A nonnegative sensitivity factor makes the family's expected probe radius nonnegative. -/
theorem prefixFamilyProbeRadius_nonnegative
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    0 ≤ prefixFamilyProbeRadius distribution factor := by
  apply distribution.expectation_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (Approximation.CCL.Cylinder.cylinderSpread_nonneg atom.item.blocks)

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Center a rational interval at the witness expectation with the expected cylinder radius. -/
def prefixFamilyProbeWitnessBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor) : Data.Rat.Interval where
  lower := prefixFamilyProbeWitnessExpectation distribution probe -
    prefixFamilyProbeRadius distribution factor
  upper := prefixFamilyProbeWitnessExpectation distribution probe +
    prefixFamilyProbeRadius distribution factor
  valid := by
    have radiusNonnegative :=
      prefixFamilyProbeRadius_nonnegative distribution factor factorNonnegative
    have lower := Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusNonnegative
      (prefixFamilyProbeWitnessExpectation distribution probe)
    have restore : prefixFamilyProbeWitnessExpectation distribution probe - 0 =
        prefixFamilyProbeWitnessExpectation distribution probe := by ring1
    rewrite [restore] at lower
    exact lower.trans (le_add_of_nonneg_right radiusNonnegative)

/-- The endpoint-averaged probe enclosure equals the witness-centered expected-radius interval. -/
theorem prefixFamilyProbeExpectationBound_eq_witnessBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive =
      prefixFamilyProbeWitnessBound distribution probe factor
        factorNonnegative := by
  apply Interval.ext
  · unfold prefixFamilyProbeExpectationBound prefixFamilyProbeWitnessBound
    rw [Distribution.enclosedExpectation_lower]
    change distribution.expectation (fun certificate =>
        probe certificate.witness -
          factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) = _
    rw [distribution.expectation_sub]
    rfl
  · unfold prefixFamilyProbeExpectationBound prefixFamilyProbeWitnessBound
    rw [Distribution.enclosedExpectation_upper]
    change distribution.expectation (fun certificate =>
        probe certificate.witness +
          factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) = _
    rw [distribution.expectation_add]
    rfl

/-- The family expectation enclosure has width twice its expected probe radius. -/
theorem prefixFamilyProbeExpectationBound_width_eq_two_mul_radius
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      2 * prefixFamilyProbeRadius distribution factor := by
  rw [prefixFamilyProbeExpectationBound_eq_witnessBound]
  unfold prefixFamilyProbeWitnessBound Interval.width
  ring1

/-- The family expectation enclosure's width is the original expectation of twice each scaled cylinder spread. -/
theorem prefixFamilyProbeExpectationBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks) := by
  unfold prefixFamilyProbeExpectationBound
  rw [Distribution.enclosedExpectation_width]
  exact distribution.expectation_congr _ _ (fun certificate =>
    Approximation.CCL.Prefix.completedPrefixProbeBound_width certificate.blocks
      certificate.witness certificate.witnessRealizes probe factor
      factorNonnegative sensitive)

/-- The family enclosure contains the probe expectation of any realization of the original certificate blocks. -/
theorem prefixFamilyProbeExpectationBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes atom.item.blocks (points atom.item)) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) := by
  unfold prefixFamilyProbeExpectationBound
  apply Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains atom.item.blocks
    atom.item.witness atom.item.witnessRealizes probe factor
    factorNonnegative sensitive (pointsRealize atom member)

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Average probe enclosures after appending each certificate's supplied suffix.

The original distribution and witnesses remain fixed, with evidence that each witness realizes its extended blocks. -/
def extendedPrefixFamilyProbeExpectationBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Data.Rat.Interval :=
  distribution.enclosedExpectation fun certificate =>
    Approximation.CCL.Prefix.completedPrefixProbeBound
      (certificate.blocks ++ suffix certificate) certificate.witness
      (extendedRealizes certificate) probe factor factorNonnegative sensitive

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The extended family enclosure contains the probe expectation of any points realizing the same extended blocks. -/
theorem extendedPrefixFamilyProbeExpectationBound_contains
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : Cylinder.CompletedPrefixCertificate → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (atom.item.blocks ++ suffix atom.item) (points atom.item)) :
    (extendedPrefixFamilyProbeExpectationBound distribution suffix
      extendedRealizes probe factor factorNonnegative sensitive).Contains
      (distribution.expectation fun certificate => probe (points certificate)) := by
  unfold extendedPrefixFamilyProbeExpectationBound
  apply Distribution.expectation_mem_enclosedExpectation
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains
    (atom.item.blocks ++ suffix atom.item) atom.item.witness
    (extendedRealizes atom.item) probe factor factorNonnegative sensitive
    (pointsRealize atom member)

/-- Extending certificate blocks while retaining their witnesses refines the original family expectation enclosure. -/
theorem extendedPrefixFamilyProbeExpectationBound_refines
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Interval.Refines
      (extendedPrefixFamilyProbeExpectationBound distribution suffix
        extendedRealizes probe factor factorNonnegative sensitive)
      (prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive) := by
  apply distribution.enclosedExpectation_refines
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_append_refines atom.item.blocks
    (suffix atom.item) atom.item.witness (extendedRealizes atom.item)
    probe factor factorNonnegative sensitive

/-- The extended family expectation enclosure is no wider than the original enclosure. -/
theorem extendedPrefixFamilyProbeExpectationBound_width_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (extendedRealizes : ∀ certificate,
      Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (extendedPrefixFamilyProbeExpectationBound distribution suffix
      extendedRealizes probe factor factorNonnegative sensitive).width ≤
      (prefixFamilyProbeExpectationBound distribution probe factor
        factorNonnegative sensitive).width :=
  (extendedPrefixFamilyProbeExpectationBound_refines distribution suffix
    extendedRealizes probe factor factorNonnegative sensitive).width_le

/-- An expected doubled-radius budget bounds the family expectation enclosure's width. -/
theorem prefixFamilyProbeExpectationBound_width_lt_of_budget
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational)
    (budget : distribution.expectation (fun certificate =>
      2 * (factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks)) < target) :
    (prefixFamilyProbeExpectationBound distribution probe factor
      factorNonnegative sensitive).width < target := by
  rw [prefixFamilyProbeExpectationBound_width]
  exact budget

end

open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Enough blocks on each original atom make the expectation enclosure narrower than the positive target.

The per-atom request uses half the target and the positive sensitivity factor, retaining the original certificate
witnesses and distribution. -/
theorem prefixFamilyProbeExpectationBound_width_lt_requested
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 2) factor ≤ atom.item.blocks.length) :
    (prefixFamilyProbeExpectationBound distribution probe factor
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
  unfold prefixFamilyProbeExpectationBound
  apply distribution.enclosedExpectation_width_lt_of_uniform
    (fun certificate => certificate.probeBound probe factor
      factorPositive.le sensitive)
    (target / 2) target
  · intro atom member
    exact (Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested atom.item.witness
      atom.item.witnessRealizes probe factor factorPositive sensitive
      (target / 2) halfPositive (enough atom member)).le
  · exact halfSmall

end

end Purelib.Measure.CCL.Prefix

end

section
section
@[expose] public section

/-!
# Witness-centred variance enclosures from finite CCL prefixes

The displayed prefix witnesses have an exact rational probe expectation.
Variance around that computable centre differs from the true finite variance
by exactly the square of the mean error.  A powered-deviation enclosure and
the explicit prefix mean radius therefore give a direct rational variance
enclosure without squaring a signed mean interval.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- Take the expected scaled cylinder spread after each certificate's supplied suffix extension. -/
def extendedPrefixFamilyProbeRadius
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (factor : Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun certificate =>
    factor * Approximation.CCL.Cylinder.cylinderSpread (certificate.blocks ++ suffix certificate)

open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Measure
/-- A nonnegative factor makes the expected extended-prefix radius nonnegative. -/
theorem extendedPrefixFamilyProbeRadius_nonnegative
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    0 ≤ extendedPrefixFamilyProbeRadius distribution suffix factor := by
  apply distribution.expectation_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (Approximation.CCL.Cylinder.cylinderSpread_nonneg (atom.item.blocks ++ suffix atom.item))

/-- Appending blocks cannot increase the original family's expected scaled radius. -/
theorem extendedPrefixFamilyProbeRadius_le
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (suffix : Cylinder.CompletedPrefixCertificate → List Block)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    extendedPrefixFamilyProbeRadius distribution suffix factor ≤
      prefixFamilyProbeRadius distribution factor := by
  apply distribution.expectation_mono
  intro atom member
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Approximation.CCL.Cylinder.cylinderSpread_le_of_append atom.item.blocks (suffix atom.item))
    factorNonnegative
end Purelib.Measure.CCL.Prefix

end

end
