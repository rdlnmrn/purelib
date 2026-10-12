module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
public section

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

namespace Purelib.Measure.CCL.Prefix

section
open Purelib
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- Take the essential maximum magnitude of the retained certificates' scaled cylinder spreads. -/
@[expose] def prefixFamilyProbeEssentialMaximumRadius
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) : Fraction.Rational :=
  distribution.essentialMaximumMagnitude fun certificate =>
    factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Take the essential maximum magnitude of the probe at the original certificate witnesses. -/
@[expose] def prefixFamilyProbeWitnessEssentialMaximum
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) : Fraction.Rational :=
  distribution.essentialMaximumMagnitude fun certificate =>
    probe certificate.witness

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The essential maximum cylinder radius is nonnegative for every scalar factor. -/
theorem prefixFamilyProbeEssentialMaximumRadius_nonnegative
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) :
    0 ≤ prefixFamilyProbeEssentialMaximumRadius distribution factor :=
  distribution.essentialMaximumMagnitude_nonnegative _

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Center an interval at the witness essential maximum with the essential maximum cylinder radius.

The retained original law determines which zero-weight atoms are ignored by both quantities. -/
@[expose] def prefixFamilyProbeEssentialMaximumBound
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational) :
    Data.Rat.Interval where
  lower := prefixFamilyProbeWitnessEssentialMaximum distribution probe -
    prefixFamilyProbeEssentialMaximumRadius distribution factor
  upper := prefixFamilyProbeWitnessEssentialMaximum distribution probe +
    prefixFamilyProbeEssentialMaximumRadius distribution factor
  valid := by
    have nonnegative := prefixFamilyProbeEssentialMaximumRadius_nonnegative distribution factor
    apply Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
      ((Fraction.zero_add (0 : Fraction.Rational)) ▸
        Fraction.Order.Arithmetic.add_le_add_direct nonnegative nonnegative)
      (prefixFamilyProbeWitnessEssentialMaximum distribution probe)
    calc
      (prefixFamilyProbeWitnessEssentialMaximum distribution probe) = 0 +
        (prefixFamilyProbeWitnessEssentialMaximum distribution probe) := (Fraction.zero_add _).symm
      _ ≤ (prefixFamilyProbeEssentialMaximumRadius distribution factor) +
        (prefixFamilyProbeEssentialMaximumRadius distribution factor) +
        (prefixFamilyProbeWitnessEssentialMaximum distribution probe) := translated
      _ = ((prefixFamilyProbeWitnessEssentialMaximum distribution probe) +
        (prefixFamilyProbeEssentialMaximumRadius distribution factor)) +
        (prefixFamilyProbeEssentialMaximumRadius distribution factor) := by
        ring1

/-- The essential maximum enclosure has width twice its retained radius. -/
theorem prefixFamilyProbeEssentialMaximumBound_width
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational) :
    (prefixFamilyProbeEssentialMaximumBound distribution probe factor).width =
      2 * prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  unfold prefixFamilyProbeEssentialMaximumBound
    Interval.width
  ring1

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Every original nonzero-weight atom's nonnegative scaled cylinder spread is bounded by the family essential radius.
-/
private theorem cellRadius_le_familyRadius
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (atom : Measure.Weighted Cylinder.CompletedPrefixCertificate)
    (member : atom ∈ distribution.atoms) (nonzero : atom.weight ≠ 0) :
    factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  have bounded :=
    distribution.toContent
      |>.essentiallyBoundedBy_essentialMaximumMagnitude
        (fun certificate => factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks)
        atom member
  rcases bounded with zero | bound
  · exact (nonzero zero).elim
  · have cellNonnegative :
        0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
      Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
        (Approximation.CCL.Cylinder.cylinderSpread_nonneg atom.item.blocks)
    change Distance.rationalSeparation
        (factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks) 0 ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor at bound
    rw [Distance.rationalSeparation_zero_of_nonneg
      cellNonnegative] at bound
    exact bound

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The essential maximum distance between realizing and witness probe families is bounded by the retained cylinder
radius. -/
theorem prefixFamilyProbe_essentialMaximumDistance_le_radius
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
    distribution.essentialMaximumDistance
        (fun certificate => probe (points certificate))
        (fun certificate => probe certificate.witness) ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  change distribution.toContent.essentialMaximumMagnitude
      (fun certificate =>
        probe (points certificate) - probe certificate.witness) ≤ _
  apply distribution.toContent.essentialMaximumMagnitude_le
    (fun certificate =>
      probe (points certificate) - probe certificate.witness)
    (prefixFamilyProbeEssentialMaximumRadius distribution factor)
    (prefixFamilyProbeEssentialMaximumRadius_nonnegative
      distribution factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation
      (probe (points atom.item) - probe atom.item.witness) 0 ≤ _
    rw [← Distance.rationalSeparation_eq_sub_zero]
    calc
      Distance.rationalSeparation
          (probe (points atom.item)) (probe atom.item.witness) ≤
          factor * Chordal.Basic.chordalSq
            (points atom.item) atom.item.witness :=
        sensitive _ _
      _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Realizes.chordalSq_le_half_pow
            (pointsRealize atom member) atom.item.witnessRealizes)
          factorNonnegative
      _ ≤ prefixFamilyProbeEssentialMaximumRadius distribution factor :=
        cellRadius_le_familyRadius distribution factor factorNonnegative
          atom member zero

/-- The witness-centered enclosure contains the essential maximum magnitude of any realizing probe family. -/
theorem prefixFamilyProbeEssentialMaximumBound_contains
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
    Interval.Contains
      (prefixFamilyProbeEssentialMaximumBound distribution probe factor)
      (distribution.essentialMaximumMagnitude fun certificate =>
        probe (points certificate)) := by
  let actual := distribution.essentialMaximumMagnitude fun certificate =>
    probe (points certificate)
  let center := prefixFamilyProbeWitnessEssentialMaximum distribution probe
  let radius := prefixFamilyProbeEssentialMaximumRadius distribution factor
  have separation :
      Distance.rationalSeparation actual center ≤ radius := by
    calc
      Distance.rationalSeparation actual center ≤
          distribution.essentialMaximumDistance
            (fun certificate => probe (points certificate))
            (fun certificate => probe certificate.witness) :=
        distribution.essentialMaximumMagnitude_separation_le_distance _ _
      _ ≤ radius :=
        prefixFamilyProbe_essentialMaximumDistance_le_radius distribution
          probe factor factorNonnegative sensitive points pointsRealize
  have directed : actual - center ≤ radius ∧ center - actual ≤ radius :=
    ⟨(Fraction.Order.Basic.le_max_left _ _).trans separation,
      (Fraction.Order.Basic.le_max_right _ _).trans separation⟩
  change center - radius ≤ actual ∧ actual ≤ center + radius
  constructor
  · apply Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr
    calc
      center ≤ radius + actual := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp directed.2
      _ = actual + radius := by ring1
  · calc
      actual ≤ radius + center := Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mp directed.1
      _ = center + radius := by ring1

end

open Purelib.Approximation.Rational in
open Purelib.CCL.Measure in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Sufficient retained blocks make the essential maximum enclosure narrower than the positive target.

The positive sensitivity factor and per-atom request at one quarter of the target bound the same original law's
essential radius. -/
theorem prefixFamilyProbeEssentialMaximumBound_width_lt_requested
    (distribution :
      Measure.Distribution Cylinder.CompletedPrefixCertificate)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 4) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbeEssentialMaximumBound distribution probe factor).width <
      target := by
  have quarterPositive : 0 < target / 4 :=
    Fraction.Order.Field.div_pos_direct targetPositive (by decide)
  have radiusBound :
      prefixFamilyProbeEssentialMaximumRadius distribution factor ≤
        target / 4 := by
    apply distribution.toContent.essentialMaximumMagnitude_le
      (fun certificate => factor * Approximation.CCL.Cylinder.cylinderSpread certificate.blocks)
      (target / 4) quarterPositive.le
    intro atom member
    by_cases zero : atom.weight = 0
    · exact Or.inl zero
    · apply Or.inr
      have cellNonnegative :
          0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
        Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
          (Approximation.CCL.Cylinder.cylinderSpread_nonneg atom.item.blocks)
      change Distance.rationalSeparation
          (factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks) 0 ≤ target / 4
      rw [Distance.rationalSeparation_zero_of_nonneg
        cellNonnegative]
      have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
        atom.item.witness atom.item.witnessRealizes probe factor
        factorPositive sensitive (target / 4) quarterPositive
        (enough atom member)
      rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width] at widthSmall
      exact (calc
          factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks ≤
              2 * (factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks) := by
            calc
              factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks =
                  factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks + 0 := by ring1
              _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks +
                    factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks :=
                add_le_add le_rfl cellNonnegative
              _ = 2 * (factor * Approximation.CCL.Cylinder.cylinderSpread atom.item.blocks) := by ring1
          _ < target / 4 := widthSmall).le
  rw [prefixFamilyProbeEssentialMaximumBound_width]
  calc
    2 * prefixFamilyProbeEssentialMaximumRadius distribution factor ≤
        2 * (target / 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusBound (by decide)
    _ = target / 2 := Purelib.Data.Rat.Fraction.Order.two_mul_quarter_eq_half target
    _ < target := Purelib.Data.Rat.Fraction.Order.Field.half_lt_self targetPositive

end

end Purelib.Measure.CCL.Prefix

end
