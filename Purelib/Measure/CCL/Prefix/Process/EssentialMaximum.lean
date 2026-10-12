module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Cylinder.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
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
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
public section

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

namespace Purelib.Measure.CCL.Prefix

section PrefixFamilyProcess

section
open Purelib
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- Take the original law's essential maximum magnitude of scaled cylinder spreads at the current state. -/
@[expose] def PrefixFamilyProcess.probeEssentialMaximumRadius {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (factor : Fraction.Rational) : Fraction.Rational :=
  distribution.essentialMaximumMagnitude fun item =>
    factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Take the original law's essential maximum magnitude of the probe at the fixed process witnesses. -/
@[expose] def PrefixFamilyProcess.probeWitnessEssentialMaximum {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) : Fraction.Rational :=
  distribution.essentialMaximumMagnitude fun item =>
    probe (process.witness item)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The current essential radius is nonnegative for every scalar factor. -/
theorem PrefixFamilyProcess.probeEssentialMaximumRadius_nonnegative {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (factor : Fraction.Rational) :
    0 ≤ (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor :=
  distribution.essentialMaximumMagnitude_nonnegative _

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Center an interval at the fixed witness essential maximum with the current essential cylinder radius.

Both quantities use the original law's nonzero-weight occurrences and retain the supplied process state. -/
@[expose] def PrefixFamilyProcess.probeEssentialMaximumBound {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) : Data.Rat.Interval where
  lower := (PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe -
    (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor
  upper := (PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe +
    (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor
  valid := by
    have nonnegative := (PrefixFamilyProcess.probeEssentialMaximumRadius_nonnegative process) distribution
      state factor
    apply Fraction.Order.Arithmetic.sub_le_iff_le_add_direct.mpr
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
      ((Fraction.zero_add (0 : Fraction.Rational)) ▸
        Fraction.Order.Arithmetic.add_le_add_direct nonnegative nonnegative)
      ((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe)
    calc
      ((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe) = 0 +
        ((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe) := (Fraction.zero_add
        _).symm
      _ ≤ ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor) +
        ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor) +
        ((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe) := translated
      _ = (((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe) +
        ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor)) +
        ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor) := by
        ring1

/-- The current essential maximum enclosure has width twice its retained radius. -/
theorem PrefixFamilyProcess.probeEssentialMaximumBound_width {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) :
    ((PrefixFamilyProcess.probeEssentialMaximumBound process) distribution state probe factor).width =
      2 * (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor := by
  unfold PrefixFamilyProcess.probeEssentialMaximumBound Interval.width
  ring1

end

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Measure
/-- Each retained nonzero-weight atom's nonnegative scaled spread is bounded by the current essential radius. -/
private theorem Process.cellRadius_le_radius {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (atom : Measure.Weighted ι)
    (member : atom ∈ distribution.atoms) (nonzero : atom.weight ≠ 0) :
    factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) ≤
      (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor := by
  have bounded :=
    distribution.toContent
      |>.essentiallyBoundedBy_essentialMaximumMagnitude
        (fun item => factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item))
        atom member
  rcases bounded with zero | bound
  · exact (nonzero zero).elim
  · have cellNonnegative :
        0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
        (Approximation.CCL.Cylinder.cylinderSpread_nonneg (process.blocks state atom.item))
    change Distance.rationalSeparation
        (factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item)) 0 ≤
      (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor at bound
    rw [Distance.rationalSeparation_zero_of_nonneg
      cellNonnegative] at bound
    exact bound

/-- Pointwise prefix extension cannot increase the essential cylinder radius for a nonnegative factor. -/
private theorem PrefixFamilyProcess.probeEssentialMaximumRadius_le_of_extensions {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (inner outer : process.State) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (extension : ∀ item, ∃ suffix,
      process.blocks inner item = process.blocks outer item ++ suffix) :
    (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution inner factor ≤
      (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution outer factor := by
  apply distribution.toContent.essentialMaximumMagnitude_le
    (fun item => factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks inner item))
    ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution outer factor)
    ((PrefixFamilyProcess.probeEssentialMaximumRadius_nonnegative process)
      distribution outer factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    have innerNonnegative :
        0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks inner atom.item) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
        (Approximation.CCL.Cylinder.cylinderSpread_nonneg (process.blocks inner atom.item))
    change Distance.rationalSeparation
        (factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks inner atom.item)) 0 ≤ _
    rw [Distance.rationalSeparation_zero_of_nonneg
      innerNonnegative]
    rcases extension atom.item with ⟨suffix, equal⟩
    calc
      factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks inner atom.item) =
          factor * Approximation.CCL.Cylinder.cylinderSpread
            (process.blocks outer atom.item ++ suffix) := by rw [equal]
      _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks outer atom.item) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Approximation.CCL.Cylinder.cylinderSpread_le_of_append
            (process.blocks outer atom.item) suffix)
          factorNonnegative
      _ ≤ (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution outer factor :=
        (Process.cellRadius_le_radius process) distribution outer factor
          factorNonnegative atom member zero

end

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- Pointwise prefix extension refines the enclosure around the fixed witness essential maximum. -/
private theorem PrefixFamilyProcess.probeEssentialMaximumBound_refines_of_extensions
  {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (inner outer : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (extension : ∀ item, ∃ suffix,
      process.blocks inner item = process.blocks outer item ++ suffix) :
    Interval.Refines
      ((PrefixFamilyProcess.probeEssentialMaximumBound process) distribution inner probe factor)
      ((PrefixFamilyProcess.probeEssentialMaximumBound process) distribution outer probe factor) := by
  have radiusLe := (PrefixFamilyProcess.probeEssentialMaximumRadius_le_of_extensions process)
    distribution inner outer factor factorNonnegative extension
  constructor
  · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct radiusLe
      ((PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe)
  · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl radiusLe

/-- The essential distance from a current realizing probe family to the witnesses is bounded by the current radius. -/
theorem PrefixFamilyProcess.probe_essentialMaximumDistance_le_radius {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.essentialMaximumDistance
        (fun item => probe (points item))
        (fun item => probe (process.witness item)) ≤
      (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor := by
  change distribution.toContent.essentialMaximumMagnitude
      (fun item => probe (points item) - probe (process.witness item)) ≤ _
  apply distribution.toContent.essentialMaximumMagnitude_le
    (fun item => probe (points item) - probe (process.witness item))
    ((PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor)
    ((PrefixFamilyProcess.probeEssentialMaximumRadius_nonnegative process)
      distribution state factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation
      (probe (points atom.item) - probe (process.witness atom.item)) 0 ≤ _
    rw [← Distance.rationalSeparation_eq_sub_zero]
    calc
      Distance.rationalSeparation
          (probe (points atom.item)) (probe (process.witness atom.item)) ≤
          factor * Chordal.Basic.chordalSq
            (points atom.item) (process.witness atom.item) := sensitive _ _
      _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Realizes.chordalSq_le_half_pow
            (pointsRealize atom member) (process.realizes state atom.item))
          factorNonnegative
      _ ≤ (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor :=
        (Process.cellRadius_le_radius process) distribution state factor
          factorNonnegative atom member zero

/-- The current essential maximum enclosure contains the magnitude maximum of any realizing probe family. -/
theorem PrefixFamilyProcess.probeEssentialMaximumBound_contains {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    Interval.Contains
      ((PrefixFamilyProcess.probeEssentialMaximumBound process) distribution state probe factor)
      (distribution.essentialMaximumMagnitude fun item =>
        probe (points item)) := by
  let actual := distribution.essentialMaximumMagnitude fun item =>
    probe (points item)
  let center := (PrefixFamilyProcess.probeWitnessEssentialMaximum process) distribution probe
  let radius := (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor
  have separation :
      Distance.rationalSeparation actual center ≤ radius := by
    calc
      Distance.rationalSeparation actual center ≤
          distribution.essentialMaximumDistance
            (fun item => probe (points item))
            (fun item => probe (process.witness item)) :=
        distribution.essentialMaximumMagnitude_separation_le_distance _ _
      _ ≤ radius := (PrefixFamilyProcess.probe_essentialMaximumDistance_le_radius process)
        distribution state probe factor factorNonnegative sensitive
          points pointsRealize
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
/-- Enough current blocks at the quarter-target request make the essential maximum enclosure narrower than the positive
target. -/
theorem PrefixFamilyProcess.probeEssentialMaximumBound_width_lt_requested {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (state : process.State) (probe : Line.GaussianLine → Fraction.Rational)
    (factor : Fraction.Rational) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Fraction.Rational) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      Budget.requiredProbeBlockCount (target / 4) factor ≤
        (process.blocks state atom.item).length) :
    ((PrefixFamilyProcess.probeEssentialMaximumBound process) distribution state probe factor).width <
      target := by
  have quarterPositive : 0 < target / 4 :=
    Fraction.Order.Field.div_pos_direct targetPositive (by decide)
  have radiusBound :
      (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor ≤
        target / 4 := by
    apply distribution.toContent.essentialMaximumMagnitude_le
      (fun item => factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item))
      (target / 4) quarterPositive.le
    intro atom member
    by_cases zero : atom.weight = 0
    · exact Or.inl zero
    · apply Or.inr
      have cellNonnegative :
          0 ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct factorPositive.le
          (Approximation.CCL.Cylinder.cylinderSpread_nonneg (process.blocks state atom.item))
      change Distance.rationalSeparation
          (factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item)) 0 ≤
        target / 4
      rw [Distance.rationalSeparation_zero_of_nonneg
        cellNonnegative]
      have widthSmall := Approximation.CCL.Prefix.completedPrefixProbeBound_width_lt_requested
        (process.witness atom.item) (process.realizes state atom.item)
        probe factor factorPositive sensitive
        (target / 4) quarterPositive (enough atom member)
      rw [Approximation.CCL.Prefix.completedPrefixProbeBound_width] at widthSmall
      exact (calc
          factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) ≤
              2 * (factor * Approximation.CCL.Cylinder.cylinderSpread
                (process.blocks state atom.item)) := by
            calc
              factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) =
                  factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) +
                    0 := by ring1
              _ ≤ factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state atom.item) +
                    factor * Approximation.CCL.Cylinder.cylinderSpread
                      (process.blocks state atom.item) :=
                add_le_add le_rfl cellNonnegative
              _ = 2 * (factor * Approximation.CCL.Cylinder.cylinderSpread
                    (process.blocks state atom.item)) := by ring1
          _ < target / 4 := widthSmall).le
  rw [(PrefixFamilyProcess.probeEssentialMaximumBound_width process)]
  calc
    2 * (PrefixFamilyProcess.probeEssentialMaximumRadius process) distribution state factor ≤
        2 * (target / 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusBound (by decide)
    _ = target / 2 := Purelib.Data.Rat.Fraction.Order.two_mul_quarter_eq_half target
    _ < target := Purelib.Data.Rat.Fraction.Order.Field.half_lt_self targetPositive

open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- Build a refining essential maximum enclosure process from the original prefix states and fixed witnesses.

A positive epsilon request extends the original blocks to the quarter-epsilon sensitivity budget and preserves the same
finite law and witness center. -/
@[expose] def PrefixFamilyProcess.toProbeEssentialMaximumProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.BoundProcess where
  State := process.State
  bound state :=
    (PrefixFamilyProcess.probeEssentialMaximumBound process) distribution state probe factor
  initial := process.initial
  request state epsilon positive :=
    process.request state (Budget.requiredProbeBlockCount (epsilon / 4) factor)
  request_refines state epsilon positive := by
    apply (PrefixFamilyProcess.probeEssentialMaximumBound_refines_of_extensions process)
      distribution _ state probe factor factorPositive.le
    intro item
    exact process.request_extends state
      (Budget.requiredProbeBlockCount (epsilon / 4) factor) item
  accurate state epsilon positive := by
    apply (PrefixFamilyProcess.probeEssentialMaximumBound_width_lt_requested process)
      distribution _ probe factor factorPositive sensitive epsilon positive
    intro atom member
    exact process.request_length state
      (Budget.requiredProbeBlockCount (epsilon / 4) factor) atom.item
  refinesInitial state := by
    apply (PrefixFamilyProcess.probeEssentialMaximumBound_refines_of_extensions process)
      distribution state process.initial probe factor factorPositive.le
    exact process.extendsInitial state

open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Measure
/-- The process's current bound contains the essential maximum magnitude of every current realizing probe family. -/
theorem PrefixFamilyProcess.essentialMaximum_mem_toProbeEssentialMaximumProcess_bound
    {ι : Type} (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (((PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.essentialMaximumMagnitude fun item =>
          probe (points item)) :=
  (PrefixFamilyProcess.probeEssentialMaximumBound_contains process) distribution state probe factor
    factorPositive.le sensitive points pointsRealize

/-- The requested essential maximum enclosure is narrower than the positive epsilon. -/
theorem PrefixFamilyProcess.request_probeEssentialMaximum_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (((PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
      factorPositive sensitive).bound
      (((PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  ((PrefixFamilyProcess.toProbeEssentialMaximumProcess process) distribution probe factor
    factorPositive sensitive).accurate state epsilon positive

end

end PrefixFamilyProcess

end Purelib.Measure.CCL.Prefix

end
