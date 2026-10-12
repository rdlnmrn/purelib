module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic

import Purelib.Approximation.Bound.Observation
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.CCL.Prefix.Process
import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Approximation.OneSided.BoundProcess
public import Purelib.Measure.Distribution.Enclosure.Process
import Purelib.Measure.Weighted.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

open Purelib.Data.CCL.Encoding.Cylinder.Basic (Realizes)

section
@[expose] public section

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

section

section

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat

namespace Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

open Purelib.Geometry.Projective in
/-- Take the original law's probe expectation at the prefix process's fixed witnesses. -/
def witnessProbeExpectation {ι : Type} (process :
  Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) : Fraction.Rational :=
  distribution.expectation fun item => probe (process.witness item)

/-- Take the original expected scaled cylinder spread at the supplied process state. -/
def probeRadius {ι : Type} (process : Cylinder.PrefixFamilyProcess
  ι)
    (distribution : Measure.Distribution ι)
    (factor : Fraction.Rational) (state : process.State) : Fraction.Rational :=
  distribution.expectation fun item =>
    factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks state item)

end Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

section
open Purelib.Measure

namespace Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

/-- A nonnegative sensitivity factor makes the current state's expected probe radius nonnegative. -/
theorem probeRadius_nonnegative {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    (state : process.State) :
    0 ≤ (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution factor state := by
  apply distribution.expectation_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (Approximation.CCL.Cylinder.cylinderSpread_nonneg (process.blocks state atom.item))

/-- Pointwise prefix extension between retained states cannot increase the expected probe radius. -/
theorem probeRadius_le_of_extends {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution factor newer ≤
      (CCL.Prefix.PrefixFamilyProcess.probeRadius process) distribution factor older := by
  apply distribution.expectation_mono
  intro atom member
  rcases extension atom.item with ⟨suffix, equal⟩
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · rw [equal]
    exact Approximation.CCL.Cylinder.cylinderSpread_le_of_append (process.blocks older atom.item) suffix
  · exact factorNonnegative

end Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

end

open Purelib.Geometry.Projective

namespace Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

/-- Build an expectation-enclosure process from the original prefix process and finite law.

The process retains the original states and witnesses and averages their pointwise probe enclosures, using the positive
sensitivity factor to answer width requests. -/
def toProbeExpectationProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Approximation.BoundProcess :=
  (process.toProbePointwiseProcess distribution probe factor
    factorPositive sensitive).toExpectationBoundProcess

end Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

namespace Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

/-- Pointwise extension of the retained blocks refines the expectation enclosure between the supplied states. -/
theorem probeExpectationBound_refines_of_extends {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    Interval.Refines
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).bound newer)
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).bound older) := by
  apply distribution.enclosedExpectation_refines
  intro atom member
  rcases extension atom.item with ⟨suffix, equal⟩
  unfold Cylinder.PrefixFamilyProcess.toProbePointwiseProcess
  change Interval.Refines
    (Approximation.CCL.Prefix.completedPrefixProbeBound (process.blocks newer atom.item)
      (process.witness atom.item) (process.realizes newer atom.item)
      probe factor factorPositive.le sensitive)
    (Approximation.CCL.Prefix.completedPrefixProbeBound (process.blocks older atom.item)
      (process.witness atom.item) (process.realizes older atom.item)
      probe factor factorPositive.le sensitive)
  have spreadLe :
      factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks newer atom.item) ≤
        factor * Approximation.CCL.Cylinder.cylinderSpread (process.blocks older atom.item) := by
    rw [equal]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Approximation.CCL.Cylinder.cylinderSpread_le_of_append (process.blocks older atom.item) suffix)
      factorPositive.le
  constructor
  · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct spreadLe (probe (process.witness atom.item))
  · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl spreadLe

end Purelib.Measure.CCL.Prefix.PrefixFamilyProcess

end

end

end

end

section
section
@[expose] public section

/-!
# Finite-request processes of CCL prefixes

This module packages the operational use of progressively longer finite CCL
prefixes.  A request supplies a natural-number block count and returns one
new finite state whose displayed prefixes extend the current ones and meet
that count.  There is no stream of states and no eventual CCL value.
-/

section
section

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry.Projective

namespace Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

/-- The current expectation enclosure contains every probe family realizing the current state's original blocks. -/
theorem expectation_mem_probeExpectationProcess_bound {ι :
  Type}
    (process : Cylinder.PrefixFamilyProcess ι)
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
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.expectation fun item => probe (points item)) := by
  apply (process.toProbePointwiseProcess distribution probe factor
    factorPositive sensitive).expectation_mem
  intro atom member
  exact Approximation.CCL.Prefix.completedPrefixProbeBound_contains
    (process.blocks state atom.item) (process.witness atom.item)
    (process.realizes state atom.item) probe factor factorPositive.le
    sensitive (pointsRealize atom member)

/-- The requested state's expectation enclosure is narrower than the supplied positive epsilon. -/
theorem request_probeExpectation_width_lt {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  (process.toProbeExpectationProcess distribution probe factor
    factorPositive sensitive).accurate state epsilon positive

/-- At the requested state, every realizing probe expectation is strictly within epsilon of the fixed witness
expectation. -/
theorem request_probeExpectation_separation_witness_lt {ι
  : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (points : ι → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (points atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => probe (points item))
        (distribution.expectation fun item => probe (process.witness item)) <
      epsilon := by
  let boundProcess := process.toProbeExpectationProcess distribution probe
    factor factorPositive sensitive
  let requested := boundProcess.request state epsilon positive
  apply boundProcess.request_rationalSeparation_lt state epsilon positive
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested points pointsRealize
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested process.witness
      (fun atom member => process.realizes requested atom.item)

/-- Any two probe families realizing the requested state's blocks have expectation separation strictly below epsilon. -/
theorem request_probeExpectations_pairwise_separation_lt
  {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Line.GaussianLine)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      Realizes
        (process.blocks
          ((process.toProbeExpectationProcess distribution probe factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (rightPoints atom.item)) :
    Distance.rationalSeparation
        (distribution.expectation fun item => probe (leftPoints item))
        (distribution.expectation fun item => probe (rightPoints item)) <
      epsilon := by
  let boundProcess := process.toProbeExpectationProcess distribution probe
    factor factorPositive sensitive
  let requested := boundProcess.request state epsilon positive
  apply boundProcess.request_rationalSeparation_lt state epsilon positive
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested leftPoints leftRealize
  · exact process.expectation_mem_probeExpectationProcess_bound distribution
      probe factor factorPositive sensitive requested rightPoints rightRealize

end Purelib.Data.CCL.Encoding.Cylinder.PrefixFamilyProcess

end

end

end

end

end
