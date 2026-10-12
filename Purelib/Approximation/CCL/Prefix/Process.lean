module
public import Purelib.Approximation.CCL.Prefix.Observation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Weighted.Enclosure.Process

import Purelib.Approximation.Observation.Basic
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Process
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Rational.Budget.Dyadic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

open Purelib

open Purelib.Approximation.CCL

open Purelib.Approximation.Rational

open Purelib.Data

open Purelib.Data.CCL.Encoding

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line.Basic

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

namespace Purelib.Data.CCL.Encoding.Cylinder
namespace PrefixFamilyProcess

/-- Turn finite CCL prefix requests into pointwise rational probe-enclosure requests on one fixed finite probability
table. -/
def toProbePointwiseProcess {ι : Type}
    (process : Cylinder.PrefixFamilyProcess ι)
    (distribution : Measure.Distribution ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Measure.PointwiseEnclosureProcess distribution where
  State := process.State
  ranges state item := Prefix.completedPrefixProbeBound
    (process.blocks state item) (process.witness item)
    (process.realizes state item) probe factor factorPositive.le sensitive
  initial := process.initial
  request state epsilon positive :=
    process.request state (Budget.requiredProbeBlockCount epsilon factor)
  request_refines state epsilon positive atom member := by
    rcases process.request_extends state
      (Budget.requiredProbeBlockCount epsilon factor) atom.item with
      ⟨suffix, equal⟩
    have spreadLe :
        Cylinder.cylinderSpread
            (process.blocks
              (process.request state
                (Budget.requiredProbeBlockCount epsilon factor)) atom.item) ≤
          Cylinder.cylinderSpread (process.blocks state atom.item) := by
      rw [equal]
      exact Cylinder.cylinderSpread_le_of_append
        (process.blocks state atom.item) suffix
    have scaledLe :
        factor * Cylinder.cylinderSpread
            (process.blocks
              (process.request state
                (Budget.requiredProbeBlockCount epsilon factor)) atom.item) ≤
          factor * Cylinder.cylinderSpread (process.blocks state atom.item) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledLe
  accurate state epsilon positive atom member := by
    exact (Prefix.completedPrefixProbeBound_width_lt_requested
      (process.witness atom.item)
      (process.realizes
        (process.request state (Budget.requiredProbeBlockCount epsilon factor))
        atom.item)
      probe factor factorPositive sensitive epsilon positive
      (process.request_length state
        (Budget.requiredProbeBlockCount epsilon factor) atom.item)).le
  refinesInitial state atom member := by
    rcases process.extendsInitial state atom.item with ⟨suffix, equal⟩
    have spreadLe : Cylinder.cylinderSpread (process.blocks state atom.item) ≤
        Cylinder.cylinderSpread (process.blocks process.initial atom.item) := by
      rw [equal]
      exact Cylinder.cylinderSpread_le_of_append
        (process.blocks process.initial atom.item) suffix
    have scaledLe : factor * Cylinder.cylinderSpread (process.blocks state atom.item) ≤
        factor * Cylinder.cylinderSpread (process.blocks process.initial atom.item) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        spreadLe factorPositive.le
    constructor
    · exact Fraction.Order.Arithmetic.sub_le_sub_left_direct scaledLe (probe (process.witness atom.item))
    · exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl scaledLe
end PrefixFamilyProcess

end Purelib.Data.CCL.Encoding.Cylinder

end

end

section
@[expose] public section

/-!
# Progressive threshold probabilities from finite CCL prefixes

A lower-threshold event can be decided after one finite prefix request when
each displayed witness probe has an explicit positive rational margin from
the threshold.  The requested completed-block count makes every current
probe enclosure narrower than that margin, so every finite row is classified
and the resulting probability enclosure has width zero.  No eventual CCL
point or infinite refinement sequence is introduced.
-/

namespace Purelib.Approximation.CCL.Prefix
namespace PrefixFamilyProcess

/-- Current rational enclosure of a probe on one process-controlled CCL prefix row. -/
def probeRange {ι : Type} (process :
  Cylinder.PrefixFamilyProcess ι)
    (probe : Line.GaussianLine → Fraction.Rational) (factor : Fraction.Rational)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (state : process.State) (item : ι) : Rat.Interval :=
  Prefix.completedPrefixProbeBound (process.blocks state item)
    (process.witness item) (process.realizes state item)
    probe factor factorNonnegative sensitive
end PrefixFamilyProcess

end Purelib.Approximation.CCL.Prefix

end
