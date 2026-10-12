module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Content.EssentialBound.Lp
import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.AlmostEverywhere
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Content.Lp.Natural
import Purelib.Data.Rat.Fraction

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Content.AlmostEverywhere.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Measure
open Purelib.Examples

/-- The Boolean content assigning mass zero to false and mass one to true. -/
def zeroMassContent : Content Bool where
  atoms :=
    [⟨false, 0, by decide⟩,
      ⟨true, 1, by decide⟩]

/-- The displayed observable equal to three at true and seven at the zero-mass false atom. -/
def zeroMassLeft (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 3 else 7

/-- The displayed observable equal to three at true and nine at the zero-mass false atom. -/
def zeroMassRight (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 3 else 9

/-- The two displayed observables agree on every positive-mass atom. -/
theorem
  zeroMassObservables_equalAlmostEverywhere
  :
    zeroMassContent.EqualAlmostEverywhere
      zeroMassLeft
      zeroMassRight := by
  intro atom member
  simp only [zeroMassContent, -eq_self, -iff_self] at member
  rcases Membership.mem_cons.mp member with rfl | member
  · exact Or.inl rfl
  · have same := Membership.mem_singleton.mp member
    cases same
    right
    change (3 : Fraction.Rational) = 3
    rfl

/-- The second observable is essentially bounded in magnitude by three. -/
theorem zeroMassRight_essentiallyBounded :
    zeroMassContent.EssentiallyBoundedBy
      zeroMassRight 3 := by
  intro atom member
  simp only [zeroMassContent, -eq_self, -iff_self] at member
  rcases Membership.mem_cons.mp member with rfl | member
  · exact Or.inl rfl
  · have same := Membership.mem_singleton.mp member
    cases same
    exact Or.inr (by decide)

/-- The first observable has essential maximum magnitude three. -/
example : zeroMassContent.essentialMaximumMagnitude
  zeroMassLeft = 3 := by
  decide

/-- The second observable has essential maximum magnitude three. -/
example : zeroMassContent.essentialMaximumMagnitude
  zeroMassRight = 3 := by
  decide

/-- Almost-everywhere equality preserves the displayed essential maximum. -/
example : zeroMassContent.essentialMaximumMagnitude
  zeroMassLeft =
    zeroMassContent.essentialMaximumMagnitude
      zeroMassRight :=
  zeroMassContent.essentialMaximumMagnitude_congr_almostEverywhere
    zeroMassLeft
      zeroMassRight
      zeroMassObservables_equalAlmostEverywhere

/-- The displayed almost-everywhere equal observables have zero L1 distance. -/
example : zeroMassContent.l1Distance
  zeroMassLeft
  zeroMassRight = 0 :=
  zeroMassContent.l1Distance_eq_zero_of_equalAlmostEverywhere
    zeroMassLeft
      zeroMassRight
      zeroMassObservables_equalAlmostEverywhere

/-- The displayed almost-everywhere equal observables have equal powered L4 values. -/
example : zeroMassContent.poweredLp 4
  zeroMassLeft =
    zeroMassContent.poweredLp 4
      zeroMassRight :=
  zeroMassContent.poweredLp_congr_almostEverywhere 4
    zeroMassLeft
      zeroMassRight
      zeroMassObservables_equalAlmostEverywhere

/-- The displayed observables have zero cubed Lp distance. -/
example : zeroMassContent.poweredLpDistance 3
      zeroMassLeft
        zeroMassRight = 0 :=
  (zeroMassContent.poweredLpDistance_eq_zero_iff 2
    zeroMassLeft
      zeroMassRight).mpr
      zeroMassObservables_equalAlmostEverywhere

/-- Zero squared L2 distance is equivalent to almost-everywhere equality for the displayed pair. -/
example : zeroMassContent.poweredL2Distance
      zeroMassLeft
        zeroMassRight = 0 ↔
    zeroMassContent.EqualAlmostEverywhere
      zeroMassLeft
      zeroMassRight :=
  zeroMassContent.poweredL2Distance_eq_zero_iff
    zeroMassLeft
      zeroMassRight

/-- The displayed almost-everywhere equal observables have equal finite integrals. -/
example : zeroMassContent.integral
  zeroMassLeft =
    zeroMassContent.integral
      zeroMassRight :=
  zeroMassContent.integral_congr_almostEverywhere
    zeroMassLeft
      zeroMassRight
      zeroMassObservables_equalAlmostEverywhere

/-- The retained essential bound three bounds the squared L2 value by total mass times nine. -/
example : zeroMassContent.poweredLp 2
  zeroMassRight ≤
    zeroMassContent.total * 3 ^ 2 :=
  zeroMassContent.poweredLp_le_of_essentialBound 2
    zeroMassRight 3
    zeroMassRight_essentiallyBounded

end Purelib.Examples.Measure.Content.AlmostEverywhere.Coin.WorkedExamples

end
