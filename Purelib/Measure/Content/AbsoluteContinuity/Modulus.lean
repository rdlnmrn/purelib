module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Measure.Content.Density.Witness
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Measure.Content.Density.Transport
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

/-!
# Explicit finite absolute-continuity moduli

The computed essential maximum of a finite Radon--Nikodym density bounds the
target content of every event by that constant times its source content.
Consequently absolute continuity has a requested rational epsilon--delta
modulus, constructed without compactness, an infimum, or an existential
choice.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content.DensityWitness

open Purelib.Data.Rat in
open Purelib.Measure in
/-- A retained density witness bounds target event mass by the source essential maximum density times source event mass.
-/
theorem measure_le_essentialMaximumDensity_mul {α : Type}
    {source target : Content α}
    (witness : AtomicChange.Witness source target)
    (event : α → Bool) :
    target.measure event ≤
      source.essentialMaximumMagnitude witness.density *
        source.measure event := by
  calc
    target.measure event = source.integral (fun item =>
          witness.density item * Distribution.indicator event item) :=
      Content.DensityWitness.measure_eq witness event
    _ = source.integral (fun item =>
          Distribution.indicator event item * witness.density item) := by
      exact source.integral_congr _ _ (fun item => by ring1)
    _ ≤ source.integral (fun item =>
          source.essentialMaximumMagnitude witness.density *
            Distribution.indicator event item) := by
      apply source.integral_mono_off_zero
      intro atom member
      rcases source.essentiallyBoundedBy_essentialMaximumMagnitude
          witness.density atom member with zero | magnitudeBound
      · exact Or.inl zero
      · apply Or.inr
        have densityLe : witness.density atom.item ≤
            source.essentialMaximumMagnitude witness.density := by
          change Distance.rationalSeparation (witness.density atom.item) 0 ≤
            source.essentialMaximumMagnitude witness.density at magnitudeBound
          rw [Distance.rationalSeparation_zero_of_nonneg
            (witness.nonnegative atom.item)] at magnitudeBound
          exact magnitudeBound
        cases selected : event atom.item
        · simp only [Distribution.indicator, selected, zero_mul, mul_zero]
          exact le_rfl
        · simp only [Distribution.indicator, selected, one_mul, mul_one]
          exact densityLe
    _ = source.essentialMaximumMagnitude witness.density *
          source.measure event := by
      rw [source.integral_scale, source.integral_indicator]

end Content.DensityWitness

namespace Content

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a positive source-mass request for every positive target tolerance, with its strict event-mass guarantee.

The request depends on the exact original source and target contents. Its certificate quantifies over all Boolean events
measured by these same owners. -/
structure AbsoluteContinuityModulus {α : Type}
    (target source : Content α) where
  /-- The source-mass threshold requested for each positive target tolerance. -/ request : (epsilon : Fraction.Rational)
    → 0 < epsilon → Fraction.Rational
  /-- Every requested threshold is strictly positive. -/ request_positive : ∀ epsilon positive,
    0 < request epsilon positive
  /-- Source event mass below the exact request forces target event mass below the original tolerance. -/ controls : ∀
    epsilon positive event,
    source.measure event < request epsilon positive →
      target.measure event < epsilon

constructive_injectivity AbsoluteContinuityModulus

end Content

namespace Content.DensityWitness

open Purelib.Data.Rat in
open Purelib.Measure in
/-- Compute an absolute-continuity modulus from the essential maximum of the exact retained density.

Use the target tolerance itself when that maximum vanishes; otherwise divide by the positive maximum. The original
density witness supplies the strict target event bound. -/
def absoluteContinuityModulus {α : Type}
    {source target : Content α}
    (witness : AtomicChange.Witness source target) :
    Content.AbsoluteContinuityModulus target source where
  request epsilon positive :=
    if source.essentialMaximumMagnitude witness.density = 0 then epsilon
    else epsilon / source.essentialMaximumMagnitude witness.density
  request_positive epsilon positive := by
    by_cases maximumZero :
        source.essentialMaximumMagnitude witness.density = 0
    · rewrite [if_pos maximumZero]
      exact positive
    · rewrite [if_neg maximumZero]
      have maximumPositive :
          0 < source.essentialMaximumMagnitude witness.density :=
        lt_of_le_of_ne
          (source.essentialMaximumMagnitude_nonnegative witness.density)
          (Ne.symm maximumZero)
      exact Fraction.Order.Field.div_pos_direct positive maximumPositive
  controls epsilon positive event small := by
    by_cases maximumZero :
        source.essentialMaximumMagnitude witness.density = 0
    · have bound := measure_le_essentialMaximumDensity_mul witness event
      rw [maximumZero, zero_mul] at bound
      exact bound.trans_lt positive
    · have maximumPositive :
          0 < source.essentialMaximumMagnitude witness.density :=
        lt_of_le_of_ne
          (source.essentialMaximumMagnitude_nonnegative witness.density)
          (Ne.symm maximumZero)
      have sourceSmall : source.measure event <
          epsilon / source.essentialMaximumMagnitude witness.density := by
        rewrite [if_neg maximumZero] at small
        exact small
      have scaled :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          maximumPositive sourceSmall
      calc
        target.measure event ≤
            source.essentialMaximumMagnitude witness.density *
              source.measure event :=
          measure_le_essentialMaximumDensity_mul witness event
        _ < source.essentialMaximumMagnitude witness.density *
              (epsilon /
                source.essentialMaximumMagnitude witness.density) := scaled
        _ = (epsilon /
              source.essentialMaximumMagnitude witness.density) *
                source.essentialMaximumMagnitude witness.density := by ring1
        _ = epsilon :=
          Fraction.Field.div_mul_cancel_of_ne epsilon
            (source.essentialMaximumMagnitude witness.density)
            maximumZero

end Content.DensityWitness

namespace Content.AbsolutelyContinuous

open Purelib.Measure in
/-- Construct a quantitative modulus between the original finite contents from their absolute-continuity witness.

Use the density constructed on shared finite keys and transported back to these exact source and target owners. -/
def modulus {α : Type} [DecidableEq α]
    {target source : Content α}
    (continuous : target.AbsolutelyContinuous source) :
    Content.AbsoluteContinuityModulus target source :=
  (Content.DensityWitness.ofAbsolutelyContinuous source target continuous)
    |> Content.DensityWitness.absoluteContinuityModulus

end Content.AbsolutelyContinuous

end Purelib.Measure
