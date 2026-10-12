module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
public import Purelib.Measure.Weighted.IntegralTransform

section
@[expose] public section

/-!
# Finite rational Radon--Nikodym witnesses

For two atom tables presented on the same explicit rows, absolute continuity
is the rowwise condition that a zero source weight forces a zero target
weight.  When row payloads do not repeat, the target/source quotient is an
executable rational density and reconstructs every target integral exactly.

There is no almost-everywhere quotient or existence argument over an
unbounded carrier.  The witness is calculated from the displayed finite
table.
-/

section
section

namespace Purelib.Measure.AtomicChange

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a nonnegative rational density transporting all integrals between the same source and target contents.

The witness keeps both original content owners. Every target observable integrates as the source observable multiplied
pointwise by this exact retained density. -/
structure Witness {α : Type} (source target : Content α) where
  /-- The exact rational density retained between these source and target contents. -/ density : α → Fraction.Rational
  /-- The retained density is nonnegative at every payload. -/ nonnegative : ∀ item, 0 ≤ density item
  /-- Every target integral equals the source integral multiplied pointwise by the same retained density. -/ integral_eq
    : ∀ value : α → Fraction.Rational,
    target.integral value =
      source.integral (fun item => density item * value item)

constructive_injectivity Witness

end Purelib.Measure.AtomicChange

namespace Purelib.Measure.Content.DensityWitness

/-- A retained density witness transports event measurement to the source integral of density times its indicator. -/
theorem measure_eq {α : Type}
    {source target : Content α}
    (witness : Purelib.Measure.AtomicChange.Witness source target) (event : α → Bool) :
    target.measure event =
      source.integral (fun item =>
        witness.density item * Distribution.indicator event item) := by
  rw [← target.integral_indicator event]
  exact witness.integral_eq (Distribution.indicator event)

/-- A retained density witness makes target total equal to the source integral of its exact density. -/
theorem total_eq {α : Type}
    {source target : Content α}
    (witness : Purelib.Measure.AtomicChange.Witness source target) :
    target.total = source.integral witness.density := by
  calc
    target.total = target.integral (fun _ => 1) := by
      rw [target.integral_constant, mul_one]
    _ = source.integral (fun item => witness.density item * 1) :=
      witness.integral_eq (fun _ => 1)
    _ = source.integral witness.density :=
      source.integral_congr _ _ (fun item => by ring1)

end Purelib.Measure.Content.DensityWitness

open Purelib.Data.Rat

namespace Purelib.Measure.AtomicChange

/-- Density times a singleton indicator integrates to that singleton's content mass times the density at its payload. -/
private theorem integral_density_indicator_atomEvent
    {α : Type} [DecidableEq α] (content : Content α)
    (density : α → Fraction.Rational) (item : α) :
    content.integral (fun candidate =>
        density candidate * Distribution.indicator (atomEvent item) candidate) =
      content.measure (atomEvent item) * density item := by
  calc
    content.integral (fun candidate =>
          density candidate *
            Distribution.indicator (atomEvent item) candidate) =
        content.integral (fun candidate =>
          density item *
            Distribution.indicator (atomEvent item) candidate) :=
      content.integral_congr _ _ (fun candidate => by
        cases selected : atomEvent item candidate
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected, mul_zero]
          rfl
        · have same : candidate = item := by
            unfold atomEvent at selected
            exact of_decide_eq_true selected
          rw [same])
    _ = content.measure (atomEvent item) * density item := by
      rw [content.integral_scale, content.integral_indicator]
      ring1

end Purelib.Measure.AtomicChange

namespace Purelib.Measure.Content.DensityWitness

/-- Two density witnesses between the same contents agree at every payload with positive source singleton mass. -/
theorem density_eq_of_positive_atom
    {α : Type} [DecidableEq α]
    {source target : Content α}
    (first second : Purelib.Measure.AtomicChange.Witness source target) (item : α)
    (positive : 0 < source.measure (atomEvent item)) :
    first.density item = second.density item := by
  apply Fraction.Field.mul_right_cancel_of_ne positive.ne'
  calc
    first.density item * source.measure (atomEvent item) =
        source.measure (atomEvent item) * first.density item := by
      ring1
    _ = source.integral (fun candidate =>
          first.density candidate *
            Distribution.indicator (atomEvent item) candidate) :=
      (Purelib.Measure.AtomicChange.integral_density_indicator_atomEvent source first.density item).symm
    _ = target.integral (Distribution.indicator (atomEvent item)) :=
      (first.integral_eq (Distribution.indicator (atomEvent item))).symm
    _ = source.integral (fun candidate =>
          second.density candidate *
            Distribution.indicator (atomEvent item) candidate) :=
      second.integral_eq (Distribution.indicator (atomEvent item))
    _ = source.measure (atomEvent item) * second.density item :=
      Purelib.Measure.AtomicChange.integral_density_indicator_atomEvent source second.density item
    _ = second.density item * source.measure (atomEvent item) := by
      ring1

end Purelib.Measure.Content.DensityWitness

end

end

end
