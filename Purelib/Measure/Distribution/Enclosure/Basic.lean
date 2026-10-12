module
public import Purelib.Integration.Cell.WeightedEnclosure
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Integration.Cell.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
/-- Integrate the supplied interval ranges against the exact distribution's retained weighted cells.

The lower and upper endpoints are weighted expectations of the original range endpoints, preserving each occurrence's
weight. -/
def enclosedExpectation {α : Type} (distribution : Distribution α)
    (ranges : α → Data.Rat.Interval) : Data.Rat.Interval :=
  Integration.integralBound (distribution.enclosureCells ranges)

/-- The enclosed expectation's lower endpoint is the expectation of the original lower endpoints. -/
theorem enclosedExpectation_lower {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    (distribution.enclosedExpectation ranges).lower =
      distribution.expectation (fun item => (ranges item).lower) :=
  distribution.lowerIntegral_enclosureCells ranges

/-- The enclosed expectation's upper endpoint is the expectation of the original upper endpoints. -/
theorem enclosedExpectation_upper {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    (distribution.enclosedExpectation ranges).upper =
      distribution.expectation (fun item => (ranges item).upper) :=
  distribution.upperIntegral_enclosureCells ranges

/-- The enclosed expectation's width is the expectation of the original range widths. -/
theorem enclosedExpectation_width {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval) :
    (distribution.enclosedExpectation ranges).width =
      distribution.expectation (fun item => (ranges item).width) := by
  unfold enclosedExpectation
  rw [Integration.integralBound_width,
    distribution.integralOscillation_enclosureCells]

open Purelib.Data.Rat
/-- Enclosing the pointwise sum of interval ranges adds their enclosed expectations. -/
theorem enclosedExpectation_add {α : Type}
    (distribution : Distribution α) (left right : α → Data.Rat.Interval) :
    distribution.enclosedExpectation (fun item =>
        (left item).add (right item)) =
      (distribution.enclosedExpectation left).add
        (distribution.enclosedExpectation right) := by
  apply Interval.ext
  · rw [distribution.enclosedExpectation_lower]
    change distribution.expectation (fun item =>
        (left item).lower + (right item).lower) =
      (distribution.enclosedExpectation left).lower +
        (distribution.enclosedExpectation right).lower
    rw [distribution.expectation_add,
      distribution.enclosedExpectation_lower,
      distribution.enclosedExpectation_lower]
  · rw [distribution.enclosedExpectation_upper]
    change distribution.expectation (fun item =>
        (left item).upper + (right item).upper) =
      (distribution.enclosedExpectation left).upper +
        (distribution.enclosedExpectation right).upper
    rw [distribution.expectation_add,
      distribution.enclosedExpectation_upper,
      distribution.enclosedExpectation_upper]

/-- Nonnegative scaling of every range scales its enclosed expectation by the same factor. -/
theorem enclosedExpectation_scale {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) (ranges : α → Data.Rat.Interval) :
    distribution.enclosedExpectation (fun item =>
        (ranges item).scale factor nonnegative) =
      (distribution.enclosedExpectation ranges).scale
        factor nonnegative := by
  apply Interval.ext
  · rw [distribution.enclosedExpectation_lower]
    change distribution.expectation (fun item =>
        factor * (ranges item).lower) =
      factor * (distribution.enclosedExpectation ranges).lower
    rw [distribution.expectation_scale,
      distribution.enclosedExpectation_lower]
  · rw [distribution.enclosedExpectation_upper]
    change distribution.expectation (fun item =>
        factor * (ranges item).upper) =
      factor * (distribution.enclosedExpectation ranges).upper
    rw [distribution.expectation_scale,
      distribution.enclosedExpectation_upper]

/-- Adding interval ranges adds their enclosed-expectation widths. -/
theorem enclosedExpectation_add_width {α : Type}
    (distribution : Distribution α) (left right : α → Data.Rat.Interval) :
    (distribution.enclosedExpectation (fun item =>
      (left item).add (right item))).width =
        (distribution.enclosedExpectation left).width +
          (distribution.enclosedExpectation right).width := by
  rw [distribution.enclosedExpectation_add, Interval.add_width]

/-- Nonnegative scaling multiplies enclosed-expectation width by the same factor. -/
theorem enclosedExpectation_scale_width {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) (ranges : α → Data.Rat.Interval) :
    (distribution.enclosedExpectation (fun item =>
      (ranges item).scale factor nonnegative)).width =
        factor * (distribution.enclosedExpectation ranges).width := by
  rw [distribution.enclosedExpectation_scale, Interval.scale_width]

/-- An observable lying in each retained atom's range has expectation inside the retained enclosed expectation. -/
theorem expectation_mem_enclosedExpectation {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (distribution.enclosedExpectation ranges).Contains
      (distribution.expectation value) := by
  rw [Interval.Contains, distribution.enclosedExpectation_lower,
    distribution.enclosedExpectation_upper]
  exact ⟨distribution.expectation_mono
      (fun item => (ranges item).lower) value
      (fun atom member => (inside atom member).1),
    distribution.expectation_mono value
      (fun item => (ranges item).upper)
      (fun atom member => (inside atom member).2)⟩

/-- Refinement of ranges on every retained occurrence refines their enclosed expectations. -/
theorem enclosedExpectation_refines {α : Type}
    (distribution : Distribution α) (inner outer : α → Data.Rat.Interval)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Interval.Refines (inner atom.item) (outer atom.item)) :
    Interval.Refines (distribution.enclosedExpectation inner)
      (distribution.enclosedExpectation outer) := by
  constructor
  · rw [distribution.enclosedExpectation_lower,
      distribution.enclosedExpectation_lower]
    exact distribution.expectation_mono
      (fun item => (outer item).lower)
      (fun item => (inner item).lower)
      (fun atom member => (refines atom member).lower)
  · rw [distribution.enclosedExpectation_upper,
      distribution.enclosedExpectation_upper]
    exact distribution.expectation_mono
      (fun item => (inner item).upper)
      (fun item => (outer item).upper)
      (fun atom member => (refines atom member).upper)

end

open Purelib.Data.Rat in
/-- Exact singleton ranges give the singleton interval at the exact expectation. -/
theorem enclosedExpectation_exact {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.enclosedExpectation (fun item => Interval.exact (value item)) =
      Interval.exact (distribution.expectation value) := by
  apply Interval.ext
  · rw [distribution.enclosedExpectation_lower]
    rfl
  · rw [distribution.enclosedExpectation_upper]
    rfl

open Purelib
open Purelib.Data.Rat
/-- A common width ceiling on every retained range bounds enclosed-expectation width. -/
theorem enclosedExpectation_width_le_of_uniform {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (allowance : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).width ≤ allowance) :
    (distribution.enclosedExpectation ranges).width ≤ allowance := by
  rw [distribution.enclosedExpectation_width]
  calc
    distribution.expectation (fun item => (ranges item).width) ≤
        distribution.expectation (fun _ => allowance) :=
      distribution.expectation_mono _ _ bounded
    _ = allowance := distribution.expectation_constant allowance

/-- A common retained-range width ceiling below the requested tolerance gives a strictly smaller enclosed-expectation
width. -/
theorem enclosedExpectation_width_lt_of_uniform {α : Type}
    (distribution : Distribution α) (ranges : α → Data.Rat.Interval)
    (allowance epsilon : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).width ≤ allowance)
    (budget : allowance < epsilon) :
    (distribution.enclosedExpectation ranges).width < epsilon :=
  (distribution.enclosedExpectation_width_le_of_uniform
    ranges allowance bounded).trans_lt budget

end Distribution

end Purelib.Measure

end
