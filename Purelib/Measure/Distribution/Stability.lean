module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Weighted.Error
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite expectation stability

These estimates turn supplied pointwise rational error budgets into exact
finite expectation bounds.  A second form permits a larger error on one
displayed exceptional event and charges exactly its finite probability.
-/

namespace Purelib.Measure
namespace Distribution
end Distribution

namespace Content
end Content

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Expectation over the same retained distribution preserves pointwise subtraction. -/
theorem expectation_sub {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) :
    distribution.expectation (fun item => left item - right item) =
      distribution.expectation left - distribution.expectation right :=
  Measure.expectationWeight_sub distribution.atoms left right

open Purelib.Data.Rat
/-- A pointwise symmetric error allowance bounds both signed expectation differences by its expectation. -/
theorem expectation_symmetricError {α : Type}
    (distribution : Distribution α)
    (allowance left right : α → Fraction.Rational)
    (bounded : SymmetricErrorOn distribution.atoms allowance left right) :
    distribution.expectation right - distribution.expectation left ≤
        distribution.expectation allowance ∧
      distribution.expectation left - distribution.expectation right ≤
        distribution.expectation allowance := by
  constructor
  · have averaged := distribution.expectation_mono
      (fun item => right item - left item) allowance
      (fun atom member => (bounded atom member).1)
    rw [distribution.expectation_sub] at averaged
    exact averaged
  · have averaged := distribution.expectation_mono
      (fun item => left item - right item) allowance
      (fun atom member => (bounded atom member).2)
    rw [distribution.expectation_sub] at averaged
    exact averaged

/-- A uniform pointwise error allowance bounds both signed expectation differences by that same allowance. -/
theorem expectation_close_of_uniform {α : Type}
    (distribution : Distribution α) (epsilon : Fraction.Rational)
    (left right : α → Fraction.Rational)
    (bounded : SymmetricErrorOn distribution.atoms
      (fun _ => epsilon) left right) :
    distribution.expectation right - distribution.expectation left ≤ epsilon ∧
      distribution.expectation left - distribution.expectation right ≤ epsilon := by
  have averaged := distribution.expectation_symmetricError
    (fun _ => epsilon) left right bounded
  rw [distribution.expectation_constant] at averaged
  exact averaged

/-- An ordinary error bound with an extra allowance on one event gives expectation error at most ordinary plus extra
times that event's probability.

Both pointwise hypotheses refer to the same original atom list and Boolean exceptional event. No replacement
distribution or independence premise is used. -/
theorem expectation_close_outside_event {α : Type}
    (distribution : Distribution α) (exceptional : α → Bool)
    (ordinary extra : Fraction.Rational) (left right : α → Fraction.Rational)
    (outside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = false →
        right atom.item - left atom.item ≤ ordinary ∧
          left atom.item - right atom.item ≤ ordinary)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = true →
        right atom.item - left atom.item ≤ ordinary + extra ∧
          left atom.item - right atom.item ≤ ordinary + extra) :
    distribution.expectation right - distribution.expectation left ≤
        ordinary + extra * distribution.probability exceptional ∧
      distribution.expectation left - distribution.expectation right ≤
        ordinary + extra * distribution.probability exceptional := by
  let allowance : α → Fraction.Rational := fun item =>
    ordinary + extra * indicator exceptional item
  have bounded : SymmetricErrorOn distribution.atoms allowance left right := by
    intro atom member
    cases selected : exceptional atom.item
    · simpa only [allowance, indicator, selected, mul_zero, add_zero] using
        outside atom member selected
    · simpa only [allowance, indicator, selected, mul_one] using
        inside atom member selected
  have averaged := distribution.expectation_symmetricError
    allowance left right bounded
  have allowanceExpectation : distribution.expectation allowance =
      ordinary + extra * distribution.probability exceptional := by
    calc
      distribution.expectation allowance =
          distribution.expectation (fun _ => ordinary) +
            distribution.expectation
              (fun item => extra * indicator exceptional item) :=
        distribution.expectation_add _ _
      _ = ordinary + extra * distribution.probability exceptional := by
        rw [distribution.expectation_constant,
          distribution.expectation_scale,
          distribution.expectation_indicator]
  rw [allowanceExpectation] at averaged
  exact averaged

end Distribution

end Purelib.Measure

end
