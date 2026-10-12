module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Weighted.AlmostEverywhere
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Event.NatOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Basic

section
@[expose] public section

/-!
# Finite layer-cake identities

For a natural-valued observable, truncation at a displayed finite height is
the sum of its Boolean upper-level indicators.  Integrating this pointwise
identity gives an exact finite tail-sum, or layer-cake, formula.  There is no
infinite series and no improper integral.
-/

namespace Purelib.Measure
namespace Content

open Purelib.Data.Rat in
/-- Sum the masses of the strict natural-level events below the supplied finite height.

The recursive successor step adds the event where the original natural-valued observable exceeds the previous height. -/
def natTailMeasureSum {α : Type} (content : Content α)
    (value : α → Nat) : Nat → Fraction.Rational
  | 0 => 0
  | height + 1 =>
      natTailMeasureSum content value height +
        content.measure (natAboveEvent height value)

open Purelib in
open Purelib.Data.Rat in
/-- Integrating the observable truncated at a natural height equals the finite sum of its strict tail-event masses below
that height. -/
theorem integral_truncatedNat_eq_natTailMeasureSum {α : Type}
    (content : Content α) (value : α → Nat) :
    ∀ height : Nat,
      content.integral (fun item =>
          ((min (value item) height : Nat) : Fraction.Rational)) =
        content.natTailMeasureSum value height
  | 0 => by
      rw [natTailMeasureSum]
      calc
        content.integral (fun item =>
              ((min (value item) 0 : Nat) : Fraction.Rational)) =
            content.integral (fun _ => (0 : Fraction.Rational)) :=
          content.integral_congr _ _ (fun item => by
            cases value item <;> rfl)
        _ = content.total * 0 := content.integral_constant 0
        _ = 0 := mul_zero content.total
  | height + 1 => by
      rw [natTailMeasureSum]
      calc
        content.integral (fun item =>
              ((min (value item) (height + 1) : Nat) : Fraction.Rational)) =
            content.integral (fun item =>
              ((min (value item) height : Nat) : Fraction.Rational) +
                Distribution.indicator
                  (natAboveEvent height value) item) :=
          content.integral_congr _ _ (fun item =>
            Measure.cast_min_succ_eq_cast_min_add_indicator value height item)
        _ = content.integral (fun item =>
              ((min (value item) height : Nat) : Fraction.Rational)) +
              content.integral
                (Distribution.indicator (natAboveEvent height value)) :=
          content.integral_add _ _
        _ = content.natTailMeasureSum value height +
              content.measure (natAboveEvent height value) :=
          congrArg₂ (fun left right => left + right)
            (integral_truncatedNat_eq_natTailMeasureSum
              content value height)
            (content.integral_indicator (natAboveEvent height value))

open Purelib.Data.Rat in
/-- A natural observable bounded by the supplied height on retained atoms integrates as the finite strict-tail mass sum
up to that height. -/
theorem integral_nat_eq_natTailMeasureSum_of_bounded {α : Type}
    (content : Content α) (value : α → Nat) (height : Nat)
    (bounded : ∀ atom, atom ∈ content.atoms → value atom.item ≤ height) :
    content.integral (fun item => (value item : Fraction.Rational)) =
      content.natTailMeasureSum value height := by
  calc
    content.integral (fun item => (value item : Fraction.Rational)) =
        content.integral (fun item =>
          ((min (value item) height : Nat) : Fraction.Rational)) := by
      apply expectationWeight_congr_off_zero content.atoms
      intro atom member
      apply Or.inr
      change (value atom.item : Fraction.Rational) =
        ((min (value atom.item) height : Nat) : Fraction.Rational)
      rw [Nat.min_eq_left (bounded atom member)]
    _ = content.natTailMeasureSum value height :=
      content.integral_truncatedNat_eq_natTailMeasureSum value height

end Content

end Purelib.Measure

end
