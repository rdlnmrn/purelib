module
public import Purelib.Measure.Content.Lp.AlmostEverywhere
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
public import Purelib.Measure.Weighted.EssentialBound
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Bound the rational magnitude at each retained content occurrence unless its weight is zero. -/
def EssentiallyBoundedBy {α : Type} (content : Content α)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) : Prop :=
  EssentiallyBoundedByOn content.atoms value ceiling

/-- Pointwise order at nonzero-weight occurrences gives order between integrals over the same content. -/
theorem integral_mono_off_zero {α : Type} (content : Content α)
    (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ content.atoms →
      atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) :
    content.integral lower ≤ content.integral upper :=
  expectationWeight_mono_off_zero lower upper content.atoms pointwise

/-- Equality at nonzero-weight occurrences preserves every essential magnitude ceiling. -/
theorem essentiallyBoundedBy_congr_almostEverywhere {α : Type}
    (content : Content α) {left right : α → Fraction.Rational}
    {ceiling : Fraction.Rational}
    (equal : content.EqualAlmostEverywhere left right)
    (bounded : content.EssentiallyBoundedBy left ceiling) :
    content.EssentiallyBoundedBy right ceiling := by
  intro atom member
  rcases equal atom member with zero | same
  · exact Or.inl zero
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation (right atom.item) 0 ≤ ceiling
    change Distance.rationalSeparation (left atom.item) 0 ≤ ceiling at bound
    rw [← same]
    exact bound

end

open Purelib.Data.Rat in
open Fraction.Order in
/-- The zero observable is essentially bounded by zero.

Its separation from zero is zero at every original occurrence, including
nonzero-weight rows. This scalar bound retains the same content and weights. -/
theorem essentiallyBoundedBy_zero {α : Type}
    (content : Content α) :
    content.EssentiallyBoundedBy (fun _ => 0) 0 := by
  intro atom member
  apply Or.inr
  change Distance.rationalSeparation (0 : Fraction.Rational) 0 ≤ 0
  calc
    Distance.rationalSeparation (0 : Fraction.Rational) 0 = 0 :=
      Distance.rationalSeparation_zero_of_nonneg (Basic.le_refl 0)
    _ ≤ 0 := Basic.le_refl 0

open Purelib.Data.Rat
/-- A constant observable is essentially bounded by its rational magnitude. -/
theorem essentiallyBoundedBy_constant {α : Type}
    (content : Content α) (constant : Fraction.Rational) :
    content.EssentiallyBoundedBy (fun _ => constant)
      (Distance.rationalSeparation constant 0) := by
  intro atom member
  exact Or.inr le_rfl

/-- The sum of two essential magnitude ceilings bounds the sum observable. -/
theorem essentiallyBoundedBy_add {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (leftCeiling rightCeiling : Fraction.Rational)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item + right item)
      (leftCeiling + rightCeiling) := by
  intro atom member
  rcases leftBound atom member with zero | leftLe
  · exact Or.inl zero
  rcases rightBound atom member with zero | rightLe
  · exact Or.inl zero
  · apply Or.inr
    exact (Distance.rationalSeparation_add_zero_le
      (left atom.item) (right atom.item)).trans
        (add_le_add leftLe rightLe)

/-- Scaling an observable scales its essential magnitude ceiling by the factor's magnitude. -/
theorem essentiallyBoundedBy_scale {α : Type}
    (content : Content α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.EssentiallyBoundedBy (fun item => factor * value item)
      (Distance.rationalSeparation factor 0 * ceiling) := by
  intro atom member
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation (factor * value atom.item) 0 ≤
      Distance.rationalSeparation factor 0 * ceiling
    change Distance.rationalSeparation (value atom.item) 0 ≤ ceiling at bound
    rw [Distance.rationalSeparation_mul_zero]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      bound (Distance.rationalSeparation_nonneg _ _)

/-- Negating an observable preserves its essential magnitude ceiling. -/
theorem essentiallyBoundedBy_neg {α : Type}
    (content : Content α) (value : α → Fraction.Rational)
    (ceiling : Fraction.Rational)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.EssentiallyBoundedBy (fun item => -value item) ceiling := by
  intro atom member
  rcases bounded atom member with zero | bound
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation (-value atom.item) 0 ≤ ceiling
    have magnitudeEqual :
        Distance.rationalSeparation (-value atom.item) 0 =
          Distance.rationalSeparation (value atom.item) 0 := by
      simpa only [neg_zero] using
        Distance.rationalSeparation_neg (value atom.item) 0
    rw [magnitudeEqual]
    exact bound

/-- The sum of two essential magnitude ceilings bounds the difference observable. -/
theorem essentiallyBoundedBy_sub {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (leftCeiling rightCeiling : Fraction.Rational)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item - right item)
      (leftCeiling + rightCeiling) := by
  change content.EssentiallyBoundedBy
    (fun item => left item + -right item) (leftCeiling + rightCeiling)
  exact content.essentiallyBoundedBy_add left (fun item => -right item)
    leftCeiling rightCeiling leftBound
    (content.essentiallyBoundedBy_neg right rightCeiling rightBound)

/-- The product of two essential magnitude ceilings bounds the product observable. -/
theorem essentiallyBoundedBy_mul {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (leftCeiling rightCeiling : Fraction.Rational)
    (leftBound : content.EssentiallyBoundedBy left leftCeiling)
    (rightBound : content.EssentiallyBoundedBy right rightCeiling) :
    content.EssentiallyBoundedBy (fun item => left item * right item)
      (leftCeiling * rightCeiling) := by
  intro atom member
  rcases leftBound atom member with zero | leftLe
  · exact Or.inl zero
  rcases rightBound atom member with zero | rightLe
  · exact Or.inl zero
  · apply Or.inr
    change Distance.rationalSeparation (left atom.item * right atom.item) 0 ≤
      leftCeiling * rightCeiling
    rw [Distance.rationalSeparation_mul_zero]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      leftLe rightLe (Distance.rationalSeparation_nonneg _ _)
        ((Distance.rationalSeparation_nonneg _ _).trans leftLe)
end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
