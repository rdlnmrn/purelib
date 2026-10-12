module
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.EssentialBound.Basic
import Purelib.Measure.Content.Lp.AlmostEverywhere
public import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
/-!
# Executable finite essential maxima

On a displayed finite atom table, every rational observable has a computed
least essential magnitude bound: recursively ignore zero-weight rows and
take the rational maximum on the rest.  Thus no supremum, infimum, or
completed line is needed.  The construction also gives an explicit uniform
absolute-continuity bound for restricted integrals.
-/

@[expose] public section

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- Compute the largest observable magnitude among the retained nonzero-weight content occurrences, with zero for an
empty selection.

The finite recursive maximum skips zero-weight atoms and retains the original content occurrence list. -/
def essentialMaximumMagnitude {α : Type} (content : Content α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  essentialMaximumMagnitudeOn value content.atoms

/-- Pointwise equal observables have the same essential maximum magnitude. -/
theorem essentialMaximumMagnitude_congr {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    content.essentialMaximumMagnitude left =
      content.essentialMaximumMagnitude right :=
  essentialMaximumMagnitudeOn_congr content.atoms left right pointwise

/-- The essential maximum magnitude is nonnegative. -/
theorem essentialMaximumMagnitude_nonnegative {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    0 ≤ content.essentialMaximumMagnitude value :=
  essentialMaximumMagnitudeOn_nonnegative value content.atoms

/-- The computed essential maximum bounds the observable at every nonzero-weight occurrence. -/
theorem essentiallyBoundedBy_essentialMaximumMagnitude {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.EssentiallyBoundedBy value
      (content.essentialMaximumMagnitude value) :=
  essentiallyBoundedByOn_essentialMaximumMagnitudeOn value content.atoms

/-- Any nonnegative essential magnitude ceiling bounds the computed essential maximum. -/
theorem essentialMaximumMagnitude_le {α : Type}
    (content : Content α) (value : α → Fraction.Rational)
    (ceiling : Fraction.Rational) (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.essentialMaximumMagnitude value ≤ ceiling :=
  essentialMaximumMagnitudeOn_le value ceiling ceilingNonnegative
    content.atoms bounded

/-- Equality at nonzero-weight occurrences preserves the essential maximum magnitude. -/
theorem essentialMaximumMagnitude_congr_almostEverywhere {α : Type}
    (content : Content α) (left right : α → Fraction.Rational)
    (equal : content.EqualAlmostEverywhere left right) :
    content.essentialMaximumMagnitude left =
      content.essentialMaximumMagnitude right := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply content.essentialMaximumMagnitude_le left
      (content.essentialMaximumMagnitude right)
      (content.essentialMaximumMagnitude_nonnegative right)
    exact content.essentiallyBoundedBy_congr_almostEverywhere equal.symm
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)
  · apply content.essentialMaximumMagnitude_le right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude_nonnegative left)
    exact content.essentiallyBoundedBy_congr_almostEverywhere equal
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)

/-- The zero observable has essential maximum magnitude zero. -/
theorem essentialMaximumMagnitude_zero {α : Type}
    (content : Content α) :
    content.essentialMaximumMagnitude (fun _ => 0) = 0 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact content.essentialMaximumMagnitude_le (fun _ => 0) 0 le_rfl
      content.essentiallyBoundedBy_zero
  · exact content.essentialMaximumMagnitude_nonnegative (fun _ => 0)

/-- A constant observable's essential maximum is bounded by its magnitude, including when all weights vanish. -/
theorem essentialMaximumMagnitude_constant_le {α : Type}
    (content : Content α) (constant : Fraction.Rational) :
    content.essentialMaximumMagnitude (fun _ => constant) ≤
      Distance.rationalSeparation constant 0 := by
  exact content.essentialMaximumMagnitude_le (fun _ => constant)
    (Distance.rationalSeparation constant 0) (Distance.rationalSeparation_nonneg _ _)
    (content.essentiallyBoundedBy_constant constant)

/-- The essential maximum vanishes exactly when the observable is zero at all nonzero-weight occurrences. -/
theorem essentialMaximumMagnitude_eq_zero_iff {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.essentialMaximumMagnitude value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  constructor
  · intro maximumZero atom member
    rcases content.essentiallyBoundedBy_essentialMaximumMagnitude value
        atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      apply (Distance.rationalSeparation_eq_zero_iff (value atom.item) 0).mp
      exact Fraction.Order.Basic.Compatibility.le_antisymm _ _
        (bound.trans_eq maximumZero) (Distance.rationalSeparation_nonneg _ _)
  · intro equal
    calc
      content.essentialMaximumMagnitude value =
          content.essentialMaximumMagnitude (fun _ => 0) :=
        content.essentialMaximumMagnitude_congr_almostEverywhere
          value (fun _ => 0) equal
      _ = 0 := content.essentialMaximumMagnitude_zero

/-- The essential maximum of a sum is at most the sum of the two essential maxima. -/
theorem essentialMaximumMagnitude_add_le {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => left item + right item) ≤
      content.essentialMaximumMagnitude left +
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact add_nonneg
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_add left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- The scaled observable's essential maximum is bounded by the factor magnitude times the original maximum. -/
theorem essentialMaximumMagnitude_scale_le {α : Type}
    (content : Content α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => factor * value item) ≤
      Distance.rationalSeparation factor 0 *
        content.essentialMaximumMagnitude value := by
  apply content.essentialMaximumMagnitude_le
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Distance.rationalSeparation_nonneg _ _)
      (content.essentialMaximumMagnitude_nonnegative value)
  · exact content.essentiallyBoundedBy_scale factor value
      (content.essentialMaximumMagnitude value)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

end

open Purelib.Data.Rat in
open Fraction.Order in
/-- Scaling an observable scales its essential maximum by the factor's rational magnitude.

The zero-factor case is direct; for a nonzero factor, inverse scaling gives the reverse bound on the same retained
content. -/
theorem essentialMaximumMagnitude_scale {α : Type}
    (content : Content α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 *
        content.essentialMaximumMagnitude value := by
  by_cases factorZero : factor = 0
  · subst factor
    calc
      content.essentialMaximumMagnitude (fun item => 0 * value item) =
          content.essentialMaximumMagnitude (fun _ => 0) :=
        content.essentialMaximumMagnitude_congr _ _ (fun item =>
          zero_mul (value item))
      _ = 0 := content.essentialMaximumMagnitude_zero
      _ = Distance.rationalSeparation 0 0 *
            content.essentialMaximumMagnitude value := by
        have zeroMagnitude : Distance.rationalSeparation (0 : Fraction.Rational) 0 = 0 :=
          Distance.rationalSeparation_zero_of_nonneg (Basic.le_refl 0)
        exact ((congrArg (fun magnitude => magnitude *
          content.essentialMaximumMagnitude value) zeroMagnitude).trans (zero_mul _)).symm
  · apply Fraction.Order.Basic.Compatibility.le_antisymm
    · exact content.essentialMaximumMagnitude_scale_le factor value
    · let scaledValue := fun item => factor * value item
      have inverseBound := content.essentialMaximumMagnitude_scale_le
        factor⁻¹ scaledValue
      have restored : content.essentialMaximumMagnitude
          (fun item => factor⁻¹ * scaledValue item) =
          content.essentialMaximumMagnitude value :=
        content.essentialMaximumMagnitude_congr _ _ (fun item => by
          dsimp only [scaledValue]
          calc
            factor⁻¹ * (factor * value item) =
                (factor⁻¹ * factor) * value item := by
              rw [mul_assoc]
            _ = value item := by
              rw [Fraction.Field.inv_mul_cancel factor factorZero,
                one_mul])
      rw [restored] at inverseBound
      have multiplied :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          inverseBound (Distance.rationalSeparation_nonneg factor 0)
      have magnitudesCancel :
          Distance.rationalSeparation factor 0 *
              Distance.rationalSeparation factor⁻¹ 0 = 1 := by
        rw [← Distance.rationalSeparation_mul_zero,
          Fraction.Field.mul_inv_cancel factor factorZero]
        decide
      calc
        Distance.rationalSeparation factor 0 *
              content.essentialMaximumMagnitude value ≤
            Distance.rationalSeparation factor 0 *
              (Distance.rationalSeparation factor⁻¹ 0 *
                content.essentialMaximumMagnitude scaledValue) := multiplied
        _ = (Distance.rationalSeparation factor 0 *
              Distance.rationalSeparation factor⁻¹ 0) *
                content.essentialMaximumMagnitude scaledValue := by
          rw [mul_assoc]
        _ = content.essentialMaximumMagnitude scaledValue := by
          rw [magnitudesCancel, one_mul]

section
open Purelib.Data.Rat
/-- Negating an observable preserves its essential maximum magnitude. -/
theorem essentialMaximumMagnitude_neg {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => -value item) =
      content.essentialMaximumMagnitude value := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · apply content.essentialMaximumMagnitude_le
    · exact content.essentialMaximumMagnitude_nonnegative value
    · exact content.essentiallyBoundedBy_neg value
        (content.essentialMaximumMagnitude value)
        (content.essentiallyBoundedBy_essentialMaximumMagnitude value)
  · apply content.essentialMaximumMagnitude_le
    · exact content.essentialMaximumMagnitude_nonnegative
        (fun item => -value item)
    · have doubleNegated := content.essentiallyBoundedBy_neg
          (fun item => -value item)
          (content.essentialMaximumMagnitude (fun item => -value item))
          (content.essentiallyBoundedBy_essentialMaximumMagnitude
            (fun item => -value item))
      intro atom member
      rcases doubleNegated atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        change Distance.rationalSeparation (value atom.item) 0 ≤
          content.essentialMaximumMagnitude (fun item => -value item)
        change Distance.rationalSeparation (- -value atom.item) 0 ≤
          content.essentialMaximumMagnitude (fun item => -value item) at bound
        rw [neg_neg] at bound
        exact bound

/-- The essential maximum of a difference is at most the sum of the two original essential maxima. -/
theorem essentialMaximumMagnitude_sub_le {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => left item - right item) ≤
      content.essentialMaximumMagnitude left +
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact add_nonneg
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_sub left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- The essential maximum of a product is at most the product of the two original essential maxima. -/
theorem essentialMaximumMagnitude_mul_le {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.essentialMaximumMagnitude (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude left *
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_mul left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-! ## Executable finite essential-maximum distance -/

/-- Take the essential maximum magnitude of the exact pointwise difference of two observables. -/
def essentialMaximumDistance {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  content.essentialMaximumMagnitude fun item => left item - right item

/-- The essential maximum distance is nonnegative. -/
theorem essentialMaximumDistance_nonnegative {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    0 ≤ content.essentialMaximumDistance left right :=
  content.essentialMaximumMagnitude_nonnegative _

/-- An observable's essential maximum distance from itself is zero. -/
theorem essentialMaximumDistance_refl {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.essentialMaximumDistance value value = 0 := by
  unfold essentialMaximumDistance
  calc
    content.essentialMaximumMagnitude (fun item => value item - value item) =
        content.essentialMaximumMagnitude (fun _ => (0 : Fraction.Rational)) :=
      content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
    _ = 0 := content.essentialMaximumMagnitude_zero

/-- Exchanging the two observables preserves essential maximum distance. -/
theorem essentialMaximumDistance_symm {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.essentialMaximumDistance left right =
      content.essentialMaximumDistance right left := by
  unfold essentialMaximumDistance
  have negated := content.essentialMaximumMagnitude_neg
    (fun item => left item - right item)
  have same : content.essentialMaximumMagnitude
      (fun item => -(left item - right item)) =
      content.essentialMaximumMagnitude
        (fun item => right item - left item) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same] at negated
  exact negated.symm

/-- Essential maximum distance obeys the triangle inequality through the same middle observable. -/
theorem essentialMaximumDistance_triangle {α : Type}
    (content : Content α)
    (left middle right : α → Fraction.Rational) :
    content.essentialMaximumDistance left right ≤
      content.essentialMaximumDistance left middle +
        content.essentialMaximumDistance middle right := by
  have bound := content.essentialMaximumMagnitude_add_le
    (fun item => left item - middle item)
    (fun item => middle item - right item)
  have same : content.essentialMaximumMagnitude (fun item =>
      (left item - middle item) + (middle item - right item)) =
      content.essentialMaximumMagnitude
        (fun item => left item - right item) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same] at bound
  exact bound

/-- The separation of two essential distances to a common anchor is bounded by the essential distance of their first
observables.

Each directed difference is bounded by the corresponding triangle inequality.
The rational maximum retains both directions and their common distance bound. -/
theorem essentialMaximumDistance_reverse_triangle {α : Type}
    (content : Content α)
    (first second anchor : α → Fraction.Rational) :
    Distance.rationalSeparation (content.essentialMaximumDistance first anchor)
        (content.essentialMaximumDistance second anchor) ≤
      content.essentialMaximumDistance first second := by
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · have translated := Fraction.Order.Arithmetic.add_le_add_right_direct
      (content.essentialMaximumDistance_triangle first second anchor)
      (-content.essentialMaximumDistance second anchor)
    have cancel : (content.essentialMaximumDistance first second +
        content.essentialMaximumDistance second anchor) +
        -content.essentialMaximumDistance second anchor =
        content.essentialMaximumDistance first second := by ring1
    rewrite [cancel] at translated
    exact translated
  · have triangle : content.essentialMaximumDistance second anchor ≤
        content.essentialMaximumDistance first second +
          content.essentialMaximumDistance first anchor := by
      calc
        content.essentialMaximumDistance second anchor ≤
            content.essentialMaximumDistance second first +
              content.essentialMaximumDistance first anchor :=
          content.essentialMaximumDistance_triangle second first anchor
        _ = content.essentialMaximumDistance first second +
              content.essentialMaximumDistance first anchor := by
          rw [content.essentialMaximumDistance_symm second first]
    have translated := Fraction.Order.Arithmetic.add_le_add_right_direct triangle
      (-content.essentialMaximumDistance first anchor)
    have cancel : (content.essentialMaximumDistance first second +
        content.essentialMaximumDistance first anchor) +
        -content.essentialMaximumDistance first anchor =
        content.essentialMaximumDistance first second := by ring1
    rewrite [cancel] at translated
    exact translated

/-- Essential maximum magnitude equals essential maximum distance from zero. -/
theorem essentialMaximumMagnitude_eq_distance_zero {α : Type}
    (content : Content α) (value : α → Fraction.Rational) :
    content.essentialMaximumMagnitude value =
      content.essentialMaximumDistance value (fun _ => 0) := by
  unfold essentialMaximumDistance
  exact content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)

/-- The separation of two essential maximum magnitudes is bounded by the essential distance of the original observables.
-/
theorem essentialMaximumMagnitude_separation_le_distance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (content.essentialMaximumMagnitude left)
        (content.essentialMaximumMagnitude right) ≤
      content.essentialMaximumDistance left right := by
  rw [content.essentialMaximumMagnitude_eq_distance_zero,
    content.essentialMaximumMagnitude_eq_distance_zero]
  exact content.essentialMaximumDistance_reverse_triangle
    left right (fun _ => 0)

/-- Essential maximum distance vanishes exactly when the observables agree at every nonzero-weight occurrence.

The zero-magnitude certificate applies to the original pointwise difference.
Scalar addition transports its zero equation to equality of the observables. -/
theorem essentialMaximumDistance_eq_zero_iff {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.essentialMaximumDistance left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  unfold essentialMaximumDistance
  constructor
  · intro zero
    have differenceZero :=
      (content.essentialMaximumMagnitude_eq_zero_iff
        (fun item => left item - right item)).mp zero
    intro atom member
    rcases differenceZero atom member with weightZero | same
    · exact Or.inl weightZero
    · apply Or.inr
      have restored : (left atom.item - right atom.item) + right atom.item =
          left atom.item := by ring1
      have translated := congrArg (fun difference => difference + right atom.item) same
      rewrite [restored, zero_add] at translated
      exact translated
  · intro equal
    apply (content.essentialMaximumMagnitude_eq_zero_iff
      (fun item => left item - right item)).mpr
    intro atom member
    rcases equal atom member with weightZero | same
    · exact Or.inl weightZero
    · apply Or.inr
      change left atom.item - right atom.item = 0
      rewrite [same]
      ring1

/-- Scaling both observables scales essential maximum distance by the magnitude of the same factor. -/
theorem essentialMaximumDistance_scale {α : Type}
    (content : Content α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
    content.essentialMaximumDistance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      Distance.rationalSeparation factor 0 *
        content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  have same : content.essentialMaximumMagnitude
      (fun item => factor * left item - factor * right item) =
      content.essentialMaximumMagnitude
        (fun item => factor * (left item - right item)) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same, content.essentialMaximumMagnitude_scale]
end

end Content

end Purelib.Measure

end
